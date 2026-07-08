defmodule ExArgus.ExplainTest do
  use ExUnit.Case, async: true

  alias ExArgus.{Explain, Offline}
  alias ExArgus.Kernel.Background

  @bg %Background{
    tools: %{
      "send_email" => %{
        capabilities: [:network_egress],
        egress: [:network_external],
        conf_floor: :public,
        output_bounded: false,
        issuer: "trusted",
        integ_floor: :untrusted,
        integ_inspect_floor: :untrusted,
        output_integ: :attested
      }
    },
    allow_ceiling: %{network_external: :public},
    inspect_ceiling: %{},
    trusted_issuers: ["trusted"],
    instruction_issuer: %{}
  }

  defp tainted_state do
    state = Offline.initial_state()
    {:ok, state, _} = Offline.register_tool(state, @bg, "send_email")
    {:ok, state, _} = Offline.delegate(state, @bg, "root", "a1")
    {:ok, state, _} = Offline.grant_capability(state, @bg, "root", "a1", :network_egress)
    {:ok, state, _} = Offline.sentinel_elevate_taint(state, @bg, "a1", :sensitive, %{})
    state
  end

  test "explain_invoke reports the denial the kernel would return" do
    state = tainted_state()

    assert {:error, :flow_gate_blocked} =
             Offline.invoke_start(state, @bg, "a1", "send_email", "i1", true, %{}, [
               :network_external
             ])

    report =
      Explain.explain_invoke(state, @bg, "a1", "send_email", "i1", true, %{}, [
        :network_external
      ])

    assert report.verdict == :flow_gate_blocked
    assert Explain.denied?(report)

    denied = Enum.filter(report.findings, &(&1.outcome == :denied))
    assert [finding | _] = denied
    assert finding.check == :spec_taint_vs_new_egress
    assert finding.level == :sensitive
    assert {:override_grant, "a1", "send_email", :sensitive} in finding.rescues
    assert {:ceiling_raise, :network_external, :sensitive} in finding.rescues
  end

  test "explain_invoke agrees on success" do
    state = Offline.initial_state()
    {:ok, state, _} = Offline.register_tool(state, @bg, "send_email")
    {:ok, state, _} = Offline.delegate(state, @bg, "root", "a1")
    {:ok, state, _} = Offline.grant_capability(state, @bg, "root", "a1", :network_egress)

    assert {:ok, _, _} =
             Offline.invoke_start(state, @bg, "a1", "send_email", "i1", true, %{}, [
               :network_external
             ])

    report =
      Explain.explain_invoke(state, @bg, "a1", "send_email", "i1", true, %{}, [
        :network_external
      ])

    assert report.verdict == nil
    refute Explain.denied?(report)
  end

  test "explain_return_unendorsed and explain_sentinel_elevate_taint cross the NIF" do
    state = tainted_state()
    report = Explain.explain_return_unendorsed(state, @bg, "a1", "root", %{})
    assert is_map(report)
    report = Explain.explain_sentinel_elevate_taint(state, @bg, "a1", :restricted, %{})
    assert report.verdict == nil
  end

  defp lever_bg do
    %Background{
      tools: %{},
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{},
      lever_integ_floor: :trusted,
      lever_integ_inspect_floor: :trusted
    }
  end

  test "explain_return_endorsed agrees on a below-lever-floor denial" do
    bg = lever_bg()
    state = Offline.initial_state()
    {:ok, state, _} = Offline.delegate(state, bg, "root", "c")
    {:ok, state, _} = Offline.grant_capability(state, bg, "root", "c", :declassify)
    {:ok, state, _} = Offline.sentinel_degrade_integrity(state, bg, "c", :untrusted, %{})

    assert {:error, :lever_integrity_denied} =
             Offline.return_endorsed(state, bg, "c", "root", true, :public, :attested)

    report = Explain.explain_return_endorsed(state, bg, "c", "root", true, :public, :attested)

    assert report.verdict == :lever_integrity_denied
    assert [finding | _] = Enum.filter(report.lever_findings, &(&1.outcome == :denied))
    assert finding.check == :child_integ_vs_lever_floor
    assert {:raise_integrity, "c"} in finding.rescues
    assert {:lever_floor_relabel, :trusted} in finding.rescues
  end

  test "explain_return_endorsed agrees on success" do
    bg = lever_bg()
    state = Offline.initial_state()
    {:ok, state, _} = Offline.delegate(state, bg, "root", "c")
    {:ok, state, _} = Offline.grant_capability(state, bg, "root", "c", :declassify)

    assert {:ok, _, _} =
             Offline.return_endorsed(state, bg, "c", "root", true, :public, :attested)

    report = Explain.explain_return_endorsed(state, bg, "c", "root", true, :public, :attested)
    assert report.verdict == nil
    refute Explain.denied?(report)
  end

  test "explain_grant_override agrees on a degraded-granter denial" do
    bg = lever_bg()
    state = Offline.initial_state()
    {:ok, state, _} = Offline.delegate(state, bg, "root", "target")
    {:ok, state, _} = Offline.sentinel_degrade_integrity(state, bg, "root", :untrusted, %{})

    assert {:error, :lever_integrity_denied} =
             Offline.grant_override(state, bg, "root", "target", "some_tool", :sensitive)

    report = Explain.explain_grant_override(state, bg, "root", "target", :sensitive)

    assert report.verdict == :lever_integrity_denied
    assert [finding | _] = Enum.filter(report.lever_findings, &(&1.outcome == :denied))
    assert finding.check == :granter_integ_vs_lever_floor
    assert finding.floor == finding.inspect_floor
    assert {:raise_integrity, "root"} in finding.rescues
  end

  test "explain_grant_override agrees on success" do
    bg = lever_bg()
    state = Offline.initial_state()
    {:ok, state, _} = Offline.delegate(state, bg, "root", "target")

    assert {:ok, _, _} =
             Offline.grant_override(state, bg, "root", "target", "some_tool", :sensitive)

    report = Explain.explain_grant_override(state, bg, "root", "target", :sensitive)
    assert report.verdict == nil
    refute Explain.denied?(report)
  end

  defp integ_bg do
    %Background{
      tools: %{
        "delete_repo" => %{
          capabilities: [],
          egress: [],
          conf_floor: :public,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :trusted,
          integ_inspect_floor: :trusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "explain_sentinel_degrade_integrity agrees on a blocked in-flight-floor denial" do
    bg = integ_bg()
    state = Offline.initial_state()
    {:ok, state, _} = Offline.register_tool(state, bg, "delete_repo")
    {:ok, state, _} = Offline.delegate(state, bg, "root", "a1")

    {:ok, state, _} =
      Offline.invoke_start(state, bg, "a1", "delete_repo", "inv-1", true, %{"inv-1" => true}, [])

    assert {:error, :integrity_floor_denied} =
             Offline.sentinel_degrade_integrity(state, bg, "a1", :untrusted, %{})

    report = Explain.explain_sentinel_degrade_integrity(state, bg, "a1", :untrusted, %{})

    assert report.verdict == :integrity_floor_denied
    assert [finding | _] = Enum.filter(report.integ_findings, &(&1.outcome == :denied))
    assert finding.check == :degrade_vs_in_flight_floor
    assert finding.tool == "delete_repo"
  end

  test "explain_sentinel_degrade_integrity agrees on success" do
    bg = integ_bg()
    state = Offline.initial_state()
    {:ok, state, _} = Offline.delegate(state, bg, "root", "a1")

    assert {:ok, _, _} = Offline.sentinel_degrade_integrity(state, bg, "a1", :untrusted, %{})

    report = Explain.explain_sentinel_degrade_integrity(state, bg, "a1", :untrusted, %{})
    assert report.verdict == nil
    refute Explain.denied?(report)
  end
end
