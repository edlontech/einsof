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
end
