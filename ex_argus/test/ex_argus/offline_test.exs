defmodule ExArgus.OfflineTest do
  use ExUnit.Case, async: true

  alias ExArgus.Offline
  alias ExArgus.Kernel.{Background, State}

  defp bg do
    %Background{
      tools: %{
        "read_file" => %{
          capabilities: [],
          egress: [],
          conf_floor: :public,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  # A non-vacuous integrity floor, to exercise the deny path of sentinel_degrade_integrity.
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

  test "content_gate_targets for invoke_start includes the new invocation plus in-flight invocations" do
    s = %State{
      in_flight: %{"a1" => ["inv-0"]},
      invocation_tool: %{"inv-0" => "old_tool"}
    }

    assert {"a1", ["inv-1", "inv-0"]} =
             Offline.content_gate_targets(s, {:invoke_start, "a1", "new_tool", "inv-1"})
  end

  test "content_gate_targets for return_unendorsed uses the parent's in-flight invocations" do
    s = %State{
      in_flight: %{"parent" => ["inv-p"]},
      invocation_tool: %{"inv-p" => "p_tool"}
    }

    assert {"parent", ["inv-p"]} =
             Offline.content_gate_targets(s, {:return_unendorsed, "child", "parent"})
  end

  test "content_gate_targets for sentinel_degrade_integrity uses the agent's in-flight invocations" do
    s = %State{
      in_flight: %{"a1" => ["inv-0"]},
      invocation_tool: %{"inv-0" => "old_tool"}
    }

    assert {"a1", ["inv-0"]} =
             Offline.content_gate_targets(s, {:sentinel_degrade_integrity, "a1", :standard})
  end

  test "content_gate_map evaluates the function over the targets" do
    s = %State{in_flight: %{"a1" => []}, invocation_tool: %{}}

    map =
      Offline.content_gate_map(s, {:invoke_start, "a1", "t", "i"}, fn _agent, _inv -> true end)

    assert map == %{"i" => true}
  end

  test "initial_state delegates to the NIF" do
    assert "root" in Offline.initial_state().agent_active
  end

  test "unregister_tool removes a registered, idle tool" do
    bg = bg()
    s = Offline.initial_state()
    {:ok, s, _} = Offline.register_tool(s, bg, "read_file")

    assert {:ok, s, {:unregister_tool, "read_file"}} = Offline.unregister_tool(s, bg, "read_file")
    refute "read_file" in s.tool_registered
  end

  test "unregister_tool is denied with :tool_in_flight while the tool has an in-flight invocation" do
    bg = bg()
    s = Offline.initial_state()
    {:ok, s, _} = Offline.register_tool(s, bg, "read_file")
    {:ok, s, _} = Offline.delegate(s, bg, "root", "a1")

    {:ok, s, _} =
      Offline.invoke_start(s, bg, "a1", "read_file", "inv-1", true, %{"inv-1" => true}, [])

    assert {:error, :tool_in_flight} = Offline.unregister_tool(s, bg, "read_file")
  end

  test "sentinel_degrade_integrity degrades an idle agent's held integrity" do
    bg = bg()
    s = Offline.initial_state()
    {:ok, s, _} = Offline.delegate(s, bg, "root", "a1")

    assert {:ok, s, {:sentinel_degrade_integrity, "a1", :standard}} =
             Offline.sentinel_degrade_integrity(s, bg, "a1", :standard, %{})

    assert :standard in Map.fetch!(s.integ_levels, "a1")
  end

  test "invoke_start/7 threads an {authorized?, attested} tuple from attest/4" do
    bg = bg()
    s = Offline.initial_state()
    {:ok, s, _} = Offline.register_tool(s, bg, "read_file")
    {:ok, s, _} = Offline.delegate(s, bg, "root", "a1")

    assert {:ok, s, {:invoke_start, "a1", "read_file", "inv-1"}} =
             Offline.invoke_start(s, bg, "a1", "read_file", "inv-1", {true, []}, %{
               "inv-1" => true
             })

    assert "inv-1" in Map.fetch!(s.in_flight, "a1")
  end

  test "invoke_start/7 propagates a denied authorized? through the underlying call" do
    bg = bg()
    s = Offline.initial_state()
    {:ok, s, _} = Offline.register_tool(s, bg, "read_file")
    {:ok, s, _} = Offline.delegate(s, bg, "root", "a1")

    assert {:error, :authorizer_denied} =
             Offline.invoke_start(s, bg, "a1", "read_file", "inv-1", {false, []}, %{
               "inv-1" => true
             })
  end

  test "sentinel_degrade_integrity is denied when an in-flight tool's floor would be violated" do
    bg = integ_bg()
    s = Offline.initial_state()
    {:ok, s, _} = Offline.register_tool(s, bg, "delete_repo")
    {:ok, s, _} = Offline.delegate(s, bg, "root", "a1")

    {:ok, s, _} =
      Offline.invoke_start(s, bg, "a1", "delete_repo", "inv-1", true, %{"inv-1" => true}, [])

    # "delete_repo"'s integ_floor and integ_inspect_floor are both :trusted; degrading a1 to
    # :untrusted sits below both, so no gate vouch could rescue it.
    assert {:error, :integrity_floor_denied} =
             Offline.sentinel_degrade_integrity(s, bg, "a1", :untrusted, %{})
  end
end
