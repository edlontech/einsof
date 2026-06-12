defmodule ExArgus.OfflineTest do
  use ExUnit.Case, async: true

  alias ExArgus.Offline
  alias ExArgus.Kernel.State

  test "content_gate_targets for invoke_start includes the new tool plus in-flight tools" do
    s = %State{
      in_flight: %{"a1" => ["inv-0"]},
      invocation_tool: %{"inv-0" => "old_tool"}
    }

    assert {"a1", tools} =
             Offline.content_gate_targets(s, {:invoke_start, "a1", "new_tool", "inv-1"})

    assert Enum.sort(tools) == ["new_tool", "old_tool"]
  end

  test "content_gate_targets for return_unendorsed uses the parent's in-flight tools" do
    s = %State{
      in_flight: %{"parent" => ["inv-p"]},
      invocation_tool: %{"inv-p" => "p_tool"}
    }

    assert {"parent", ["p_tool"]} =
             Offline.content_gate_targets(s, {:return_unendorsed, "child", "parent"})
  end

  test "content_gate_map evaluates the function over the targets" do
    s = %State{in_flight: %{"a1" => []}, invocation_tool: %{}}

    map =
      Offline.content_gate_map(s, {:invoke_start, "a1", "t", "i"}, fn _agent, _tool -> true end)

    assert map == %{"t" => true}
  end

  test "initial_state delegates to the NIF" do
    assert "root" in Offline.initial_state().agent_active
  end
end
