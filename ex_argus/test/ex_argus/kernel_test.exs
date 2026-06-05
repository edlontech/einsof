defmodule ExArgus.KernelTest do
  use ExUnit.Case, async: true

  alias ExArgus.Kernel
  alias ExArgus.Kernel.State

  test "content_gate_targets for invoke_start includes the new tool plus in-flight tools" do
    s = %State{
      in_flight: %{"a1" => ["inv-0"]},
      invocation_tool: %{"inv-0" => "old_tool"}
    }

    assert {"a1", tools} =
             Kernel.content_gate_targets(s, {:invoke_start, "a1", "new_tool", "inv-1"})

    assert Enum.sort(tools) == ["new_tool", "old_tool"]
  end

  test "content_gate_targets for return_unendorsed uses the parent's in-flight tools" do
    s = %State{
      in_flight: %{"parent" => ["inv-p"]},
      invocation_tool: %{"inv-p" => "p_tool"}
    }

    assert {"parent", ["p_tool"]} =
             Kernel.content_gate_targets(s, {:return_unendorsed, "child", "parent"})
  end

  test "content_gate_map evaluates the function over the targets" do
    s = %State{in_flight: %{"a1" => []}, invocation_tool: %{}}

    map =
      Kernel.content_gate_map(s, {:invoke_start, "a1", "t", "i"}, fn _agent, _tool -> true end)

    assert map == %{"t" => true}
  end

  test "initial_state delegates to the NIF" do
    assert "root" in Kernel.initial_state().agent_active
  end
end
