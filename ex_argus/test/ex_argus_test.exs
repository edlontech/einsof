defmodule ExArgusTest do
  use ExUnit.Case, async: true

  alias ExArgus.Kernel.State

  describe "state_version/0" do
    test "returns a positive integer wire-shape stamp" do
      v = ExArgus.state_version()
      assert is_integer(v)
      assert v > 0
    end
  end

  describe "Kernel.State wire shape is pinned to the current version" do
    # The field set encoded across the NIF for the current state_version. If this fails,
    # the State struct's fields changed: bump ExArgus.state_version/0 (lib/ex_argus.ex),
    # the NIF encode/decode, and this golden list together.
    @golden_fields ~w(
      agent_active agent_budget agent_cap agent_instruction agent_parent
      integ_levels in_flight invocation_egress invocation_tool invocation_used
      flow_override override_used taint_levels tool_registered
    )a

    test "State has exactly the golden fields for the current version" do
      actual = %State{} |> Map.from_struct() |> Map.keys()
      assert Enum.sort(actual) == Enum.sort(@golden_fields)
    end
  end
end
