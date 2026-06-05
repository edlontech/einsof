defmodule ExArgus.Kernel.State do
  @moduledoc """
  An Argus kernel state. Mirrors `argus_kernel::KernelState`. Sets are represented as
  lists (the kernel keeps them unique); maps are plain maps. IDs are binaries and the
  kernel enums are atoms.

  This struct's fields define the snapshot wire shape stamped by `ExArgus.state_version/0`.
  Bump that version whenever these fields or the NIF encode/decode change.
  """

  alias ExArgus.Kernel.Types

  defstruct agent_active: [],
            agent_parent: %{},
            agent_cap: %{},
            taint_levels: %{},
            in_flight: %{},
            invocation_tool: %{},
            tool_registered: [],
            gh_taint_invoked: %{},
            gh_taint_received: %{},
            agent_instruction: %{},
            override_used: %{},
            agent_budget: %{}

  @type t :: %__MODULE__{
          agent_active: [Types.agent_id()],
          agent_parent: %{optional(Types.agent_id()) => Types.agent_id()},
          agent_cap: %{optional(Types.agent_id()) => [Types.cap_kind()]},
          taint_levels: %{optional(Types.agent_id()) => [Types.conf_level()]},
          in_flight: %{optional(Types.agent_id()) => [Types.invocation_id()]},
          invocation_tool: %{optional(Types.invocation_id()) => Types.tool_id()},
          tool_registered: [Types.tool_id()],
          gh_taint_invoked: %{optional(Types.agent_id()) => [Types.conf_level()]},
          gh_taint_received: %{optional(Types.agent_id()) => [Types.conf_level()]},
          agent_instruction: %{optional(Types.agent_id()) => [Types.instruction_id()]},
          override_used: %{optional(Types.agent_id()) => [{Types.tool_id(), Types.conf_level()}]},
          agent_budget: %{optional(Types.agent_id()) => Types.budget_level()}
        }
end
