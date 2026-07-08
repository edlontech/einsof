defmodule ExArgus.Kernel.State do
  @moduledoc """
  An Argus kernel state. Mirrors `argus_kernel::KernelState`. Sets are represented as
  lists (the kernel keeps them unique); maps are plain maps. IDs are binaries and the
  kernel enums are atoms.

  This struct's fields define the snapshot wire shape stamped by `ExArgus.state_version/0`.
  Bump that version whenever these fields or the NIF encode/decode change. As of version 4
  (TzimtzumV3) the fields are `integ_levels` (dual of `taint_levels`), `invocation_used`
  (global freshness history) and `invocation_egress` (per-invocation attested egress),
  alongside the numeric `agent_budget` meter.
  """

  alias ExArgus.Kernel.Types

  defstruct agent_active: [],
            agent_parent: %{},
            agent_cap: %{},
            taint_levels: %{},
            integ_levels: %{},
            in_flight: %{},
            invocation_tool: %{},
            invocation_used: [],
            invocation_egress: %{},
            tool_registered: [],
            agent_instruction: %{},
            override_used: %{},
            flow_override: %{},
            agent_budget: %{}

  @type t :: %__MODULE__{
          agent_active: [Types.agent_id()],
          agent_parent: %{optional(Types.agent_id()) => Types.agent_id()},
          agent_cap: %{optional(Types.agent_id()) => [Types.cap_kind()]},
          taint_levels: %{optional(Types.agent_id()) => [Types.conf_level()]},
          integ_levels: %{optional(Types.agent_id()) => [Types.integ_level()]},
          in_flight: %{optional(Types.agent_id()) => [Types.invocation_id()]},
          invocation_tool: %{optional(Types.invocation_id()) => Types.tool_id()},
          invocation_used: [Types.invocation_id()],
          invocation_egress: %{optional(Types.invocation_id()) => [Types.egress_kind()]},
          tool_registered: [Types.tool_id()],
          agent_instruction: %{optional(Types.agent_id()) => [Types.instruction_id()]},
          override_used: %{optional(Types.agent_id()) => [{Types.tool_id(), Types.conf_level()}]},
          flow_override: %{optional(Types.agent_id()) => [{Types.tool_id(), Types.conf_level()}]},
          agent_budget: %{optional(Types.agent_id()) => non_neg_integer()}
        }
end
