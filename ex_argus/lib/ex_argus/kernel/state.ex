defmodule ExArgus.Kernel.State do
  @moduledoc "Canonical read-only V5 projection of every V4 kernel state field."

  alias ExArgus.Kernel.Types

  defstruct agent_active: [],
            agent_parent: [],
            agent_cap: [],
            taint_levels: [],
            integ_levels: [],
            pending: [],
            challenges: [],
            consumed_ids: [],
            consumed_attestations: [],
            consumed_crossings: [],
            crossing_grants: [],
            tool_registered: []

  @type t :: %__MODULE__{
          agent_active: [Types.agent_id()],
          agent_parent: [{Types.agent_id(), Types.agent_id()}],
          agent_cap: [{Types.agent_id(), [Types.cap_kind()]}],
          taint_levels: [{Types.agent_id(), [Types.conf_level()]}],
          integ_levels: [{Types.agent_id(), [Types.integ_level()]}],
          pending: [{Types.invocation_id(), Types.PendingInvocation.t()}],
          challenges: [{Types.invocation_id(), Types.ChallengeScope.t()}],
          consumed_ids: [Types.invocation_id()],
          consumed_attestations: [Types.attestation_id()],
          consumed_crossings: [Types.crossing_id()],
          crossing_grants: [
            {{Types.agent_id(), Types.assignment_digest()}, Types.CrossingGrant.t()}
          ],
          tool_registered: [Types.tool_id()]
        }
end
