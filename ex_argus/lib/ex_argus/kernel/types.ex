defmodule ExArgus.Kernel.Types do
  @moduledoc "Closed V4 value vocabulary shared by commands, actions, and state projection."

  @type agent_id :: String.t()
  @type tool_id :: String.t()
  @type invocation_id :: String.t()
  @type challenge_id :: String.t()
  @type attestation_id :: String.t()
  @type content_hash :: String.t()
  @type policy_digest :: String.t()
  @type crossing_id :: String.t()
  @type assignment_digest :: String.t()

  @type conf_level :: :public | :internal | :sensitive | :restricted
  @type integ_level :: :untrusted | :standard | :trusted | :attested
  @type egress_kind :: :network_external | :network_internal | :filesystem_write | :ipc
  @type cap_kind ::
          :filesystem_read
          | :filesystem_write
          | :filesystem_delete
          | :network_egress
          | :network_ingress
          | :execution_shell
          | :execution_code
          | :credentials
          | :system_info
          | :system_modify
          | :clipboard
          | :browser_navigate
          | :database_read
          | :database_write
          | :ipc
  @type verdict :: :allow | :inspection_required | :deny
  @type disposition :: :permitted | :blocked | :monitor_bypassed
  @type mode :: :enforce | :monitor
  @type outcome :: :success | :failure | :ambiguous
  @type fallback :: :fail | :release_unendorsed
  @type cross_branch :: :endorsed | :unendorsed | :fail
  @type admission :: :plain | {:inspected, attestation_id()} | :bypassed
end

defmodule ExArgus.Kernel.Types.ActionPolicySnapshot do
  @moduledoc "Frozen V4 action policy recorded in begin-invocation commands."

  alias ExArgus.Kernel.Types

  defstruct [
    :tool,
    :required_caps,
    :conf_clearance,
    :integ_floor,
    :integ_inspect,
    :output_conf,
    :output_integ,
    :declared_egress,
    :policy_digest
  ]

  @type t :: %__MODULE__{
          tool: Types.tool_id(),
          required_caps: [Types.cap_kind()],
          conf_clearance: Types.conf_level(),
          integ_floor: Types.integ_level(),
          integ_inspect: Types.integ_level(),
          output_conf: Types.conf_level(),
          output_integ: Types.integ_level(),
          declared_egress: [Types.egress_kind()],
          policy_digest: Types.policy_digest()
        }
end

defmodule ExArgus.Kernel.Types.InspectionAttestation do
  @moduledoc "Frozen V4 inspection evidence."

  alias ExArgus.Kernel.Types

  defstruct [:id, :inv, :challenge, :args_hash, :policy_digest, :positive]

  @type t :: %__MODULE__{
          id: Types.attestation_id(),
          inv: Types.invocation_id(),
          challenge: Types.challenge_id(),
          args_hash: Types.content_hash(),
          policy_digest: Types.policy_digest(),
          positive: boolean()
        }
end

defmodule ExArgus.Kernel.Types.ResolutionAttestation do
  @moduledoc "Frozen V4 quarantine-resolution evidence."

  alias ExArgus.Kernel.Types

  defstruct [:id, :inv, :outcome]

  @type t :: %__MODULE__{
          id: Types.attestation_id(),
          inv: Types.invocation_id(),
          outcome: Types.outcome()
        }
end

defmodule ExArgus.Kernel.Types.ConformanceAttestation do
  @moduledoc "Frozen V4 crossing-conformance evidence."

  alias ExArgus.Kernel.Types

  defstruct [:id, :output, :src, :rcv, :descriptor, :assignment, :positive]

  @type t :: %__MODULE__{
          id: Types.attestation_id(),
          output: Types.content_hash(),
          src: Types.agent_id(),
          rcv: Types.agent_id(),
          descriptor: Types.content_hash(),
          assignment: Types.assignment_digest(),
          positive: boolean()
        }
end

defmodule ExArgus.Kernel.Types.CrossInput do
  @moduledoc "Complete V4 cross-output input."

  alias ExArgus.Kernel.Types
  alias ExArgus.Kernel.Types.ConformanceAttestation

  defstruct [
    :src,
    :rcv,
    :crossing,
    :output_hash,
    :descriptor,
    :fallback,
    :t_integ,
    :t_conf,
    :assignment,
    :evidence,
    :released_conf,
    :released_integ
  ]

  @type t :: %__MODULE__{
          src: Types.agent_id(),
          rcv: Types.agent_id(),
          crossing: Types.crossing_id(),
          output_hash: Types.content_hash(),
          descriptor: Types.content_hash(),
          fallback: Types.fallback(),
          t_integ: Types.integ_level(),
          t_conf: Types.conf_level() | nil,
          assignment: Types.assignment_digest(),
          evidence: ConformanceAttestation.t() | nil,
          released_conf: Types.conf_level(),
          released_integ: Types.integ_level()
        }
end

defmodule ExArgus.Kernel.Types.PendingInvocation do
  @moduledoc "Canonical pending-invocation projection."

  alias ExArgus.Kernel.Types
  alias ExArgus.Kernel.Types.ActionPolicySnapshot

  defstruct [:agent, :policy, :egress, :admission, :disposition, :authorized, :quarantined]

  @type t :: %__MODULE__{
          agent: Types.agent_id(),
          policy: ActionPolicySnapshot.t(),
          egress: [Types.egress_kind()],
          admission: Types.admission(),
          disposition: Types.disposition(),
          authorized: boolean(),
          quarantined: boolean()
        }
end

defmodule ExArgus.Kernel.Types.ChallengeScope do
  @moduledoc "Canonical open-challenge projection."

  alias ExArgus.Kernel.Types
  alias ExArgus.Kernel.Types.ActionPolicySnapshot

  defstruct [:challenge, :agent, :policy, :egress, :args_hash, :authorized]

  @type t :: %__MODULE__{
          challenge: Types.challenge_id(),
          agent: Types.agent_id(),
          policy: ActionPolicySnapshot.t(),
          egress: [Types.egress_kind()],
          args_hash: Types.content_hash(),
          authorized: boolean()
        }
end

defmodule ExArgus.Kernel.Types.CrossingGrant do
  @moduledoc "Canonical crossing-grant counters."

  defstruct [:remaining, :provisioned]

  @type t :: %__MODULE__{remaining: non_neg_integer(), provisioned: non_neg_integer()}
end
