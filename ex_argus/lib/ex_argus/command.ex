defmodule ExArgus.Command do
  @moduledoc "Closed replay-complete V4 command union."

  @type t ::
          ExArgus.Command.RegisterTool.t()
          | ExArgus.Command.UnregisterTool.t()
          | ExArgus.Command.Delegate.t()
          | ExArgus.Command.GrantCapability.t()
          | ExArgus.Command.GrantCrossing.t()
          | ExArgus.Command.Revoke.t()
          | ExArgus.Command.CascadeRevoke.t()
          | ExArgus.Command.Ingest.t()
          | ExArgus.Command.BeginInvocation.t()
          | ExArgus.Command.AuthorizeInspected.t()
          | ExArgus.Command.SettleInvocation.t()
          | ExArgus.Command.CrossOutput.t()
end

defmodule ExArgus.Command.RegisterTool do
  @moduledoc false
  defstruct [:tool]
  @type t :: %__MODULE__{tool: ExArgus.Kernel.Types.tool_id()}
end

defmodule ExArgus.Command.UnregisterTool do
  @moduledoc false
  defstruct [:tool]
  @type t :: %__MODULE__{tool: ExArgus.Kernel.Types.tool_id()}
end

defmodule ExArgus.Command.Delegate do
  @moduledoc false
  defstruct [:grantor, :grantee]
  @type t :: %__MODULE__{grantor: String.t(), grantee: String.t()}
end

defmodule ExArgus.Command.GrantCapability do
  @moduledoc false
  defstruct [:parent, :child, :cap]

  @type t :: %__MODULE__{
          parent: String.t(),
          child: String.t(),
          cap: ExArgus.Kernel.Types.cap_kind()
        }
end

defmodule ExArgus.Command.GrantCrossing do
  @moduledoc false
  defstruct [:grantor, :agent, :assignment, :n]

  @type t :: %__MODULE__{
          grantor: String.t(),
          agent: String.t(),
          assignment: String.t(),
          n: non_neg_integer()
        }
end

defmodule ExArgus.Command.Revoke do
  @moduledoc false
  defstruct [:parent, :target]
  @type t :: %__MODULE__{parent: String.t(), target: String.t()}
end

defmodule ExArgus.Command.CascadeRevoke do
  @moduledoc false
  defstruct [:child, :parent]
  @type t :: %__MODULE__{child: String.t(), parent: String.t()}
end

defmodule ExArgus.Command.Ingest do
  @moduledoc false
  defstruct [:agent, :src, :pconf, :pinteg]

  @type t :: %__MODULE__{
          agent: String.t(),
          src: String.t() | nil,
          pconf: ExArgus.Kernel.Types.conf_level(),
          pinteg: ExArgus.Kernel.Types.integ_level()
        }
end

defmodule ExArgus.Command.BeginInvocation do
  @moduledoc false
  defstruct [:agent, :inv, :challenge, :policy, :egress, :args_hash, :authorized]

  @type t :: %__MODULE__{
          agent: String.t(),
          inv: String.t(),
          challenge: String.t(),
          policy: ExArgus.Kernel.Types.ActionPolicySnapshot.t(),
          egress: [ExArgus.Kernel.Types.egress_kind()],
          args_hash: String.t(),
          authorized: boolean()
        }
end

defmodule ExArgus.Command.AuthorizeInspected do
  @moduledoc false
  defstruct [:inv, :attestation]

  @type t :: %__MODULE__{
          inv: String.t(),
          attestation: ExArgus.Kernel.Types.InspectionAttestation.t()
        }
end

defmodule ExArgus.Command.SettleInvocation do
  @moduledoc false
  defstruct [:inv, :outcome, :resolution]

  @type t :: %__MODULE__{
          inv: String.t(),
          outcome: ExArgus.Kernel.Types.outcome(),
          resolution: ExArgus.Kernel.Types.ResolutionAttestation.t() | nil
        }
end

defmodule ExArgus.Command.CrossOutput do
  @moduledoc false
  defstruct [:input]
  @type t :: %__MODULE__{input: ExArgus.Kernel.Types.CrossInput.t()}
end
