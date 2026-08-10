defmodule ExArgus.Kernel.Action do
  @moduledoc "Closed union of the twelve computed V4 kernel actions."

  @type t ::
          ExArgus.Kernel.Action.RegisterTool.t()
          | ExArgus.Kernel.Action.UnregisterTool.t()
          | ExArgus.Kernel.Action.Delegate.t()
          | ExArgus.Kernel.Action.GrantCapability.t()
          | ExArgus.Kernel.Action.GrantCrossing.t()
          | ExArgus.Kernel.Action.Revoke.t()
          | ExArgus.Kernel.Action.CascadeRevoke.t()
          | ExArgus.Kernel.Action.Ingest.t()
          | ExArgus.Kernel.Action.BeginInvocation.t()
          | ExArgus.Kernel.Action.AuthorizeInspected.t()
          | ExArgus.Kernel.Action.SettleInvocation.t()
          | ExArgus.Kernel.Action.CrossOutput.t()
end

defmodule ExArgus.Kernel.Action.RegisterTool do
  @moduledoc false
  defstruct [:tool]
  @type t :: %__MODULE__{tool: String.t()}
end

defmodule ExArgus.Kernel.Action.UnregisterTool do
  @moduledoc false
  defstruct [:tool]
  @type t :: %__MODULE__{tool: String.t()}
end

defmodule ExArgus.Kernel.Action.Delegate do
  @moduledoc false
  defstruct [:grantor, :grantee]
  @type t :: %__MODULE__{grantor: String.t(), grantee: String.t()}
end

defmodule ExArgus.Kernel.Action.GrantCapability do
  @moduledoc false
  defstruct [:parent, :child, :cap]

  @type t :: %__MODULE__{
          parent: String.t(),
          child: String.t(),
          cap: ExArgus.Kernel.Types.cap_kind()
        }
end

defmodule ExArgus.Kernel.Action.GrantCrossing do
  @moduledoc false
  defstruct [:grantor, :agent, :assignment, :n]

  @type t :: %__MODULE__{
          grantor: String.t(),
          agent: String.t(),
          assignment: String.t(),
          n: non_neg_integer()
        }
end

defmodule ExArgus.Kernel.Action.Revoke do
  @moduledoc false
  defstruct [:parent, :target]
  @type t :: %__MODULE__{parent: String.t(), target: String.t()}
end

defmodule ExArgus.Kernel.Action.CascadeRevoke do
  @moduledoc false
  defstruct [:child, :parent]
  @type t :: %__MODULE__{child: String.t(), parent: String.t()}
end

defmodule ExArgus.Kernel.Action.Ingest do
  @moduledoc false
  defstruct [:agent, :src, :pconf, :pinteg, :disposition]

  @type t :: %__MODULE__{
          agent: String.t(),
          src: String.t() | nil,
          pconf: ExArgus.Kernel.Types.conf_level(),
          pinteg: ExArgus.Kernel.Types.integ_level(),
          disposition: ExArgus.Kernel.Types.disposition()
        }
end

defmodule ExArgus.Kernel.Action.BeginInvocation do
  @moduledoc false
  defstruct [:agent, :inv, :tool, :verdict, :authorized]

  @type t :: %__MODULE__{
          agent: String.t(),
          inv: String.t(),
          tool: String.t(),
          verdict: ExArgus.Kernel.Types.verdict(),
          authorized: boolean()
        }
end

defmodule ExArgus.Kernel.Action.AuthorizeInspected do
  @moduledoc false
  defstruct [:inv, :attestation, :admitted]
  @type t :: %__MODULE__{inv: String.t(), attestation: String.t(), admitted: boolean()}
end

defmodule ExArgus.Kernel.Action.SettleInvocation do
  @moduledoc false
  defstruct [:inv, :agent, :disposition, :outcome, :clvl, :ilvl, :resolution]

  @type t :: %__MODULE__{
          inv: String.t(),
          agent: String.t(),
          disposition: ExArgus.Kernel.Types.disposition(),
          outcome: ExArgus.Kernel.Types.outcome(),
          clvl: ExArgus.Kernel.Types.conf_level(),
          ilvl: ExArgus.Kernel.Types.integ_level(),
          resolution: String.t() | nil
        }
end

defmodule ExArgus.Kernel.Action.CrossOutput do
  @moduledoc false
  defstruct [:src, :rcv, :crossing, :branch, :disposition]

  @type t :: %__MODULE__{
          src: String.t(),
          rcv: String.t(),
          crossing: String.t(),
          branch: ExArgus.Kernel.Types.cross_branch(),
          disposition: ExArgus.Kernel.Types.disposition()
        }
end
