defmodule ExArgus.Envelope do
  @moduledoc "One accepted, digest-chained V5 transition envelope."

  defstruct [:version, :sequence, :previous_digest, :digest, :command, :action]

  @type digest :: <<_::256>>
  @type t :: %__MODULE__{
          version: 5,
          sequence: pos_integer(),
          previous_digest: digest(),
          digest: digest(),
          command: ExArgus.Command.t(),
          action: ExArgus.Kernel.Action.t()
        }
end
