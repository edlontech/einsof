defmodule ExArgus.Chain do
  @moduledoc "Current V5 accepted-history length and digest head."

  defstruct [:version, :sequence, :head]

  @type t :: %__MODULE__{version: 5, sequence: non_neg_integer(), head: <<_::256>>}
end
