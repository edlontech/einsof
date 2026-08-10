defmodule ExArgus.Kernel.Background do
  @moduledoc "Immutable V4 background. The root identity is fixed and is not configurable."

  alias ExArgus.Kernel.Types

  defstruct [:mode, allow_ceiling: %{}, inspect_ceiling: %{}]

  @type ceiling :: %{required(Types.egress_kind()) => Types.conf_level() | nil}
  @type t :: %__MODULE__{
          mode: Types.mode(),
          allow_ceiling: ceiling(),
          inspect_ceiling: ceiling()
        }
end
