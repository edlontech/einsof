defmodule ExArgus.Kernel.Background do
  @moduledoc """
  Immutable background theory. Mirrors `argus_kernel::BackgroundTheory`.

  - `tools`: `%{tool_id => %{capabilities: [cap], egress: [egress], conf_floor: level,
    output_bounded: bool, issuer: issuer_id}}`
  - `allow_ceiling`: `%{egress_kind => conf_level}` — per-egress ALLOW ceiling (absent = deny-all)
  - `inspect_ceiling`: `%{egress_kind => conf_level}` — per-egress INSPECT ceiling (absent = no inspect band)
  - `trusted_issuers`: `[issuer_id]`
  - `instruction_issuer`: `%{instruction_id => issuer_id}`
  """

  alias ExArgus.Kernel.Types

  defstruct tools: %{},
            allow_ceiling: %{},
            inspect_ceiling: %{},
            trusted_issuers: [],
            instruction_issuer: %{}

  @type t :: %__MODULE__{
          tools: %{optional(Types.tool_id()) => Types.tool_metadata()},
          allow_ceiling: %{optional(Types.egress_kind()) => Types.conf_level()},
          inspect_ceiling: %{optional(Types.egress_kind()) => Types.conf_level()},
          trusted_issuers: [Types.issuer_id()],
          instruction_issuer: %{optional(Types.instruction_id()) => Types.issuer_id()}
        }
end
