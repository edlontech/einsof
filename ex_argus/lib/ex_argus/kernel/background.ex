defmodule ExArgus.Kernel.Background do
  @moduledoc """
  Immutable background theory. Mirrors `argus_kernel::BackgroundTheory`.

  - `tools`: `%{tool_id => %{capabilities: [cap], egress: [egress], conf_floor: level,
    output_bounded: bool, issuer: issuer_id, integ_floor: integ_level,
    integ_inspect_floor: integ_level, output_integ: integ_level}}`. All tool integrity
    fields are **required** -- the NIF decode fails closed (raises) if a tool map omits
    them, rather than silently defaulting to a trusted level.
  - `allow_ceiling`: `%{egress_kind => conf_level}` — per-egress ALLOW ceiling (absent = deny-all)
  - `inspect_ceiling`: `%{egress_kind => conf_level}` — per-egress INSPECT ceiling (absent = no inspect band)
  - `trusted_issuers`: `[issuer_id]`
  - `instruction_issuer`: `%{instruction_id => issuer_id}`
  - `lever_integ_floor` / `lever_integ_inspect_floor`: robust-declassification integrity
    floors for the levers (`return_endorsed`/`grant_override`). A `defstruct` field cannot
    be omitted like a map key, so these default to `:attested` -- the most restrictive end
    of the lattice -- rather than the Rust builder's ungated `:untrusted` default. Callers
    that want a real (lower) floor must set it explicitly.
  """

  alias ExArgus.Kernel.Types

  defstruct tools: %{},
            allow_ceiling: %{},
            inspect_ceiling: %{},
            trusted_issuers: [],
            instruction_issuer: %{},
            lever_integ_floor: :attested,
            lever_integ_inspect_floor: :attested

  @type t :: %__MODULE__{
          tools: %{optional(Types.tool_id()) => Types.tool_metadata()},
          allow_ceiling: %{optional(Types.egress_kind()) => Types.conf_level()},
          inspect_ceiling: %{optional(Types.egress_kind()) => Types.conf_level()},
          trusted_issuers: [Types.issuer_id()],
          instruction_issuer: %{optional(Types.instruction_id()) => Types.issuer_id()},
          lever_integ_floor: Types.integ_level(),
          lever_integ_inspect_floor: Types.integ_level()
        }
end
