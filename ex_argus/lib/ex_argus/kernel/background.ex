defmodule ExArgus.Kernel.Background do
  @moduledoc """
  Immutable background theory. Mirrors `argus_kernel::BackgroundTheory`.

  - `tools`: `%{tool_id => %{capabilities: [cap], egress: [egress], conf_floor: level,
    output_bounded: bool, issuer: issuer_id}}`
  - `flow_policy`: `%{{level, egress} => mode}`
  - `flow_overrides`: `[{agent_id, tool_id, level}]`
  - `trusted_issuers`: `[issuer_id]`
  - `instruction_issuer`: `%{instruction_id => issuer_id}`
  """

  alias ExArgus.Kernel.Types

  defstruct tools: %{},
            flow_policy: %{},
            flow_overrides: [],
            trusted_issuers: [],
            instruction_issuer: %{}

  @type t :: %__MODULE__{
          tools: %{optional(Types.tool_id()) => Types.tool_metadata()},
          flow_policy: %{optional({Types.conf_level(), Types.egress_kind()}) => Types.flow_mode()},
          flow_overrides: [{Types.agent_id(), Types.tool_id(), Types.conf_level()}],
          trusted_issuers: [Types.issuer_id()],
          instruction_issuer: %{optional(Types.instruction_id()) => Types.issuer_id()}
        }
end
