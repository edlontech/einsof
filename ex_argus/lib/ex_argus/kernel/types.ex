defmodule ExArgus.Kernel.Types do
  @moduledoc """
  Shared types for the kernel boundary.

  IDs are binaries; the kernel enums are atoms; sets cross as lists; struct-keyed maps
  (the flow policy) use tuple keys. These mirror the `argus_kernel` types exactly.
  """

  @typedoc "Agent identifier (e.g. `\"root\"`)."
  @type agent_id :: String.t()

  @typedoc "Tool identifier."
  @type tool_id :: String.t()

  @typedoc "Invocation identifier."
  @type invocation_id :: String.t()

  @typedoc "Tool/instruction issuer identifier."
  @type issuer_id :: String.t()

  @typedoc "Instruction identifier."
  @type instruction_id :: String.t()

  @typedoc "Confidentiality level (`Public < Internal < Sensitive < Restricted`)."
  @type conf_level :: :public | :internal | :sensitive | :restricted

  @typedoc "Integrity level (`Untrusted < Standard < Trusted < Attested`)."
  @type integ_level :: :untrusted | :standard | :trusted | :attested

  @typedoc "Egress channel kind."
  @type egress_kind :: :network_external | :network_internal | :filesystem_write | :ipc

  @typedoc "Capability kind (18 variants)."
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
          | :declassify
          | :credit_budget
          | :grant_override

  @typedoc "Flow-gate mode for a `{conf_level, egress_kind}` pair."
  @type flow_mode :: :allow | :inspect | :deny

  @typedoc """
  Per-tool metadata in the background theory (a plain map, not a struct).

  All keys are required -- the NIF decode fails closed (raises) on a missing key rather
  than defaulting, since a missing integrity field could otherwise silently mean "trusted".
  """
  @type tool_metadata :: %{
          capabilities: [cap_kind()],
          egress: [egress_kind()],
          conf_floor: conf_level(),
          output_bounded: boolean(),
          issuer: issuer_id(),
          integ_floor: integ_level(),
          integ_inspect_floor: integ_level(),
          output_integ: integ_level()
        }
end
