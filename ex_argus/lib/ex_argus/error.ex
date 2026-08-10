defmodule ExArgus.Error do
  @moduledoc "Closed, content-free V5 boundary error."

  defstruct [:class, :reason, path: [], index: nil, cause: nil]

  @type class :: :boundary | :kernel | :recovery | :internal
  @type path_component :: atom() | non_neg_integer()
  @type boundary_reason ::
          :invalid_type
          | :invalid_struct
          | :invalid_keys
          | :invalid_utf8
          | :empty_value
          | :value_too_large
          | :unknown_enum
          | :duplicate_value
          | :integer_out_of_range
          | :capacity_exceeded
          | :sequence_exhausted
          | :instance_busy
  @type kernel_reason ::
          :tool_already_registered
          | :tool_not_registered
          | :tool_in_use
          | :agent_inactive
          | :agent_already_active
          | :root_not_allowed
          | :not_direct_child
          | :parent_still_active
          | :agent_has_children
          | :capability_missing
          | :not_root
          | :invocation_exists
          | :invocation_replayed
          | :not_pending
          | :egress_not_narrowing
          | :egress_not_covering
          | :incoherent_policy
          | :challenge_already_open
          | :clearance_denied
          | :flow_gate_blocked
          | :authorizer_denied
          | :integrity_floor_denied
          | :pairwise_conflict
          | :challenge_not_open
          | :challenge_scope_mismatch
          | :attestation_consumed
          | :inspection_negative
          | :blocked_pending
          | :not_quarantined
          | :quarantine_resolution_required
          | :resolution_attestation_invalid
          | :ingest_hold_failed
          | :provenance_not_dominated
          | :crossing_replayed
          | :grant_missing
          | :grant_exhausted
          | :source_in_flight
          | :crossing_bound_violated
          | :crossing_hold_failed
          | :event_store
  @type recovery_reason ::
          :invalid_version
          | :sequence_mismatch
          | :previous_digest_mismatch
          | :action_mismatch
          | :digest_mismatch
          | :replay_refused
          | :recovery_consumed
          | :final_anchor_mismatch
  @type internal_reason :: :resource_poisoned | :native_contract_violation
  @type reason :: boundary_reason() | kernel_reason() | recovery_reason() | internal_reason()

  @type t :: %__MODULE__{
          class: class(),
          reason: reason(),
          path: [path_component()],
          index: non_neg_integer() | nil,
          cause: kernel_reason() | nil
        }

  @kernel_reasons [
    :tool_already_registered,
    :tool_not_registered,
    :tool_in_use,
    :agent_inactive,
    :agent_already_active,
    :root_not_allowed,
    :not_direct_child,
    :parent_still_active,
    :agent_has_children,
    :capability_missing,
    :not_root,
    :invocation_exists,
    :invocation_replayed,
    :not_pending,
    :egress_not_narrowing,
    :egress_not_covering,
    :incoherent_policy,
    :challenge_already_open,
    :clearance_denied,
    :flow_gate_blocked,
    :authorizer_denied,
    :integrity_floor_denied,
    :pairwise_conflict,
    :challenge_not_open,
    :challenge_scope_mismatch,
    :attestation_consumed,
    :inspection_negative,
    :blocked_pending,
    :not_quarantined,
    :quarantine_resolution_required,
    :resolution_attestation_invalid,
    :ingest_hold_failed,
    :provenance_not_dominated,
    :crossing_replayed,
    :grant_missing,
    :grant_exhausted,
    :source_in_flight,
    :crossing_bound_violated,
    :crossing_hold_failed,
    :event_store
  ]

  @doc false
  @spec kernel_reasons() :: [kernel_reason()]
  def kernel_reasons, do: @kernel_reasons

  @doc false
  @spec from_native(term()) :: {:error, t()}
  for reason <- @kernel_reasons do
    def from_native({:kernel, unquote(reason)}) do
      {:error, %__MODULE__{class: :kernel, reason: unquote(reason)}}
    end
  end

  def from_native(:instance_busy), do: boundary(:instance_busy)
  def from_native(:capacity_exceeded), do: boundary(:capacity_exceeded)
  def from_native(:sequence_exhausted), do: boundary(:sequence_exhausted)

  def from_native(:resource_poisoned) do
    {:error, %__MODULE__{class: :internal, reason: :resource_poisoned}}
  end

  def from_native(_reason) do
    {:error, %__MODULE__{class: :internal, reason: :native_contract_violation}}
  end

  @doc false
  @spec from_recovery(term(), non_neg_integer() | nil) :: {:error, t()}
  for reason <- [
        :invalid_version,
        :sequence_mismatch,
        :previous_digest_mismatch,
        :action_mismatch,
        :digest_mismatch,
        :recovery_consumed,
        :final_anchor_mismatch
      ] do
    def from_recovery(unquote(reason), index) do
      {:error, %__MODULE__{class: :recovery, reason: unquote(reason), index: index}}
    end
  end

  for cause <- @kernel_reasons do
    def from_recovery({:replay_refused, unquote(cause)}, index) do
      {:error,
       %__MODULE__{
         class: :recovery,
         reason: :replay_refused,
         index: index,
         cause: unquote(cause)
       }}
    end
  end

  def from_recovery(reason, index)
      when reason in [:instance_busy, :capacity_exceeded, :sequence_exhausted] do
    {:error, %__MODULE__{class: :boundary, reason: reason, index: index}}
  end

  def from_recovery(:resource_poisoned, index) do
    {:error, %__MODULE__{class: :internal, reason: :resource_poisoned, index: index}}
  end

  def from_recovery(_reason, index) do
    {:error, %__MODULE__{class: :internal, reason: :native_contract_violation, index: index}}
  end

  defp boundary(reason), do: {:error, %__MODULE__{class: :boundary, reason: reason}}
end
