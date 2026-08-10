defmodule ExArgus.Instance do
  @moduledoc """
  Opaque live V4 kernel resource with lifecycle observations and named transitions.

  An unexpected binding exception or internal error makes the handle terminal. Discard it rather
  than retrying an operationally ambiguous transition.
  """

  alias ExArgus.{Chain, Command, Envelope, Error, Limits, Native, Telemetry, Validation}
  alias ExArgus.Kernel.{Action, Background}

  @empty_projection %{verdict: nil, disposition: nil, branch: nil}
  @envelope_keys [
    :__struct__,
    :version,
    :sequence,
    :previous_digest,
    :digest,
    :command,
    :action
  ]

  defstruct [:resource]

  @opaque t :: %__MODULE__{resource: reference()}
  @type result :: {:ok, Envelope.t()} | {:error, Error.t()}

  @doc "Creates a fresh live instance at the fixed-root initial state."
  @spec new(Background.t()) :: {:ok, t()} | {:error, Error.t()}
  def new(background) do
    with {:ok, normalized} <- Validation.background(background),
         {:ok, resource} <- Native.instance_new(normalized) do
      {:ok, %__MODULE__{resource: resource}}
    else
      {:error, %Error{}} = error -> error
      {:error, reason} -> Error.from_native(reason)
      _other -> internal_error()
    end
  end

  @doc """
  Reconstructs a live instance from a complete validated V5 history and trusted anchor.

  Unexpected binding exceptions or result shapes fail closed as a typed internal error because no
  partial recovery handle is exposed.
  """
  @spec recover(Background.t(), [Envelope.t()], Chain.t()) :: {:ok, t()} | {:error, Error.t()}
  def recover(background, history, expected) do
    with {:ok, {normalized_background, normalized_history, normalized_expected}} <-
           Validation.recovery(background, history, expected),
         {:ok, recovery} <- recovery_new(normalized_background),
         :ok <- replay_history(recovery, normalized_history),
         {:ok, resource} <- recovery_finalize(recovery, normalized_expected) do
      {:ok, %__MODULE__{resource: resource}}
    end
  catch
    _kind, _reason -> internal_error()
  end

  @doc "Returns the canonical read-only V5 state projection."
  @spec state(t()) :: {:ok, ExArgus.Kernel.State.t()} | {:error, Error.t()}
  def state(instance), do: observe(instance, &Native.instance_state/1)

  @doc "Returns the accepted-history length and digest head."
  @spec status(t()) :: {:ok, Chain.t()} | {:error, Error.t()}
  def status(instance), do: observe(instance, &Native.instance_status/1)

  @doc "Registers an exact tool identity."
  @spec register_tool(t(), String.t()) :: result()
  def register_tool(instance, tool) do
    transition(instance, :register_tool, %Command.RegisterTool{tool: tool})
  end

  @doc "Unregisters an exact tool identity when it is not in use."
  @spec unregister_tool(t(), String.t()) :: result()
  def unregister_tool(instance, tool) do
    transition(instance, :unregister_tool, %Command.UnregisterTool{tool: tool})
  end

  @doc "Delegates a new child agent from an active grantor."
  @spec delegate(t(), String.t(), String.t()) :: result()
  def delegate(instance, grantor, grantee) do
    transition(instance, :delegate, %Command.Delegate{grantor: grantor, grantee: grantee})
  end

  @doc "Grants one capability from a parent to its direct child."
  @spec grant_capability(t(), String.t(), String.t(), ExArgus.Kernel.Types.cap_kind()) :: result()
  def grant_capability(instance, parent, child, cap) do
    transition(
      instance,
      :grant_capability,
      %Command.GrantCapability{parent: parent, child: child, cap: cap}
    )
  end

  @doc "Sets a root-provisioned crossing grant count."
  @spec grant_crossing(t(), String.t(), String.t(), String.t(), non_neg_integer()) :: result()
  def grant_crossing(instance, grantor, agent, assignment, n) do
    transition(
      instance,
      :grant_crossing,
      %Command.GrantCrossing{grantor: grantor, agent: agent, assignment: assignment, n: n}
    )
  end

  @doc "Revokes one active direct child."
  @spec revoke(t(), String.t(), String.t()) :: result()
  def revoke(instance, parent, target) do
    transition(instance, :revoke, %Command.Revoke{parent: parent, target: target})
  end

  @doc "Revokes a child after its recorded parent is inactive."
  @spec cascade_revoke(t(), String.t(), String.t()) :: result()
  def cascade_revoke(instance, child, parent) do
    transition(
      instance,
      :cascade_revoke,
      %Command.CascadeRevoke{child: child, parent: parent}
    )
  end

  @doc "Applies an exact replay-complete ingest command."
  @spec ingest(t(), Command.Ingest.t()) :: result()
  def ingest(instance, command), do: transition(instance, :ingest, command)

  @doc "Applies an exact replay-complete begin-invocation command."
  @spec begin_invocation(t(), Command.BeginInvocation.t()) :: result()
  def begin_invocation(instance, command), do: transition(instance, :begin_invocation, command)

  @doc "Applies an exact replay-complete inspected-authorization command."
  @spec authorize_inspected(t(), Command.AuthorizeInspected.t()) :: result()
  def authorize_inspected(instance, command) do
    transition(instance, :authorize_inspected, command)
  end

  @doc "Applies an exact replay-complete settlement command."
  @spec settle_invocation(t(), Command.SettleInvocation.t()) :: result()
  def settle_invocation(instance, command), do: transition(instance, :settle_invocation, command)

  @doc "Applies an exact replay-complete cross-output command."
  @spec cross_output(t(), Command.CrossOutput.t()) :: result()
  def cross_output(instance, command), do: transition(instance, :cross_output, command)

  @doc "Resolves a quarantined invocation through one settlement transition."
  @spec resolve_quarantine(
          t(),
          String.t(),
          :success | :failure,
          ExArgus.Kernel.Types.ResolutionAttestation.t()
        ) :: result()
  def resolve_quarantine(instance, invocation, outcome, attestation) do
    command = %Command.SettleInvocation{
      inv: invocation,
      outcome: outcome,
      resolution: attestation
    }

    transition(
      instance,
      :settle_invocation,
      command,
      &Validation.quarantine_resolution/1
    )
  end

  defp recovery_new(background) do
    case Native.recovery_new(background) do
      {:ok, resource} when is_reference(resource) -> {:ok, resource}
      {:error, reason} -> Error.from_recovery(reason, nil)
      _other -> internal_error()
    end
  end

  defp replay_history(recovery, history) do
    history
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn {envelope, index}, :ok ->
      case Native.recovery_replay(recovery, envelope) do
        {:ok, {}} -> {:cont, :ok}
        {:error, reason} -> {:halt, Error.from_recovery(reason, index)}
        _other -> {:halt, internal_error(index)}
      end
    end)
  end

  defp recovery_finalize(recovery, expected) do
    case Native.recovery_finalize(recovery, expected) do
      {:ok, resource} when is_reference(resource) -> {:ok, resource}
      {:error, reason} -> Error.from_recovery(reason, nil)
      _other -> internal_error()
    end
  end

  defp observe(instance, native) do
    with {:ok, resource} <- Validation.instance(instance) do
      case native.(resource) do
        {:ok, value} -> {:ok, value}
        {:error, reason} -> Error.from_native(reason)
        _other -> internal_error()
      end
    end
  end

  defp transition(instance, command_name, command, validator \\ nil) do
    started = System.monotonic_time()
    validator = transition_validator(command_name, validator)

    try do
      {result, outcome, sequence, reason, projection} =
        with {:ok, resource} <- Validation.instance(instance),
             {:ok, normalized} <- validator.(command) do
          resource
          |> Native.instance_apply(normalized)
          |> transition_result(normalized)
        else
          {:error, %Error{} = error} -> classified_error(error)
        end

      duration = System.monotonic_time() - started
      Telemetry.emit_transition(command_name, outcome, duration, sequence, reason, projection)
      result
    catch
      kind, reason ->
        duration = System.monotonic_time() - started

        Telemetry.emit_transition(
          command_name,
          :internal_error,
          duration,
          nil,
          :native_contract_violation,
          @empty_projection
        )

        :erlang.raise(kind, reason, __STACKTRACE__)
    end
  end

  defp transition_validator(command_name, nil),
    do: &Validation.command(&1, command_name)

  defp transition_validator(_command_name, validator), do: validator

  defp transition_result({:ok, %Envelope{} = envelope}, command) do
    case envelope_projection(envelope, command) do
      {:ok, projection} ->
        {{:ok, envelope}, :accepted, envelope.sequence, nil, projection}

      :error ->
        classified_error(%Error{class: :internal, reason: :native_contract_violation})
    end
  end

  defp transition_result({:error, reason}, _command) do
    reason
    |> Error.from_native()
    |> then(fn {:error, error} -> classified_error(error) end)
  end

  defp transition_result(_result, _command) do
    classified_error(%Error{class: :internal, reason: :native_contract_violation})
  end

  defp classified_error(%Error{} = error) do
    outcome =
      case error.class do
        :kernel -> :kernel_refused
        :boundary -> :boundary_refused
        :internal -> :internal_error
      end

    {{:error, error}, outcome, nil, error.reason, @empty_projection}
  end

  defp envelope_projection(envelope, command) do
    with true <- exact_envelope?(envelope),
         true <- envelope.version == 5,
         true <- valid_sequence?(envelope.sequence),
         true <- valid_digest?(envelope.previous_digest),
         true <- valid_digest?(envelope.digest),
         true <- envelope.command == command,
         {:ok, projection} <- Action.telemetry_projection(envelope.action) do
      {:ok, projection}
    else
      _invalid -> :error
    end
  end

  defp exact_envelope?(envelope) do
    map_size(envelope) == length(@envelope_keys) and
      Enum.all?(@envelope_keys, &Map.has_key?(envelope, &1))
  end

  defp valid_sequence?(sequence) do
    is_integer(sequence) and sequence > 0 and sequence <= Limits.max_accepted_sequence()
  end

  defp valid_digest?(digest), do: is_binary(digest) and byte_size(digest) == 32

  defp internal_error(index \\ nil) do
    {:error, %Error{class: :internal, reason: :native_contract_violation, index: index}}
  end
end
