defmodule ExArgus.Instance do
  @moduledoc """
  Live, stateful interface to the verified argus-kernel.

  The only mutable copy of the `KernelState` lives inside a refcounted Rust NIF resource
  (`new/1` returns an opaque handle). Each transition runs the pure kernel transition under
  a lock, commits on success and leaves state untouched on refusal, returning
  `{:ok, seq, action}` or `{:error, reason}`. `seq` is a monotone counter stamped per
  ACCEPTED transition -- persist it alongside the entry for gap/reorder detection.

  State only ever EXPORTS (`state/1`, read-only); no function imports a state term back into
  a handle. This makes out-of-reachable-space state -- the P1 hazard of the state-passing
  `ExArgus.Offline` API -- unrepresentable on the live path. The background is bound at
  `new/1`/`recover/2` and is immutable for the instance's life (matches the spec semantics
  that background is constant across a trajectory); a policy change means a new instance
  recovered under the new background.
  """

  alias ExArgus.Kernel.State
  alias ExArgus.{Native, Offline}

  @type t :: reference()
  @type background :: ExArgus.Kernel.Background.t()
  @type id :: String.t()
  @type outcome :: {:ok, non_neg_integer, tuple} | {:error, Offline.error_reason()}

  @recoverable_transitions ~w(
    register_tool load_instruction delegate grant_capability revoke cascade_revoke
    return_endorsed sentinel_credit_budget grant_override invoke_start invoke_complete
    return_unendorsed sentinel_elevate_taint
  )a

  @doc "Create a fresh instance at the initial state, with `bg` bound for its lifetime."
  @spec new(background) :: t
  defdelegate new(bg), to: Native, as: :instance_new

  @typedoc "A recorded kernel-call log entry, identical to `ExArgus.Replay.entry/0`."
  @type entry :: {atom, [term]}
  @type recovery_error :: %{
          index: non_neg_integer,
          entry: entry,
          reason: Offline.error_reason() | :unknown_transition
        }

  @doc """
  Rebuild an instance by replaying a recorded `{fun, args}` log from the initial state
  under `bg`, applying each entry through the real transitions. Because the log records
  only ACCEPTED transitions, a refusal during replay proves corruption / tampering / a
  wrong background: recovery aborts strictly with the offending `index`, `entry`, and
  `reason`, and returns NO instance.

  Replay-by-transitions means even a tampered log can only land a protocol-REACHABLE
  state -- every guard is re-enforced during the fold. (Log integrity -- which reachable
  state, audit completeness -- is hash-chain / mesh territory.) For the lenient
  skip-and-continue mode, use offline `ExArgus.Replay.run/2`.

  An entry whose `fun` is not one of the 13 kernel transitions aborts immediately with
  `reason: :unknown_transition`; no `apply` is attempted.
  """
  @spec recover(background, [entry]) :: {:ok, t} | {:error, recovery_error}
  def recover(bg, log) do
    handle = new(bg)

    result =
      log
      |> Enum.with_index()
      |> Enum.reduce_while(:ok, fn {{fun, args}, i}, :ok ->
        if fun in @recoverable_transitions do
          case apply(__MODULE__, fun, [handle | args]) do
            {:ok, _seq, _action} -> {:cont, :ok}
            {:error, reason} -> {:halt, {:error, %{index: i, entry: {fun, args}, reason: reason}}}
          end
        else
          {:halt, {:error, %{index: i, entry: {fun, args}, reason: :unknown_transition}}}
        end
      end)

    case result do
      :ok -> {:ok, handle}
      {:error, _} = error -> error
    end
  end

  @doc "Read-only snapshot of the live state (telemetry/UI/diagnostics)."
  @spec state(t) :: State.t()
  defdelegate state(handle), to: Native, as: :instance_state

  @doc "The monotone count of accepted transitions on this instance."
  @spec seq(t) :: non_neg_integer
  defdelegate seq(handle), to: Native, as: :instance_seq

  defdelegate register_tool(handle, tool), to: Native, as: :instance_register_tool
  defdelegate load_instruction(handle, agent, instr), to: Native, as: :instance_load_instruction
  defdelegate delegate(handle, grantor, grantee), to: Native, as: :instance_delegate

  defdelegate grant_capability(handle, parent, child, cap),
    to: Native,
    as: :instance_grant_capability

  defdelegate revoke(handle, parent, target), to: Native, as: :instance_revoke
  defdelegate cascade_revoke(handle, child, parent), to: Native, as: :instance_cascade_revoke

  defdelegate return_endorsed(handle, child, parent, return_conforms),
    to: Native,
    as: :instance_return_endorsed

  defdelegate sentinel_credit_budget(handle, agent, amount),
    to: Native,
    as: :instance_sentinel_credit_budget

  defdelegate grant_override(handle, granter, target, tool, level),
    to: Native,
    as: :instance_grant_override

  defdelegate invoke_start(handle, agent, tool, inv, authorizer_allows, content_gate),
    to: Native,
    as: :instance_invoke_start

  defdelegate invoke_complete(handle, agent, inv, conformance_conforms),
    to: Native,
    as: :instance_invoke_complete

  defdelegate return_unendorsed(handle, child, parent, content_gate),
    to: Native,
    as: :instance_return_unendorsed

  defdelegate sentinel_elevate_taint(handle, agent, level, content_gate),
    to: Native,
    as: :instance_sentinel_elevate_taint

  @doc """
  The `{agent, tools}` the content gate will be queried for, for a gate-consuming action,
  computed over the live state projection. Delegates to the pure `ExArgus.Offline` logic.
  """
  @spec content_gate_targets(t, tuple) :: {id, [id]}
  def content_gate_targets(handle, action),
    do: Offline.content_gate_targets(state(handle), action)

  @doc "Build the `%{tool => boolean}` content-gate map over the live state projection."
  @spec content_gate_map(t, tuple, (id, id -> boolean)) :: %{id => boolean}
  def content_gate_map(handle, action, fun) when is_function(fun, 2),
    do: Offline.content_gate_map(state(handle), action, fun)

  defdelegate explain_invoke(handle, agent, tool, inv, authorizer_allows, content_gate),
    to: Native,
    as: :instance_explain_invoke

  defdelegate explain_return_unendorsed(handle, child, parent, content_gate),
    to: Native,
    as: :instance_explain_return_unendorsed

  defdelegate explain_sentinel_elevate_taint(handle, agent, level, content_gate),
    to: Native,
    as: :instance_explain_sentinel_elevate_taint

  @doc "True if the report's verdict is a denial (delegates to `ExArgus.Explain.denied?/1`)."
  @spec denied?(ExArgus.Explain.report()) :: boolean
  defdelegate denied?(report), to: ExArgus.Explain
end
