defmodule ExArgus.Shadow.Instance do
  @moduledoc """
  A live `ExArgus.Instance` trajectory with a candidate background bound alongside the
  live one, for shadow replay at O(entry) NIF cost (Policy Lab approach B).

  `new/2` binds BOTH backgrounds once into the NIF resource. Each `apply/3` evaluates the
  candidate against the PRE-entry state, applies the entry under the live background, and
  returns `%{live: outcome, candidate: verdict, report: report | nil}`:

    * `live` -- `{:ok, seq, action}` or `{:error, reason}`, identical to `ExArgus.Instance`
      semantics: commits on success, leaves state untouched on refusal.
    * `candidate` -- `:allow` or `{:deny, reason}`, the verdict the same transition would
      get under the candidate background at the same pre-entry state. The candidate never
      advances state ("same state, both policies"), so it carries no seq/action.
    * `report` -- an `ExArgus.Explain.report/0` computed under the CANDIDATE background,
      present exactly when the two decisions differ AND the transition is one of the six
      explain-capable policy-sensitive ones (`invoke_start`, `return_unendorsed`,
      `sentinel_elevate_taint`, `sentinel_degrade_integrity`, `return_endorsed`,
      `grant_override`). Transitions without explain machinery (notably `register_tool` /
      `load_instruction`, which can still flip on `trusted_issuers`) report divergence via
      the `candidate` verdict alone.

  State never crosses the NIF boundary: the candidate transition runs in Rust on a clone
  of the pre-entry state and is discarded. Every transition evaluates the candidate --
  including the ones the flow gates never touch -- because issuer-consulting transitions
  are ceiling-insensitive but NOT issuer-insensitive.
  """

  import Kernel, except: [apply: 3]

  alias ExArgus.Kernel.State
  alias ExArgus.{Explain, Native, Offline}

  @type t :: reference()
  @type background :: ExArgus.Kernel.Background.t()
  @type id :: String.t()
  @type live_outcome :: {:ok, non_neg_integer, tuple} | {:error, Offline.error_reason()}
  @type candidate_verdict :: :allow | {:deny, Offline.error_reason()}
  @type outcome :: %{
          live: live_outcome,
          candidate: candidate_verdict,
          report: Explain.report() | nil
        }

  @transitions ~w(
    register_tool unregister_tool load_instruction delegate grant_capability revoke
    cascade_revoke return_endorsed sentinel_credit_budget grant_override invoke_start
    invoke_complete return_unendorsed sentinel_elevate_taint sentinel_degrade_integrity
  )a

  @doc "Create a fresh shadow instance at the initial state, with both backgrounds bound."
  @spec new(background, background) :: t
  defdelegate new(live_bg, candidate_bg), to: Native, as: :shadow_new

  @doc "Read-only snapshot of the live-side state (the candidate never advances it)."
  @spec state(t) :: State.t()
  defdelegate state(handle), to: Native, as: :shadow_state

  @doc "The monotone count of transitions ACCEPTED on the live side."
  @spec seq(t) :: non_neg_integer
  defdelegate seq(handle), to: Native, as: :shadow_seq

  @doc """
  Apply one recorded `{fun, args}` entry: candidate verdict against the pre-entry state,
  then the live transition. `fun` must be one of the 15 kernel transitions; anything else
  returns `{:error, :unknown_transition}` without touching the instance.
  """
  @spec apply(t, atom, [term]) :: outcome | {:error, :unknown_transition}
  def apply(handle, fun, args) when fun in @transitions,
    do: Kernel.apply(__MODULE__, fun, [handle | args])

  def apply(_handle, _fun, _args), do: {:error, :unknown_transition}

  @typedoc "A recorded kernel-call log entry, identical to `ExArgus.Replay.entry/0`."
  @type entry :: {atom, [term]}
  @type recovery_error :: %{
          index: non_neg_integer,
          entry: term,
          reason: Offline.error_reason() | :unknown_transition
        }

  @doc """
  Rebuild a shadow instance by replaying a recorded log from the initial state, applying
  each entry through `apply/3` under the LIVE background (candidate verdicts along the
  prefix are computed and discarded). Same strictness as `ExArgus.Instance.recover/2`:
  the log must begin with `ExArgus.log_header/0`, and a live-side refusal aborts with the
  offending index/entry/reason and returns no instance.
  """
  @spec recover(background, background, [entry]) :: {:ok, t} | {:error, recovery_error}
  def recover(live_bg, candidate_bg, log) do
    case ExArgus.strip_log_header(log) do
      {:ok, entries} ->
        recover_entries(live_bg, candidate_bg, entries)

      :error ->
        {:error, %{index: 0, entry: List.first(log), reason: :state_version_mismatch}}
    end
  end

  defp recover_entries(live_bg, candidate_bg, entries) do
    handle = new(live_bg, candidate_bg)

    result =
      entries
      |> Enum.with_index()
      |> Enum.reduce_while(:ok, fn {{fun, args}, i}, :ok ->
        case apply(handle, fun, args) do
          %{live: {:ok, _seq, _action}} ->
            {:cont, :ok}

          %{live: {:error, reason}} ->
            {:halt, {:error, %{index: i, entry: {fun, args}, reason: reason}}}

          {:error, :unknown_transition} ->
            {:halt, {:error, %{index: i, entry: {fun, args}, reason: :unknown_transition}}}
        end
      end)

    case result do
      :ok -> {:ok, handle}
      {:error, _} = error -> error
    end
  end

  defdelegate register_tool(handle, tool), to: Native, as: :shadow_register_tool
  defdelegate unregister_tool(handle, tool), to: Native, as: :shadow_unregister_tool
  defdelegate load_instruction(handle, agent, instr), to: Native, as: :shadow_load_instruction
  defdelegate delegate(handle, grantor, grantee), to: Native, as: :shadow_delegate

  defdelegate grant_capability(handle, parent, child, cap),
    to: Native,
    as: :shadow_grant_capability

  defdelegate revoke(handle, parent, target), to: Native, as: :shadow_revoke
  defdelegate cascade_revoke(handle, child, parent), to: Native, as: :shadow_cascade_revoke

  defdelegate return_endorsed(handle, child, parent, return_conforms, clvl, ilvl),
    to: Native,
    as: :shadow_return_endorsed

  defdelegate sentinel_credit_budget(handle, agent, amount),
    to: Native,
    as: :shadow_sentinel_credit_budget

  defdelegate grant_override(handle, granter, target, tool, level),
    to: Native,
    as: :shadow_grant_override

  defdelegate invoke_start(
                handle,
                agent,
                tool,
                inv,
                authorizer_allows,
                content_gate,
                attested_egress
              ),
              to: Native,
              as: :shadow_invoke_start

  defdelegate invoke_complete(handle, agent, inv, conformance_conforms),
    to: Native,
    as: :shadow_invoke_complete

  defdelegate return_unendorsed(handle, child, parent, content_gate),
    to: Native,
    as: :shadow_return_unendorsed

  defdelegate sentinel_elevate_taint(handle, agent, level, content_gate),
    to: Native,
    as: :shadow_sentinel_elevate_taint

  defdelegate sentinel_degrade_integrity(handle, agent, level, content_gate),
    to: Native,
    as: :shadow_sentinel_degrade_integrity
end
