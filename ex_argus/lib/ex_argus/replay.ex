defmodule ExArgus.Replay do
  @moduledoc """
  Offline trajectory replay of a recorded kernel-call log against an arbitrary
  background. An entry is `{fun, args}` where the live call was
  `apply(ExArgus.Offline, fun, [state, bg | args])` -- args include the recorded oracle
  verdicts, so the replay re-decides ONLY the policy, not the oracles.

  On an error outcome the state is left unchanged and the replay continues, mirroring
  how a live adapter retains its state when the kernel refuses a transition.
  """

  alias ExArgus.Offline

  @type entry :: {atom, [term]}
  @type divergence :: %{
          index: non_neg_integer,
          entry: entry,
          live: Offline.outcome(),
          candidate: Offline.outcome()
        }

  @doc """
  Replay the log from the initial state; returns the outcome of every entry, in order.

  The log must begin with `ExArgus.log_header/0`, checked BEFORE any entry replays -- a
  missing or mismatched header returns `{:error, :state_version_mismatch}` without
  replaying anything.
  """
  @spec run([entry], Offline.background()) ::
          {:error, :state_version_mismatch} | [Offline.outcome()]
  def run(log, bg) do
    case ExArgus.strip_log_header(log) do
      {:ok, entries} -> run_entries(entries, bg)
      :error -> {:error, :state_version_mismatch}
    end
  end

  defp run_entries(entries, bg) do
    {outcomes, _state} =
      Enum.reduce(entries, {[], Offline.initial_state()}, fn {fun, args}, {acc, state} ->
        case apply(Offline, fun, [state, bg | args]) do
          {:ok, new_state, _action} = ok -> {[ok | acc], new_state}
          {:error, _reason} = err -> {[err | acc], state}
        end
      end)

    Enum.reverse(outcomes)
  end

  @doc """
  Replay the log against both backgrounds and report every entry whose decision differs.
  Entries where both sides return equal ok-actions or equal error-reasons are omitted.

  The log must begin with `ExArgus.log_header/0`; see `run/2`.
  """
  @spec diff([entry], Offline.background(), Offline.background()) ::
          {:error, :state_version_mismatch} | [divergence]
  def diff(log, live_bg, candidate_bg) do
    case ExArgus.strip_log_header(log) do
      {:ok, entries} ->
        live = run_entries(entries, live_bg)
        candidate = run_entries(entries, candidate_bg)

        [entries, live, candidate, 0..(length(entries) - 1)]
        |> Enum.zip()
        |> Enum.reject(fn {_entry, l, c, _i} -> same_decision?(l, c) end)
        |> Enum.map(fn {entry, l, c, i} ->
          %{index: i, entry: entry, live: l, candidate: c}
        end)

      :error ->
        {:error, :state_version_mismatch}
    end
  end

  defp same_decision?({:ok, _, action}, {:ok, _, action}), do: true
  defp same_decision?({:error, reason}, {:error, reason}), do: true
  defp same_decision?(_, _), do: false
end
