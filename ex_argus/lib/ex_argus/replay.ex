defmodule ExArgus.Replay do
  @moduledoc """
  Offline trajectory replay of a recorded kernel-call log against an arbitrary
  background. An entry is `{fun, args}` where the live call was
  `apply(ExArgus.Kernel, fun, [state, bg | args])` -- args include the recorded oracle
  verdicts, so the replay re-decides ONLY the policy, not the oracles.

  On an error outcome the state is left unchanged and the replay continues, mirroring
  how a live adapter retains its state when the kernel refuses a transition.
  """

  alias ExArgus.Kernel

  @type entry :: {atom, [term]}
  @type divergence :: %{
          index: non_neg_integer,
          entry: entry,
          live: Kernel.outcome(),
          candidate: Kernel.outcome()
        }

  @doc "Replay the log from the initial state; returns the outcome of every entry, in order."
  @spec run([entry], Kernel.background()) :: [Kernel.outcome()]
  def run(log, bg) do
    {outcomes, _state} =
      Enum.reduce(log, {[], Kernel.initial_state()}, fn {fun, args}, {acc, state} ->
        case apply(Kernel, fun, [state, bg | args]) do
          {:ok, new_state, _action} = ok -> {[ok | acc], new_state}
          {:error, _reason} = err -> {[err | acc], state}
        end
      end)

    Enum.reverse(outcomes)
  end

  @doc """
  Replay the log against both backgrounds and report every entry whose decision differs.
  Entries where both sides return equal ok-actions or equal error-reasons are omitted.
  """
  @spec diff([entry], Kernel.background(), Kernel.background()) :: [divergence]
  def diff(log, live_bg, candidate_bg) do
    live = run(log, live_bg)
    candidate = run(log, candidate_bg)

    [log, live, candidate, 0..(length(log) - 1)]
    |> Enum.zip()
    |> Enum.reject(fn {_entry, l, c, _i} -> same_decision?(l, c) end)
    |> Enum.map(fn {entry, l, c, i} ->
      %{index: i, entry: entry, live: l, candidate: c}
    end)
  end

  defp same_decision?({:ok, _, action}, {:ok, _, action}), do: true
  defp same_decision?({:error, reason}, {:error, reason}), do: true
  defp same_decision?(_, _), do: false
end
