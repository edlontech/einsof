defmodule ExArgus.Shadow do
  @moduledoc """
  Decision-level shadow evaluation: run one kernel transition against the live and a
  candidate `ExArgus.Kernel.Background`, and compare the DECISIONS (ok/error reason).
  The caller always proceeds with `result.live`; the comparison is evidence for the
  policy-review loop.

  This deliberately does not maintain a forked candidate trajectory -- both runs see the
  same (live) state, so a divergence means "the candidate policy decides this call
  differently on the live trajectory". Trajectory-level confidence comes from
  `ExArgus.Replay` over a recorded log.
  """

  alias ExArgus.Offline

  @type comparison :: %{
          live: Offline.outcome(),
          candidate: Offline.outcome(),
          decision: :same | :diverged
        }

  @doc """
  Run `fun` (a one-argument closure over a background) against both backgrounds.

      Shadow.compare(live_bg, candidate_bg, fn bg ->
        Offline.invoke_start(state, bg, agent, tool, inv, auth, gate_map)
      end)
  """
  @spec compare(
          Offline.background(),
          Offline.background(),
          (Offline.background() -> Offline.outcome())
        ) :: comparison
  def compare(live_bg, candidate_bg, fun) when is_function(fun, 1) do
    live = fun.(live_bg)
    candidate = fun.(candidate_bg)
    %{live: live, candidate: candidate, decision: decision(live, candidate)}
  end

  defp decision({:ok, _, action}, {:ok, _, action}), do: :same
  defp decision({:error, reason}, {:error, reason}), do: :same
  defp decision(_, _), do: :diverged
end
