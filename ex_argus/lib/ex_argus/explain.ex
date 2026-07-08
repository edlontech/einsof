defmodule ExArgus.Explain do
  @moduledoc """
  Read-only diagnosis of the gate-consuming transitions: what the kernel WOULD decide and,
  for every denied (level, egress) pair, the counterfactual rescues that would flip it
  (override grant, policy change, tool relabel, content-gate pass).

  The `verdict` field is the exact `ExArgus.Offline.error_reason/0` the real transition
  returns (`nil` = it would succeed) -- the agreement is enforced by a property suite in
  `argus-explain`. Reports are diagnostics from an UNVERIFIED crate: feed them to
  telemetry and the policy review loop, never back into authorization decisions.
  """

  alias ExArgus.Native

  @type report :: %{
          verdict: ExArgus.Offline.error_reason() | nil,
          missing_caps: [atom],
          findings: [map],
          authorizer_denied: boolean
        }

  defdelegate explain_invoke(
                state,
                bg,
                agent,
                tool,
                inv,
                authorizer_allows,
                content_gate,
                attested_egress
              ),
              to: Native

  defdelegate explain_return_unendorsed(state, bg, child, parent, content_gate), to: Native

  defdelegate explain_sentinel_elevate_taint(state, bg, agent, level, content_gate), to: Native

  @doc "True if the report's verdict is a denial."
  @spec denied?(report) :: boolean
  def denied?(%{verdict: verdict}), do: verdict != nil
end
