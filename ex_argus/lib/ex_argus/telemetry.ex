defmodule ExArgus.Telemetry do
  @moduledoc false

  @event [:ex_argus, :transition]
  @commands [
    :register_tool,
    :unregister_tool,
    :delegate,
    :grant_capability,
    :grant_crossing,
    :revoke,
    :cascade_revoke,
    :ingest,
    :begin_invocation,
    :authorize_inspected,
    :settle_invocation,
    :cross_output
  ]
  @outcomes [:accepted, :kernel_refused, :boundary_refused, :internal_error]

  @doc false
  @spec emit_transition(
          atom(),
          atom(),
          non_neg_integer(),
          non_neg_integer() | nil,
          atom() | nil,
          %{verdict: atom() | nil, disposition: atom() | nil, branch: atom() | nil}
        ) :: :ok
  def emit_transition(command, outcome, duration, sequence, reason, projection)
      when command in @commands and outcome in @outcomes and is_integer(duration) and
             duration >= 0 do
    :telemetry.execute(
      @event,
      %{duration: duration},
      %{
        command: command,
        outcome: outcome,
        sequence: sequence,
        reason: reason,
        verdict: projection.verdict,
        disposition: projection.disposition,
        branch: projection.branch
      }
    )
  end
end
