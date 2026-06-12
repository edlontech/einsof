defmodule ExArgus.Telemetry do
  @moduledoc """
  Telemetry emission for kernel denials. The adapter calls `emit_denied/2` with an
  `ExArgus.Explain` report whenever a transition returns an error; downstream aggregation
  (the weekly policy-review loop) attaches to `[:ex_argus, :flow, :denied]`.
  """

  @flow_denied [:ex_argus, :flow, :denied]

  @doc """
  Emit `[:ex_argus, :flow, :denied]` for a denied explain report. Success reports
  (`verdict: nil`) are ignored, so callers can emit unconditionally.
  """
  @spec emit_denied(ExArgus.Explain.report(), map) :: :ok
  def emit_denied(%{verdict: nil}, _metadata), do: :ok

  def emit_denied(%{findings: findings} = report, metadata) when is_map(metadata) do
    :telemetry.execute(
      @flow_denied,
      %{findings: length(findings)},
      Map.put(metadata, :report, report)
    )
  end
end
