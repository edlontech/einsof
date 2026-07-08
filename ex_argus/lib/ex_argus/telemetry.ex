defmodule ExArgus.Telemetry do
  @moduledoc """
  Telemetry emission for kernel denials and completions. The adapter calls `emit_denied/2`
  with an `ExArgus.Explain` report whenever a transition returns an error, and
  `emit_completed/2` with the accepted `invoke_complete` action; downstream aggregation
  (the weekly policy-review loop) attaches to `[:ex_argus, :flow, :denied]` and
  `[:ex_argus, :flow, :completed]`.
  """

  @flow_denied [:ex_argus, :flow, :denied]
  @flow_completed [:ex_argus, :flow, :completed]

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

  @doc """
  Emit `[:ex_argus, :flow, :completed]` for an accepted `invoke_complete` action, carrying
  the `endorsed` flag in the metadata so the policy-review loop can distinguish endorsed
  from unendorsed completions.
  """
  @spec emit_completed(tuple, map) :: :ok
  def emit_completed({:invoke_complete, _agent, _inv, endorsed}, metadata)
      when is_map(metadata) do
    :telemetry.execute(@flow_completed, %{}, Map.put(metadata, :endorsed, endorsed))
  end
end
