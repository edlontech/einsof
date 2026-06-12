defmodule ExArgus.TelemetryTest do
  use ExUnit.Case, async: false

  test "emit_denied fires [:ex_argus, :flow, :denied] with the report attached" do
    handler_id = "telemetry-test-#{System.unique_integer([:positive])}"
    parent = self()

    :telemetry.attach(
      handler_id,
      [:ex_argus, :flow, :denied],
      fn event, measurements, metadata, _ -> send(parent, {event, measurements, metadata}) end,
      nil
    )

    on_exit(fn -> :telemetry.detach(handler_id) end)

    report = %{
      verdict: :flow_gate_blocked,
      findings: [%{outcome: :denied}],
      missing_caps: [],
      authorizer_denied: false
    }

    ExArgus.Telemetry.emit_denied(report, %{tenant: "t1"})

    assert_receive {[:ex_argus, :flow, :denied], %{findings: 1}, %{report: ^report, tenant: "t1"}}
  end

  test "emit_denied is a no-op for a success report" do
    report = %{verdict: nil, findings: [], missing_caps: [], authorizer_denied: false}
    assert :ok = ExArgus.Telemetry.emit_denied(report, %{})
  end
end
