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

  test "emit_completed fires [:ex_argus, :flow, :completed] carrying the endorsed flag" do
    handler_id = "telemetry-test-#{System.unique_integer([:positive])}"
    parent = self()

    :telemetry.attach(
      handler_id,
      [:ex_argus, :flow, :completed],
      fn event, measurements, metadata, _ -> send(parent, {event, measurements, metadata}) end,
      nil
    )

    on_exit(fn -> :telemetry.detach(handler_id) end)

    ExArgus.Telemetry.emit_completed({:invoke_complete, "a1", "inv-1", true}, %{tenant: "t1"})

    assert_receive {[:ex_argus, :flow, :completed], %{}, %{endorsed: true, tenant: "t1"}}

    ExArgus.Telemetry.emit_completed({:invoke_complete, "a1", "inv-2", false}, %{tenant: "t1"})

    assert_receive {[:ex_argus, :flow, :completed], %{}, %{endorsed: false, tenant: "t1"}}
  end
end
