defmodule ExArgus.TelemetryTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureLog

  alias ExArgus.{Command, Error, Instance, Native}
  alias ExArgus.Kernel.{Action, Background, Types}

  @event [:ex_argus, :transition]
  @egress [:network_external, :network_internal, :filesystem_write, :ipc]
  @metadata_keys [
    :command,
    :outcome,
    :sequence,
    :reason,
    :verdict,
    :disposition,
    :branch
  ]

  defp background do
    ceiling = Map.new(@egress, &{&1, nil})
    %Background{mode: :enforce, allow_ceiling: ceiling, inspect_ceiling: ceiling}
  end

  @doc false
  def send_event(event, measurements, metadata, test) do
    send(test, {:transition, event, measurements, metadata})
  end

  @doc false
  def raise_event(_event, _measurements, _metadata, _config), do: raise("handler failed")

  defp attach_handler(function \\ &__MODULE__.send_event/4) do
    id = {__MODULE__, self(), make_ref()}
    :ok = :telemetry.attach(id, @event, function, self())
    on_exit(fn -> :telemetry.detach(id) end)
    id
  end

  defp assert_event(expected) do
    assert_receive {:transition, @event, measurements, metadata}
    assert Map.keys(measurements) == [:duration]
    assert is_integer(measurements.duration) and measurements.duration >= 0
    assert Enum.sort(Map.keys(metadata)) == Enum.sort(@metadata_keys)
    assert Map.take(metadata, Map.keys(expected)) == expected
    metadata
  end

  test "accepted attempt emits exactly one bounded content-free event" do
    attach_handler()
    assert {:ok, instance} = Instance.new(background())
    sensitive = "sensitive-tool-identity"

    assert {:ok, _} = Instance.register_tool(instance, sensitive)

    metadata =
      assert_event(%{
        command: :register_tool,
        outcome: :accepted,
        sequence: 1,
        reason: nil,
        verdict: nil,
        disposition: nil,
        branch: nil
      })

    refute inspect(metadata) =~ sensitive
    refute_receive {:transition, _, _, _}
  end

  test "kernel, malformed, and command-capacity refusals each emit once" do
    attach_handler()
    assert {:ok, instance} = Instance.new(background())
    assert {:ok, _} = Instance.register_tool(instance, "tool")
    assert_event(%{outcome: :accepted})

    assert {:error, %Error{class: :kernel, reason: :tool_already_registered}} =
             Instance.register_tool(instance, "tool")

    assert_event(%{
      command: :register_tool,
      outcome: :kernel_refused,
      sequence: nil,
      reason: :tool_already_registered
    })

    assert {:error, %Error{class: :boundary, reason: :invalid_utf8}} =
             Instance.register_tool(instance, <<0xFF>>)

    assert_event(%{
      command: :register_tool,
      outcome: :boundary_refused,
      sequence: nil,
      reason: :invalid_utf8
    })

    oversized_policy = %Types.ActionPolicySnapshot{
      tool: "tool",
      required_caps: List.duplicate(:ipc, 16),
      conf_clearance: :restricted,
      integ_floor: :untrusted,
      integ_inspect: :untrusted,
      output_conf: :public,
      output_integ: :attested,
      declared_egress: [],
      policy_digest: "policy"
    }

    command = %Command.BeginInvocation{
      agent: "agent",
      inv: "invocation",
      challenge: "challenge",
      policy: oversized_policy,
      egress: [],
      args_hash: "arguments",
      authorized: true
    }

    assert {:error, %Error{class: :boundary, reason: :capacity_exceeded}} =
             Instance.begin_invocation(instance, command)

    assert_event(%{
      command: :begin_invocation,
      outcome: :boundary_refused,
      sequence: nil,
      reason: :capacity_exceeded
    })

    refute_receive {:transition, _, _, _}
  end

  test "improper set input returns one typed boundary refusal event" do
    attach_handler()
    assert {:ok, instance} = Instance.new(background())

    policy = %Types.ActionPolicySnapshot{
      tool: "tool",
      required_caps: [],
      conf_clearance: :restricted,
      integ_floor: :untrusted,
      integ_inspect: :untrusted,
      output_conf: :public,
      output_integ: :attested,
      declared_egress: [],
      policy_digest: "policy"
    }

    command = %Command.BeginInvocation{
      agent: "agent",
      inv: "invocation",
      challenge: "challenge",
      policy: policy,
      egress: [:ipc | :improper],
      args_hash: "arguments",
      authorized: true
    }

    assert {:error, %Error{class: :boundary, reason: :invalid_type, path: [:egress]}} =
             Instance.begin_invocation(instance, command)

    assert_event(%{
      command: :begin_invocation,
      outcome: :boundary_refused,
      sequence: nil,
      reason: :invalid_type
    })

    refute_receive {:transition, _, _, %{outcome: :internal_error}}
    refute_receive {:transition, _, _, _}
  end

  test "computed action projection exposes only verdict, disposition, and branch" do
    assert {:ok, instance} = Instance.new(background())
    assert {:ok, _} = Instance.register_tool(instance, "tool")
    assert {:ok, _} = Instance.delegate(instance, "root", "agent")
    attach_handler()

    policy = %Types.ActionPolicySnapshot{
      tool: "tool",
      required_caps: [],
      conf_clearance: :restricted,
      integ_floor: :untrusted,
      integ_inspect: :untrusted,
      output_conf: :public,
      output_integ: :attested,
      declared_egress: [],
      policy_digest: "policy"
    }

    command = %Command.BeginInvocation{
      agent: "agent",
      inv: "invocation",
      challenge: "challenge",
      policy: policy,
      egress: [],
      args_hash: "arguments",
      authorized: true
    }

    assert {:ok, _} = Instance.begin_invocation(instance, command)

    assert_event(%{
      command: :begin_invocation,
      outcome: :accepted,
      verdict: :allow,
      disposition: nil,
      branch: nil
    })

    assert {:ok, _} =
             Instance.settle_invocation(
               instance,
               %Command.SettleInvocation{
                 inv: "invocation",
                 outcome: :success,
                 resolution: nil
               }
             )

    assert_event(%{
      command: :settle_invocation,
      verdict: nil,
      disposition: :permitted,
      branch: nil
    })

    assert {:ok, _} =
             Instance.ingest(
               instance,
               %Command.Ingest{
                 agent: "agent",
                 src: nil,
                 pconf: :public,
                 pinteg: :untrusted
               }
             )

    assert_event(%{command: :ingest, disposition: :permitted})

    assert {:ok, _} = Instance.delegate(instance, "root", "source")
    assert_event(%{command: :delegate})
    assert {:ok, _} = Instance.delegate(instance, "root", "receiver")
    assert_event(%{command: :delegate})

    cross = %Command.CrossOutput{
      input: %Types.CrossInput{
        src: "source",
        rcv: "receiver",
        crossing: "crossing",
        output_hash: "output",
        descriptor: "descriptor",
        fallback: :fail,
        t_integ: :attested,
        t_conf: :public,
        assignment: "assignment",
        evidence: nil,
        released_conf: :public,
        released_integ: :attested
      }
    }

    assert {:ok, _} = Instance.cross_output(instance, cross)

    assert_event(%{
      command: :cross_output,
      verdict: nil,
      disposition: :permitted,
      branch: :fail
    })
  end

  test "metadata projection rejects non-kernel enum values" do
    assert :error =
             Action.telemetry_projection(%Action.BeginInvocation{
               agent: "agent",
               inv: "invocation",
               tool: "tool",
               verdict: :forged,
               authorized: true
             })
  end

  test "a raising Telemetry handler is detached and cannot alter the fixed result" do
    id = attach_handler(&__MODULE__.raise_event/4)

    assert {:ok, instance} = Instance.new(background())

    capture_log(fn ->
      assert {:ok, %{sequence: 1}} = Instance.register_tool(instance, "tool")
    end)

    assert :telemetry.list_handlers(@event) |> Enum.all?(&(&1.id != id))
    assert {:ok, %{sequence: 1}} = Instance.status(instance)
  end

  test "wrong native resource type emits internal once and re-raises the original exception" do
    attach_handler()
    assert {:ok, recovery} = Native.recovery_new(background())
    forged = %Instance{resource: recovery}

    {exception, stacktrace} =
      try do
        Instance.register_tool(forged, "tool")
        flunk("the forged resource must raise")
      rescue
        exception in ArgumentError -> {exception, __STACKTRACE__}
      end

    assert Exception.message(exception) == "argument error"
    assert [{ExArgus.Native, :instance_apply, _, _} | _] = stacktrace

    assert_event(%{
      command: :register_tool,
      outcome: :internal_error,
      sequence: nil,
      reason: :native_contract_violation,
      verdict: nil,
      disposition: nil,
      branch: nil
    })

    refute_receive {:transition, _, _, _}
  end

  test "quarantine helper emits one settlement event" do
    assert {:ok, instance} = Instance.new(background())
    assert {:ok, _} = Instance.register_tool(instance, "tool")
    assert {:ok, _} = Instance.delegate(instance, "root", "agent")

    policy = %Types.ActionPolicySnapshot{
      tool: "tool",
      required_caps: [],
      conf_clearance: :restricted,
      integ_floor: :untrusted,
      integ_inspect: :untrusted,
      output_conf: :public,
      output_integ: :attested,
      declared_egress: [],
      policy_digest: "policy"
    }

    assert {:ok, _} =
             Instance.begin_invocation(
               instance,
               %Command.BeginInvocation{
                 agent: "agent",
                 inv: "invocation",
                 challenge: "challenge",
                 policy: policy,
                 egress: [],
                 args_hash: "arguments",
                 authorized: true
               }
             )

    assert {:ok, _} =
             Instance.settle_invocation(
               instance,
               %Command.SettleInvocation{
                 inv: "invocation",
                 outcome: :ambiguous,
                 resolution: nil
               }
             )

    attach_handler()

    resolution =
      %Types.ResolutionAttestation{id: "resolution", inv: "invocation", outcome: :success}

    assert {:ok, _} =
             Instance.resolve_quarantine(instance, "invocation", :success, resolution)

    assert_event(%{command: :settle_invocation, outcome: :accepted})
    refute_receive {:transition, _, _, _}
  end

  test "new and lifecycle observations emit no transition event" do
    attach_handler()
    assert {:ok, instance} = Instance.new(background())
    assert {:ok, _} = Instance.status(instance)
    assert {:ok, _} = Instance.state(instance)
    refute_receive {:transition, _, _, _}, 50
  end

  test "every contended transition attempt emits exactly one busy event" do
    assert {:ok, instance} = Instance.new(background())

    for index <- 1..1_000 do
      assert {:ok, _} = Instance.register_tool(instance, "tool-#{index}")
    end

    attach_handler()
    parent = self()

    tasks =
      for index <- 1..48 do
        Task.async(fn ->
          send(parent, {:ready, self()})

          receive do
            :go -> Instance.register_tool(instance, "contended-#{index}")
          end
        end)
      end

    pids =
      for _ <- tasks do
        assert_receive {:ready, pid}
        pid
      end

    Enum.each(pids, &send(&1, :go))
    results = Enum.map(tasks, &Task.await(&1, 5_000))

    events =
      for _ <- tasks do
        assert_receive {:transition, @event, measurements, metadata}, 5_000
        assert Map.keys(measurements) == [:duration]
        assert Enum.sort(Map.keys(metadata)) == Enum.sort(@metadata_keys)
        metadata
      end

    busy_results =
      Enum.count(results, &match?({:error, %Error{class: :boundary, reason: :instance_busy}}, &1))

    busy_events =
      Enum.count(
        events,
        &match?(%{outcome: :boundary_refused, reason: :instance_busy}, &1)
      )

    accepted_results = Enum.count(results, &match?({:ok, _}, &1))

    assert busy_results > 0
    assert busy_events == busy_results
    assert {:ok, %{sequence: sequence}} = Instance.status(instance)
    assert sequence == 1_000 + accepted_results
    refute_receive {:transition, _, _, _}
  end
end
