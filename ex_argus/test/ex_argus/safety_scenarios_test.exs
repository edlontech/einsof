defmodule ExArgus.SafetyScenariosTest do
  use ExUnit.Case, async: true

  alias ExArgus.{Command, Error, Instance}
  alias ExArgus.Kernel.{Action, Background, Types}

  @egress [:network_external, :network_internal, :filesystem_write, :ipc]

  defp background(mode \\ :enforce, allow \\ nil, inspect \\ nil) do
    %Background{
      mode: mode,
      allow_ceiling: Map.new(@egress, &{&1, allow}),
      inspect_ceiling: Map.new(@egress, &{&1, inspect})
    }
  end

  defp policy(overrides \\ %{}) do
    Map.merge(
      %Types.ActionPolicySnapshot{
        tool: "tool",
        required_caps: [],
        conf_clearance: :restricted,
        integ_floor: :untrusted,
        integ_inspect: :untrusted,
        output_conf: :public,
        output_integ: :attested,
        declared_egress: [],
        policy_digest: "policy"
      },
      overrides
    )
  end

  defp begin_command(inv, overrides \\ %{}) do
    Map.merge(
      %Command.BeginInvocation{
        agent: "agent",
        inv: inv,
        challenge: "challenge-#{inv}",
        policy: policy(),
        egress: [],
        args_hash: "arguments-#{inv}",
        authorized: true
      },
      overrides
    )
  end

  defp prepare_agent(instance, agent \\ "agent") do
    assert {:ok, _} = Instance.delegate(instance, "root", agent)
  end

  defp prepare_tool_agent(instance) do
    assert {:ok, _} = Instance.register_tool(instance, "tool")
    prepare_agent(instance)
  end

  test "enforce denies while monitor records a bypass for the same authorizer decision" do
    command = begin_command("inv", %{authorized: false})

    assert {:ok, enforce} = Instance.new(background(:enforce))
    prepare_tool_agent(enforce)

    assert {:error, %Error{class: :kernel, reason: :authorizer_denied}} =
             Instance.begin_invocation(enforce, command)

    assert {:ok, monitor} = Instance.new(background(:monitor))
    prepare_tool_agent(monitor)

    assert {:ok, %{action: %Action.BeginInvocation{verdict: :deny, authorized: false}}} =
             Instance.begin_invocation(monitor, command)

    assert {:ok, state} = Instance.state(monitor)

    assert Enum.any?(
             state.pending,
             &match?(
               {"inv",
                %Types.PendingInvocation{
                  disposition: :monitor_bypassed,
                  admission: :bypassed
                }},
               &1
             )
           )
  end

  test "confidentiality and integrity gates refuse unsafe invocations without state mutation" do
    assert {:ok, confidential} = Instance.new(background())
    prepare_tool_agent(confidential)

    assert {:ok, _} =
             Instance.ingest(
               confidential,
               %Command.Ingest{
                 agent: "agent",
                 src: nil,
                 pconf: :sensitive,
                 pinteg: :attested
               }
             )

    confidential_command =
      begin_command("conf", %{
        policy:
          policy(%{
            output_conf: :public,
            declared_egress: [:network_external]
          }),
        egress: [:network_external]
      })

    assert {:error, %Error{class: :kernel, reason: :flow_gate_blocked}} =
             Instance.begin_invocation(confidential, confidential_command)

    assert {:ok, state} = Instance.state(confidential)
    assert state.pending == []
    assert state.challenges == []

    assert {:ok, integrity} = Instance.new(background())
    prepare_tool_agent(integrity)

    assert {:ok, _} =
             Instance.ingest(
               integrity,
               %Command.Ingest{
                 agent: "agent",
                 src: nil,
                 pconf: :public,
                 pinteg: :untrusted
               }
             )

    integrity_command =
      begin_command("integ", %{policy: policy(%{integ_floor: :trusted, integ_inspect: :trusted})})

    assert {:error, %Error{class: :kernel, reason: :integrity_floor_denied}} =
             Instance.begin_invocation(integrity, integrity_command)
  end

  test "inspection handles positive, negative, scope mismatch, and one-use evidence" do
    assert {:ok, instance} = Instance.new(background(:enforce, :internal, :sensitive))
    prepare_tool_agent(instance)

    inspection_policy =
      policy(%{output_conf: :sensitive, declared_egress: [:network_external]})

    first =
      begin_command("first", %{
        policy: inspection_policy,
        egress: [:network_external]
      })

    assert {:ok, %{action: %Action.BeginInvocation{verdict: :inspection_required}}} =
             Instance.begin_invocation(instance, first)

    mismatched = %Types.InspectionAttestation{
      id: "scope",
      inv: "first",
      challenge: "wrong",
      args_hash: "arguments-first",
      policy_digest: "policy",
      positive: true
    }

    assert {:error, %Error{class: :kernel, reason: :challenge_scope_mismatch}} =
             Instance.authorize_inspected(
               instance,
               %Command.AuthorizeInspected{inv: "first", attestation: mismatched}
             )

    positive = %Types.InspectionAttestation{mismatched | challenge: "challenge-first"}

    assert {:ok, %{action: %Action.AuthorizeInspected{admitted: true}}} =
             Instance.authorize_inspected(
               instance,
               %Command.AuthorizeInspected{inv: "first", attestation: positive}
             )

    second =
      begin_command("second", %{
        policy: inspection_policy,
        egress: [:network_external]
      })

    assert {:ok, _} = Instance.begin_invocation(instance, second)

    reused = %Types.InspectionAttestation{
      positive
      | inv: "second",
        challenge: "challenge-second",
        args_hash: "arguments-second"
    }

    assert {:error, %Error{class: :kernel, reason: :attestation_consumed}} =
             Instance.authorize_inspected(
               instance,
               %Command.AuthorizeInspected{inv: "second", attestation: reused}
             )

    negative = %Types.InspectionAttestation{reused | id: "negative", positive: false}

    assert {:ok, %{action: %Action.AuthorizeInspected{admitted: false}}} =
             Instance.authorize_inspected(
               instance,
               %Command.AuthorizeInspected{inv: "second", attestation: negative}
             )

    assert {:ok, state} = Instance.state(instance)
    refute Enum.any?(state.challenges, &match?({"second", _}, &1))
    refute Enum.any?(state.pending, &match?({"second", _}, &1))
    assert "scope" in state.consumed_attestations
    assert "negative" in state.consumed_attestations
  end

  test "ambiguous settlement quarantines until one scoped resolution" do
    assert {:ok, instance} = Instance.new(background())
    prepare_tool_agent(instance)
    assert {:ok, _} = Instance.begin_invocation(instance, begin_command("invocation"))

    assert {:ok, %{action: %Action.SettleInvocation{outcome: :ambiguous, resolution: nil}}} =
             Instance.settle_invocation(
               instance,
               %Command.SettleInvocation{
                 inv: "invocation",
                 outcome: :ambiguous,
                 resolution: nil
               }
             )

    assert {:ok, state} = Instance.state(instance)

    assert Enum.any?(
             state.pending,
             &match?({"invocation", %Types.PendingInvocation{quarantined: true}}, &1)
           )

    resolution =
      %Types.ResolutionAttestation{id: "resolution", inv: "invocation", outcome: :failure}

    assert {:ok, %{action: %Action.SettleInvocation{outcome: :failure}}} =
             Instance.resolve_quarantine(instance, "invocation", :failure, resolution)

    assert {:ok, state} = Instance.state(instance)
    refute Enum.any?(state.pending, &match?({"invocation", _}, &1))
    assert "resolution" in state.consumed_attestations

    assert {:error, %Error{class: :kernel, reason: :not_pending}} =
             Instance.resolve_quarantine(instance, "invocation", :failure, resolution)
  end

  test "crossing commits endorsed, unendorsed, and fail branches with grant accounting" do
    assert {:ok, endorsed} = Instance.new(background())
    prepare_agent(endorsed, "source")
    prepare_agent(endorsed, "receiver")

    assert {:ok, _} =
             Instance.grant_crossing(endorsed, "root", "receiver", "assignment", 2)

    evidence = %Types.ConformanceAttestation{
      id: "evidence",
      output: "output",
      src: "source",
      rcv: "receiver",
      descriptor: "descriptor",
      assignment: "assignment",
      positive: true
    }

    assert {:ok, %{action: %Action.CrossOutput{branch: :endorsed}}} =
             Instance.cross_output(
               endorsed,
               cross_command("endorsed", :fail, evidence)
             )

    assert {:ok, state} = Instance.state(endorsed)

    assert {{"receiver", "assignment"}, %Types.CrossingGrant{remaining: 1, provisioned: 2}} in state.crossing_grants

    assert "evidence" in state.consumed_attestations

    assert {:ok, exhausted} = Instance.new(background())
    prepare_agent(exhausted, "source")
    prepare_agent(exhausted, "receiver")
    assert {:ok, _} = Instance.grant_crossing(exhausted, "root", "receiver", "assignment", 0)

    assert {:ok, %{action: %Action.CrossOutput{branch: :unendorsed}}} =
             Instance.cross_output(
               exhausted,
               cross_command("unendorsed", :release_unendorsed, evidence)
             )

    assert {:ok, failed} = Instance.new(background())
    prepare_agent(failed, "source")
    prepare_agent(failed, "receiver")

    assert {:ok, %{action: %Action.CrossOutput{branch: :fail}}} =
             Instance.cross_output(failed, cross_command("failed", :fail, nil))

    assert {:ok, state} = Instance.state(failed)
    assert "failed" in state.consumed_crossings
    assert state.taint_levels == []
    assert state.integ_levels == []
  end

  defp cross_command(crossing, fallback, evidence) do
    %Command.CrossOutput{
      input: %Types.CrossInput{
        src: "source",
        rcv: "receiver",
        crossing: crossing,
        output_hash: "output",
        descriptor: "descriptor",
        fallback: fallback,
        t_integ: :attested,
        t_conf: :public,
        assignment: "assignment",
        evidence: evidence,
        released_conf: :public,
        released_integ: :attested
      }
    }
  end
end
