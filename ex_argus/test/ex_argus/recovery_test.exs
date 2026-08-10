defmodule ExArgus.RecoveryTest do
  use ExUnit.Case, async: false

  alias ExArgus.{Chain, Command, Envelope, Error, Instance, Limits, Native, Validation}
  alias ExArgus.Kernel.{Action, Background, Types}

  @egress [:network_external, :network_internal, :filesystem_write, :ipc]

  defp background do
    ceiling = Map.new(@egress, &{&1, nil})
    %Background{mode: :enforce, allow_ceiling: ceiling, inspect_ceiling: ceiling}
  end

  @doc false
  def send_recovery_event(event, measurements, metadata, test) do
    send(test, {:transition, event, measurements, metadata})
  end

  test "recovers an empty history from its genesis anchor" do
    assert {:ok, original} = Instance.new(background())
    assert {:ok, genesis} = Instance.status(original)

    assert {:ok, recovered} = Instance.recover(background(), [], genesis)
    assert Instance.status(recovered) == {:ok, genesis}
    assert Instance.state(recovered) == Instance.state(original)
    assert %Chain{version: 5, sequence: 0} = genesis

    assert {:error, %Error{class: :recovery, reason: :final_anchor_mismatch, index: nil}} =
             Instance.recover(background(), [], %{genesis | head: <<0::256>>})
  end

  test "recovers every accepted prefix with exact state, status, and normalized sets" do
    assert {:ok, original} = Instance.new(background())

    commands = [
      fn -> Instance.register_tool(original, "tool") end,
      fn -> Instance.delegate(original, "root", "agent") end,
      fn -> Instance.grant_capability(original, "root", "agent", :ipc) end,
      fn -> Instance.grant_capability(original, "root", "agent", :filesystem_read) end,
      fn -> Instance.begin_invocation(original, begin_command()) end,
      fn ->
        Instance.settle_invocation(
          original,
          %Command.SettleInvocation{inv: "invocation", outcome: :success, resolution: nil}
        )
      end
    ]

    {_history, checkpoints} =
      Enum.reduce(commands, {[], []}, fn call, {history, checkpoints} ->
        assert {:ok, envelope} = call.()
        next_history = history ++ [envelope]
        assert {:ok, status} = Instance.status(original)
        assert {:ok, state} = Instance.state(original)
        {next_history, checkpoints ++ [{next_history, status, state}]}
      end)

    for {history, status, state} <- checkpoints do
      assert {:ok, recovered} = Instance.recover(background(), history, status)
      assert Instance.status(recovered) == {:ok, status}
      assert Instance.state(recovered) == {:ok, state}
    end

    {history, _status, _state} = List.last(checkpoints)
    begin_envelope = Enum.at(history, 4)
    assert begin_envelope.command.policy.required_caps == [:filesystem_read, :ipc]
  end

  test "rejects chain corruption and replay refusal at the exact link" do
    {history, %Chain{} = anchor, _state} = accepted_history()
    [first, second, third] = history

    cases = [
      {[Map.put(first, :sequence, 2) | tl(history)], anchor, :sequence_mismatch, 0, nil},
      {[first, Map.put(second, :previous_digest, <<0::256>>), third], anchor,
       :previous_digest_mismatch, 1, nil},
      {[Map.put(first, :action, %Action.RegisterTool{tool: "edited"}) | tl(history)], anchor,
       :action_mismatch, 0, nil},
      {[first, second, Map.put(third, :digest, <<1::256>>)], %Chain{anchor | head: <<1::256>>},
       :digest_mismatch, 2, nil},
      {[first, %{second | command: %Command.RegisterTool{tool: "tool"}}, third], anchor,
       :replay_refused, 1, :tool_already_registered}
    ]

    for {corrupt, expected, reason, index, cause} <- cases do
      assert {:error,
              %Error{
                class: :recovery,
                reason: ^reason,
                index: ^index,
                cause: ^cause
              }} = Instance.recover(background(), corrupt, expected)
    end
  end

  test "rejects edit, insertion, deletion, reorder, duplicate, and gap before exposure" do
    {history, %Chain{} = anchor, _state} = accepted_history()
    [first, second, third] = history

    corruptions = [
      {[first, second, %{third | command: %Command.RegisterTool{tool: "tool"}}], :replay_refused,
       2},
      {[first, second, second, third], :sequence_mismatch, 2},
      {[first, third], :sequence_mismatch, 1},
      {[second, first, third], :sequence_mismatch, 0},
      {[first, first, second, third], :sequence_mismatch, 1},
      {[first, %{second | sequence: 3}, third], :sequence_mismatch, 1}
    ]

    for {corrupt, reason, index} <- corruptions do
      expected =
        if length(corrupt) == anchor.sequence,
          do: anchor,
          else: %Chain{anchor | sequence: length(corrupt)}

      assert {:error, %Error{class: :recovery, reason: ^reason, index: ^index}} =
               Instance.recover(background(), corrupt, expected)
    end
  end

  test "malformed recovery terms stay closed with exact index and path" do
    {[first, second, third], %Chain{} = anchor, _state} = accepted_history()

    assert {:error, %Error{class: :boundary, reason: :invalid_struct, path: [], index: nil}} =
             Instance.recover(nil, [first, second, third], anchor)

    assert {:error, %Error{class: :boundary, reason: :invalid_keys, path: [], index: nil}} =
             Instance.recover(
               Map.put(background(), :forged, true),
               [first, second, third],
               anchor
             )

    malformed_histories = [
      {nil, :invalid_type, [], 0},
      {[Map.put(first, :forged, true), second, third], :invalid_keys, [], 0},
      {[Map.delete(first, :digest), second, third], :invalid_keys, [], 0},
      {[%{first | digest: <<0>>}, second, third], :invalid_type, [:digest], 0},
      {[%{first | command: Map.put(first.command, :forged, true)}, second, third], :invalid_keys,
       [:command], 0},
      {[%{first | action: Map.put(first.action, :forged, true)}, second, third], :invalid_keys,
       [:action], 0},
      {[first | :improper], :invalid_type, [], 1}
    ]

    for {history, reason, path, index} <- malformed_histories do
      assert {:error, %Error{class: :boundary, reason: ^reason, path: ^path, index: ^index}} =
               Instance.recover(background(), history, anchor)
    end

    assert {:error, %Error{class: :recovery, reason: :invalid_version, index: 0}} =
             Instance.recover(background(), [%{first | version: 4}, second, third], anchor)

    malformed_anchors = [
      {nil, :invalid_struct, []},
      {Map.put(anchor, :forged, true), :invalid_keys, []},
      {Map.delete(anchor, :head), :invalid_keys, []},
      {%{anchor | sequence: -1}, :integer_out_of_range, [:sequence]},
      {%{anchor | head: <<0>>}, :invalid_type, [:head]}
    ]

    for {expected, reason, path} <- malformed_anchors do
      assert {:error, %Error{class: :boundary, reason: ^reason, path: ^path, index: nil}} =
               Instance.recover(background(), [first, second, third], expected)
    end

    assert {:error, %Error{class: :recovery, reason: :invalid_version, index: nil}} =
             Instance.recover(background(), [first, second, third], %{anchor | version: 4})
  end

  test "ordinary malformed terms never raise during recovery validation" do
    {_history, %Chain{} = anchor, _state} = accepted_history()

    ordinary_terms = [nil, 1, 1.0, :atom, "binary", {}, {1, 2}, %{}, [1], [nil | :tail]]

    for background <- ordinary_terms do
      assert {:error, %Error{}} = Instance.recover(background, [], anchor)
    end

    for history <- ordinary_terms do
      assert {:error, %Error{}} = Instance.recover(background(), history, anchor)
    end

    for expected <- ordinary_terms do
      assert {:error, %Error{}} = Instance.recover(background(), [], expected)
    end
  end

  test "the complete history and anchor validate before native recovery creation" do
    {[first, second, third], %Chain{} = anchor, _state} = accepted_history()
    wrong_background = %Background{background() | mode: :monitor}
    malformed_second = %{second | command: Map.put(second.command, :forged, true)}

    assert {:error,
            %Error{
              class: :boundary,
              reason: :invalid_keys,
              path: [:command],
              index: 1
            }} =
             Instance.recover(wrong_background, [first, malformed_second, third], anchor)

    assert {:error, %Error{class: :boundary, reason: :invalid_type, path: [:head], index: nil}} =
             Instance.recover(wrong_background, [first, second, third], %{anchor | head: <<0>>})
  end

  test "history count and aggregate content use bounded checked arithmetic" do
    maximum_count = Limits.max_recovery_envelopes()
    maximum_content = Limits.max_replay_content_bytes()

    assert :ok = Validation.checked_recovery_count(maximum_count - 1)

    assert {:error, %Error{class: :boundary, reason: :capacity_exceeded, index: ^maximum_count}} =
             Validation.checked_recovery_count(maximum_count)

    assert {:ok, ^maximum_content} =
             Validation.checked_replay_content(maximum_content - 64, 64)

    assert {:error, %Error{class: :boundary, reason: :capacity_exceeded}} =
             Validation.checked_replay_content(maximum_content - 63, 64)

    assert {:error, %Error{class: :boundary, reason: :capacity_exceeded}} =
             Validation.checked_replay_content(maximum_content + 1, 0)

    assert {:error, %Error{class: :boundary, reason: :invalid_type}} =
             Validation.checked_replay_content(:bad, 1)

    {[first | _], _anchor, _state} = accepted_history()
    assert {:ok, 72} = Validation.replay_envelope_content(first)
  end

  test "validates every exact action field and normalizes embedded commands" do
    for {command, action} <- valid_command_actions() do
      envelope = validation_envelope(command, action)
      expected = %Chain{version: 5, sequence: 1, head: envelope.digest}

      assert {:ok, {_background, [normalized], ^expected}} =
               Validation.recovery(background(), [envelope], expected)

      assert normalized.action == action

      for field <- Map.keys(Map.from_struct(action)) do
        {invalid, reason} = invalid_action_field(field)
        malformed = %{envelope | action: Map.put(action, field, invalid)}

        assert {:error,
                %Error{
                  class: :boundary,
                  reason: ^reason,
                  path: [:action, ^field],
                  index: 0
                }} = Validation.recovery(background(), [malformed], expected)
      end

      first_field = action |> Map.from_struct() |> Map.keys() |> hd()

      for malformed <- [Map.put(action, :forged, true), Map.delete(action, first_field)] do
        assert {:error,
                %Error{class: :boundary, reason: :invalid_keys, path: [:action], index: 0}} =
                 Validation.recovery(background(), [%{envelope | action: malformed}], expected)
      end
    end
  end

  test "content metric counts every retained binary repetition and ignores fixed values" do
    pairs = valid_command_actions()
    {begin_command, begin_action} = Enum.at(pairs, 8)
    {cross_command, cross_action} = Enum.at(pairs, 11)

    assert {:ok, 73} =
             Validation.replay_envelope_content(validation_envelope(begin_command, begin_action))

    assert {:ok, 79} =
             Validation.replay_envelope_content(validation_envelope(cross_command, cross_action))
  end

  test "an unnormalized recorded set history recovers to canonical envelope semantics" do
    ceiling = Map.new(@egress, &{&1, :restricted})
    permissive = %Background{mode: :enforce, allow_ceiling: ceiling, inspect_ceiling: ceiling}
    assert {:ok, original} = Instance.new(permissive)

    calls = [
      fn -> Instance.register_tool(original, "tool") end,
      fn -> Instance.delegate(original, "root", "agent") end,
      fn -> Instance.grant_capability(original, "root", "agent", :filesystem_read) end,
      fn -> Instance.grant_capability(original, "root", "agent", :ipc) end,
      fn -> Instance.begin_invocation(original, begin_command_with_egress()) end
    ]

    history =
      Enum.map(calls, fn call ->
        assert {:ok, envelope} = call.()
        envelope
      end)

    assert {:ok, anchor} = Instance.status(original)
    assert {:ok, state} = Instance.state(original)
    begin_envelope = List.last(history)
    %Command.BeginInvocation{} = command = begin_envelope.command
    %Types.ActionPolicySnapshot{} = policy = command.policy

    unnormalized = %{
      begin_envelope
      | command: %Command.BeginInvocation{
          command
          | egress: Enum.reverse(command.egress),
            policy: %Types.ActionPolicySnapshot{
              policy
              | required_caps: Enum.reverse(policy.required_caps),
                declared_egress: Enum.reverse(policy.declared_egress)
            }
        }
    }

    assert {:ok, recovered} =
             Instance.recover(permissive, List.replace_at(history, 4, unnormalized), anchor)

    assert Instance.state(recovered) == {:ok, state}
    assert Instance.status(recovered) == {:ok, anchor}
  end

  test "recovery emits no transition telemetry and has no callback surface" do
    {history, anchor, _state} = accepted_history()
    handler = {__MODULE__, self(), make_ref()}
    test = self()

    :ok =
      :telemetry.attach(
        handler,
        [:ex_argus, :transition],
        &__MODULE__.send_recovery_event/4,
        test
      )

    on_exit(fn -> :telemetry.detach(handler) end)

    assert {:ok, _recovered} = Instance.recover(background(), history, anchor)

    assert {:error, %Error{class: :recovery}} =
             Instance.recover(%Background{background() | mode: :monitor}, history, anchor)

    refute_receive {:transition, _, _, _}, 50
    refute Code.ensure_loaded?(ExArgus.Authorizer)
    refute Code.ensure_loaded?(ExArgus.ContentGate)
    refute Code.ensure_loaded?(ExArgus.Conformance)
  end

  test "no partial recovery handle is public and native finalization consumes exactly once" do
    assert {:ok, original} = Instance.new(background())
    assert {:ok, genesis} = Instance.status(original)
    assert {:ok, recovery} = Native.recovery_new(background())
    assert {:ok, live} = Native.recovery_finalize(recovery, genesis)
    assert {:ok, ^genesis} = Native.instance_status(live)

    assert {:error, :recovery_consumed} = Native.recovery_finalize(recovery, genesis)

    envelope =
      validation_envelope(%Command.RegisterTool{tool: "tool"}, %Action.RegisterTool{tool: "tool"})

    assert {:error, :recovery_consumed} = Native.recovery_replay(recovery, envelope)

    assert_raise ArgumentError, fn -> Native.recovery_replay(live, envelope) end
    assert_raise ArgumentError, fn -> Native.instance_status(recovery) end

    expected = [
      __struct__: 0,
      __struct__: 1,
      new: 1,
      recover: 3,
      state: 1,
      status: 1,
      register_tool: 2,
      unregister_tool: 2,
      delegate: 3,
      grant_capability: 4,
      grant_crossing: 5,
      revoke: 3,
      cascade_revoke: 3,
      ingest: 2,
      begin_invocation: 2,
      authorize_inspected: 2,
      settle_invocation: 2,
      cross_output: 2,
      resolve_quarantine: 4
    ]

    assert Enum.sort(Instance.__info__(:functions)) == Enum.sort(expected)
    refute function_exported?(Instance, :recovery_new, 1)
    refute function_exported?(Instance, :replay, 2)
    refute function_exported?(Instance, :finalize, 2)
  end

  test "maps every closed native recovery result without dynamic atoms or caller content" do
    indexed = [
      :invalid_version,
      :sequence_mismatch,
      :previous_digest_mismatch,
      :action_mismatch,
      :digest_mismatch,
      :recovery_consumed,
      :final_anchor_mismatch
    ]

    for reason <- indexed do
      assert {:error, %Error{class: :recovery, reason: ^reason, index: 2}} =
               Error.from_recovery(reason, 2)
    end

    for cause <- Error.kernel_reasons() do
      assert {:error,
              %Error{
                class: :recovery,
                reason: :replay_refused,
                index: 3,
                cause: ^cause
              }} = Error.from_recovery({:replay_refused, cause}, 3)
    end

    for reason <- [:instance_busy, :capacity_exceeded, :sequence_exhausted] do
      assert {:error, %Error{class: :boundary, reason: ^reason, index: 1}} =
               Error.from_recovery(reason, 1)
    end

    assert {:error, %Error{class: :internal, reason: :resource_poisoned, index: 1}} =
             Error.from_recovery(:resource_poisoned, 1)

    assert {:error, %Error{class: :internal, reason: :native_contract_violation, index: nil}} =
             Error.from_recovery({:replay_refused, :forged}, nil)
  end

  test "rejects wrong background and stale, truncated, future, or wrong-head anchors" do
    {history, %Chain{} = anchor, _state} = accepted_history()
    [first | _] = history
    monitor = %Background{background() | mode: :monitor}

    assert {:error, %Error{class: :recovery, reason: :previous_digest_mismatch, index: 0}} =
             Instance.recover(monitor, history, anchor)

    for sequence <- [anchor.sequence - 1, anchor.sequence + 1] do
      assert {:error, %Error{class: :recovery, reason: :sequence_mismatch, index: nil}} =
               Instance.recover(background(), history, %Chain{anchor | sequence: sequence})
    end

    assert {:error, %Error{class: :recovery, reason: :sequence_mismatch, index: nil}} =
             Instance.recover(background(), [first], anchor)

    assert {:error, %Error{class: :recovery, reason: :final_anchor_mismatch, index: nil}} =
             Instance.recover(background(), history, %Chain{anchor | head: <<0::256>>})
  end

  defp begin_command do
    %Command.BeginInvocation{
      agent: "agent",
      inv: "invocation",
      challenge: "challenge",
      policy: %Types.ActionPolicySnapshot{
        tool: "tool",
        required_caps: [:ipc, :filesystem_read],
        conf_clearance: :restricted,
        integ_floor: :untrusted,
        integ_inspect: :untrusted,
        output_conf: :public,
        output_integ: :attested,
        declared_egress: [],
        policy_digest: "policy"
      },
      egress: [],
      args_hash: "arguments",
      authorized: true
    }
  end

  defp begin_command_with_egress do
    command = begin_command()

    %Command.BeginInvocation{
      command
      | egress: [:ipc, :network_external],
        policy: %Types.ActionPolicySnapshot{
          command.policy
          | declared_egress: [:ipc, :network_external]
        }
    }
  end

  defp valid_command_actions do
    policy = %Types.ActionPolicySnapshot{
      tool: "x",
      required_caps: [:ipc, :filesystem_read],
      conf_clearance: :restricted,
      integ_floor: :untrusted,
      integ_inspect: :standard,
      output_conf: :internal,
      output_integ: :trusted,
      declared_egress: [:ipc, :network_external],
      policy_digest: "x"
    }

    inspection = %Types.InspectionAttestation{
      id: "x",
      inv: "x",
      challenge: "x",
      args_hash: "x",
      policy_digest: "x",
      positive: true
    }

    resolution = %Types.ResolutionAttestation{id: "x", inv: "x", outcome: :success}

    evidence = %Types.ConformanceAttestation{
      id: "x",
      output: "x",
      src: "x",
      rcv: "x",
      descriptor: "x",
      assignment: "x",
      positive: true
    }

    cross = %Types.CrossInput{
      src: "x",
      rcv: "x",
      crossing: "x",
      output_hash: "x",
      descriptor: "x",
      fallback: :release_unendorsed,
      t_integ: :trusted,
      t_conf: :internal,
      assignment: "x",
      evidence: evidence,
      released_conf: :internal,
      released_integ: :standard
    }

    [
      {%Command.RegisterTool{tool: "x"}, %Action.RegisterTool{tool: "x"}},
      {%Command.UnregisterTool{tool: "x"}, %Action.UnregisterTool{tool: "x"}},
      {%Command.Delegate{grantor: "x", grantee: "x"},
       %Action.Delegate{grantor: "x", grantee: "x"}},
      {%Command.GrantCapability{parent: "x", child: "x", cap: :ipc},
       %Action.GrantCapability{parent: "x", child: "x", cap: :ipc}},
      {%Command.GrantCrossing{grantor: "x", agent: "x", assignment: "x", n: 1},
       %Action.GrantCrossing{grantor: "x", agent: "x", assignment: "x", n: 1}},
      {%Command.Revoke{parent: "x", target: "x"}, %Action.Revoke{parent: "x", target: "x"}},
      {%Command.CascadeRevoke{child: "x", parent: "x"},
       %Action.CascadeRevoke{child: "x", parent: "x"}},
      {%Command.Ingest{agent: "x", src: "x", pconf: :internal, pinteg: :standard},
       %Action.Ingest{
         agent: "x",
         src: "x",
         pconf: :internal,
         pinteg: :standard,
         disposition: :permitted
       }},
      {%Command.BeginInvocation{
         agent: "x",
         inv: "x",
         challenge: "x",
         policy: policy,
         egress: [:ipc, :network_external],
         args_hash: "x",
         authorized: true
       },
       %Action.BeginInvocation{
         agent: "x",
         inv: "x",
         tool: "x",
         verdict: :allow,
         authorized: true
       }},
      {%Command.AuthorizeInspected{inv: "x", attestation: inspection},
       %Action.AuthorizeInspected{inv: "x", attestation: "x", admitted: true}},
      {%Command.SettleInvocation{inv: "x", outcome: :success, resolution: resolution},
       %Action.SettleInvocation{
         inv: "x",
         agent: "x",
         disposition: :permitted,
         outcome: :success,
         clvl: :internal,
         ilvl: :standard,
         resolution: "x"
       }},
      {%Command.CrossOutput{input: cross},
       %Action.CrossOutput{
         src: "x",
         rcv: "x",
         crossing: "x",
         branch: :endorsed,
         disposition: :permitted
       }}
    ]
  end

  defp invalid_action_field(field)
       when field in [
              :cap,
              :pconf,
              :pinteg,
              :disposition,
              :verdict,
              :outcome,
              :clvl,
              :ilvl,
              :branch
            ],
       do: {:forged, :unknown_enum}

  defp invalid_action_field(field) when field in [:authorized, :admitted],
    do: {:forged, :invalid_type}

  defp invalid_action_field(:n), do: {-1, :integer_out_of_range}
  defp invalid_action_field(_field), do: {:not_a_binary, :invalid_type}

  defp validation_envelope(command, action) do
    %Envelope{
      version: 5,
      sequence: 1,
      previous_digest: <<0::256>>,
      digest: <<1::256>>,
      command: command,
      action: action
    }
  end

  defp accepted_history do
    assert {:ok, instance} = Instance.new(background())
    assert {:ok, first} = Instance.register_tool(instance, "tool")
    assert {:ok, second} = Instance.delegate(instance, "root", "agent")
    assert {:ok, third} = Instance.grant_capability(instance, "root", "agent", :ipc)
    assert {:ok, anchor} = Instance.status(instance)
    assert {:ok, state} = Instance.state(instance)
    {[first, second, third], anchor, state}
  end
end
