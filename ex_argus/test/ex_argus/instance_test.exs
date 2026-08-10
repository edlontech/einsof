defmodule ExArgus.InstanceTest do
  use ExUnit.Case, async: true

  alias ExArgus.{Command, Error, Instance}
  alias ExArgus.Kernel.{Action, Background, Types}

  @egress [:network_external, :network_internal, :filesystem_write, :ipc]

  defp background(mode \\ :enforce, allow \\ nil, inspect \\ nil) do
    allow_ceiling = Map.new(@egress, &{&1, allow})
    inspect_ceiling = Map.new(@egress, &{&1, inspect})
    %Background{mode: mode, allow_ceiling: allow_ceiling, inspect_ceiling: inspect_ceiling}
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

  defp begin_command(overrides \\ %{}) do
    Map.merge(
      %Command.BeginInvocation{
        agent: "agent",
        inv: "invocation",
        challenge: "challenge",
        policy: policy(),
        egress: [],
        args_hash: "arguments",
        authorized: true
      },
      overrides
    )
  end

  defp prepare_agent(instance, agent \\ "agent") do
    assert {:ok, _} = Instance.delegate(instance, "root", agent)
    instance
  end

  defp prepare_invocation(instance, command \\ begin_command()) do
    assert {:ok, _} = Instance.register_tool(instance, command.policy.tool)
    prepare_agent(instance, command.agent)
    assert {:ok, _} = Instance.begin_invocation(instance, command)
    instance
  end

  test "register_tool validates, applies, and returns one complete envelope" do
    assert {:ok, instance} = Instance.new(background())

    assert {:ok,
            %ExArgus.Envelope{
              version: 5,
              sequence: 1,
              command: %Command.RegisterTool{tool: "tool"},
              action: %Action.RegisterTool{tool: "tool"}
            }} = Instance.register_tool(instance, "tool")

    assert {:error, %Error{class: :boundary, reason: :invalid_utf8, path: [:tool]}} =
             Instance.register_tool(instance, <<0xFF>>)
  end

  test "exposes only the twelve named actions and quarantine helper" do
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
    refute function_exported?(Instance, :apply, 2)
    refute function_exported?(Instance, :apply, 3)
  end

  test "all seven simple wrappers construct and apply their matching command once" do
    assert {:ok, instance} = Instance.new(background())
    assert {:ok, %{command: %Command.RegisterTool{}}} = Instance.register_tool(instance, "tool")

    assert {:ok, %{command: %Command.UnregisterTool{}}} =
             Instance.unregister_tool(instance, "tool")

    assert {:ok, %{command: %Command.Delegate{}}} = Instance.delegate(instance, "root", "agent")

    assert {:ok, %{command: %Command.GrantCapability{}}} =
             Instance.grant_capability(instance, "root", "agent", :filesystem_read)

    assert {:ok, %{command: %Command.GrantCrossing{}}} =
             Instance.grant_crossing(instance, "root", "agent", "assignment", 2)

    assert {:ok, %{command: %Command.Revoke{}}} = Instance.revoke(instance, "root", "agent")

    assert {:ok, _} = Instance.delegate(instance, "root", "parent")
    assert {:ok, _} = Instance.delegate(instance, "parent", "child")
    assert {:ok, _} = Instance.revoke(instance, "root", "parent")

    assert {:ok, %{command: %Command.CascadeRevoke{}}} =
             Instance.cascade_revoke(instance, "child", "parent")
  end

  test "all five wide wrappers accept only their exact command and return normalized commands" do
    assert {:ok, ingest_instance} = Instance.new(background())
    prepare_agent(ingest_instance)

    assert {:ok, %{command: %Command.Ingest{}}} =
             Instance.ingest(
               ingest_instance,
               %Command.Ingest{agent: "agent", src: nil, pconf: :public, pinteg: :untrusted}
             )

    assert {:ok, begin_instance} = Instance.new(background())
    assert {:ok, _} = Instance.register_tool(begin_instance, "tool")
    prepare_agent(begin_instance)
    assert {:ok, _} = Instance.grant_capability(begin_instance, "root", "agent", :filesystem_read)
    assert {:ok, _} = Instance.grant_capability(begin_instance, "root", "agent", :ipc)

    begin =
      begin_command(%{
        policy: policy(%{required_caps: [:ipc, :filesystem_read]}),
        egress: []
      })

    assert {:ok,
            %{
              command: %Command.BeginInvocation{
                policy: %Types.ActionPolicySnapshot{
                  required_caps: [:filesystem_read, :ipc]
                }
              }
            }} = Instance.begin_invocation(begin_instance, begin)

    inspection_background = background(:enforce, :internal, :sensitive)
    assert {:ok, inspection_instance} = Instance.new(inspection_background)

    inspection_begin =
      begin_command(%{
        policy:
          policy(%{
            output_conf: :sensitive,
            declared_egress: [:network_external]
          }),
        egress: [:network_external]
      })

    prepare_invocation(inspection_instance, inspection_begin)

    attestation = %Types.InspectionAttestation{
      id: "attestation",
      inv: "invocation",
      challenge: "challenge",
      args_hash: "arguments",
      policy_digest: "policy",
      positive: true
    }

    assert {:ok, %{command: %Command.AuthorizeInspected{}}} =
             Instance.authorize_inspected(
               inspection_instance,
               %Command.AuthorizeInspected{inv: "invocation", attestation: attestation}
             )

    assert {:ok, settle_instance} = Instance.new(background())
    prepare_invocation(settle_instance)

    assert {:ok, %{command: %Command.SettleInvocation{}}} =
             Instance.settle_invocation(
               settle_instance,
               %Command.SettleInvocation{inv: "invocation", outcome: :success, resolution: nil}
             )

    assert {:ok, crossing_instance} = Instance.new(background())
    prepare_agent(crossing_instance, "source")
    prepare_agent(crossing_instance, "receiver")

    input = %Types.CrossInput{
      src: "source",
      rcv: "receiver",
      crossing: "crossing",
      output_hash: "output",
      descriptor: "descriptor",
      fallback: :fail,
      t_integ: :trusted,
      t_conf: :internal,
      assignment: "assignment",
      evidence: nil,
      released_conf: :internal,
      released_integ: :standard
    }

    assert {:ok, %{command: %Command.CrossOutput{}}} =
             Instance.cross_output(crossing_instance, %Command.CrossOutput{input: input})

    wrong_calls = [
      fn -> Instance.ingest(crossing_instance, begin_command()) end,
      fn ->
        Instance.begin_invocation(
          crossing_instance,
          %Command.Ingest{agent: "agent", src: nil, pconf: :public, pinteg: :untrusted}
        )
      end,
      fn ->
        Instance.authorize_inspected(
          crossing_instance,
          %Command.SettleInvocation{inv: "inv", outcome: :success, resolution: nil}
        )
      end,
      fn -> Instance.settle_invocation(crossing_instance, %Command.CrossOutput{input: input}) end,
      fn -> Instance.cross_output(crossing_instance, begin_command()) end
    ]

    for call <- wrong_calls do
      assert {:error, %Error{class: :boundary, reason: :invalid_struct}} = call.()
    end
  end

  test "resolve_quarantine validates its narrow outcome and executes one settlement" do
    assert {:ok, instance} = Instance.new(background())
    prepare_invocation(instance)

    assert {:ok, _} =
             Instance.settle_invocation(
               instance,
               %Command.SettleInvocation{inv: "invocation", outcome: :ambiguous, resolution: nil}
             )

    assert {:ok, before} = Instance.status(instance)

    resolution =
      %Types.ResolutionAttestation{id: "resolution", inv: "invocation", outcome: :success}

    assert {:ok,
            %{
              sequence: sequence,
              command: %Command.SettleInvocation{
                inv: "invocation",
                outcome: :success,
                resolution: ^resolution
              },
              action: %Action.SettleInvocation{resolution: "resolution"}
            }} = Instance.resolve_quarantine(instance, "invocation", :success, resolution)

    assert sequence == before.sequence + 1
    assert {:ok, %{sequence: ^sequence}} = Instance.status(instance)

    assert {:error, %Error{class: :boundary, reason: :unknown_enum, path: [:outcome]}} =
             Instance.resolve_quarantine(instance, "invocation", :ambiguous, resolution)
  end

  test "kernel refusal and boundary refusal preserve accepted status and state" do
    assert {:ok, instance} = Instance.new(background())
    assert {:ok, _} = Instance.register_tool(instance, "tool")
    assert {:ok, status_before} = Instance.status(instance)
    assert {:ok, state_before} = Instance.state(instance)

    assert {:error, %Error{class: :kernel, reason: :tool_already_registered}} =
             Instance.register_tool(instance, "tool")

    assert {:error, %Error{class: :boundary, reason: :invalid_utf8}} =
             Instance.register_tool(instance, <<0xFF>>)

    assert Instance.status(instance) == {:ok, status_before}
    assert Instance.state(instance) == {:ok, state_before}
  end

  test "maps the complete native kernel-error vocabulary without wildcard kernel classification" do
    source = File.read!(Path.expand("../../native/argus_nif/src/event.rs", __DIR__))
    [_, body] = Regex.run(~r/pub enum KernelErrorN \{(.*?)\n\}/s, source)

    native_reasons =
      ~r/^    ([A-Z][A-Za-z]+),$/m
      |> Regex.scan(body, capture: :all_but_first)
      |> List.flatten()
      |> Enum.map(&Macro.underscore/1)

    assert native_reasons == Enum.map(Error.kernel_reasons(), &Atom.to_string/1)

    for reason <- Error.kernel_reasons() do
      assert {:error, %Error{class: :kernel, reason: ^reason}} =
               Error.from_native({:kernel, reason})
    end

    assert {:error, %Error{class: :internal, reason: :native_contract_violation}} =
             Error.from_native({:kernel, :forged_reason})

    for reason <- [:instance_busy, :capacity_exceeded, :sequence_exhausted] do
      assert {:error, %Error{class: :boundary, reason: ^reason}} = Error.from_native(reason)
    end

    assert {:error, %Error{class: :internal, reason: :resource_poisoned}} =
             Error.from_native(:resource_poisoned)
  end

  test "malformed action values never leak Rustler badarg" do
    assert {:ok, instance} = Instance.new(background())

    calls = [
      fn -> Instance.register_tool(instance, <<0xFF>>) end,
      fn -> Instance.unregister_tool(instance, nil) end,
      fn -> Instance.delegate(instance, "root", nil) end,
      fn -> Instance.grant_capability(instance, "root", "agent", :unknown) end,
      fn -> Instance.grant_crossing(instance, "root", "agent", "assignment", 4_294_967_296) end,
      fn -> Instance.revoke(instance, "root", nil) end,
      fn -> Instance.cascade_revoke(instance, nil, "root") end,
      fn -> Instance.ingest(instance, %Command.Ingest{}) end,
      fn -> Instance.begin_invocation(instance, %Command.BeginInvocation{}) end,
      fn -> Instance.authorize_inspected(instance, %Command.AuthorizeInspected{}) end,
      fn -> Instance.settle_invocation(instance, %Command.SettleInvocation{}) end,
      fn -> Instance.cross_output(instance, %Command.CrossOutput{}) end
    ]

    for call <- calls do
      assert {:error, %Error{class: :boundary}} = call.()
    end
  end
end
