defmodule ExArgus.ValidationTest do
  use ExUnit.Case, async: true

  alias ExArgus.{Command, Error, Instance, Validation}
  alias ExArgus.Kernel.{Background, Types}

  @egress [:network_external, :network_internal, :filesystem_write, :ipc]

  defp policy do
    %Types.ActionPolicySnapshot{
      tool: "tool",
      required_caps: [:ipc, :filesystem_read],
      conf_clearance: :restricted,
      integ_floor: :untrusted,
      integ_inspect: :untrusted,
      output_conf: :internal,
      output_integ: :trusted,
      declared_egress: [:ipc, :network_external],
      policy_digest: "policy"
    }
  end

  defp inspection do
    %Types.InspectionAttestation{
      id: "attestation",
      inv: "invocation",
      challenge: "challenge",
      args_hash: "arguments",
      policy_digest: "policy",
      positive: true
    }
  end

  defp resolution do
    %Types.ResolutionAttestation{id: "resolution", inv: "invocation", outcome: :success}
  end

  defp evidence do
    %Types.ConformanceAttestation{
      id: "evidence",
      output: "output",
      src: "source",
      rcv: "receiver",
      descriptor: "descriptor",
      assignment: "assignment",
      positive: true
    }
  end

  defp cross_input do
    %Types.CrossInput{
      src: "source",
      rcv: "receiver",
      crossing: "crossing",
      output_hash: "output",
      descriptor: "descriptor",
      fallback: :release_unendorsed,
      t_integ: :trusted,
      t_conf: :internal,
      assignment: "assignment",
      evidence: evidence(),
      released_conf: :internal,
      released_integ: :standard
    }
  end

  defp commands do
    [
      %Command.RegisterTool{tool: "tool"},
      %Command.UnregisterTool{tool: "tool"},
      %Command.Delegate{grantor: "root", grantee: "agent"},
      %Command.GrantCapability{parent: "root", child: "agent", cap: :filesystem_read},
      %Command.GrantCrossing{grantor: "root", agent: "agent", assignment: "assignment", n: 1},
      %Command.Revoke{parent: "root", target: "agent"},
      %Command.CascadeRevoke{child: "agent", parent: "root"},
      %Command.Ingest{agent: "agent", src: "source", pconf: :internal, pinteg: :standard},
      %Command.BeginInvocation{
        agent: "agent",
        inv: "invocation",
        challenge: "challenge",
        policy: policy(),
        egress: [:ipc, :network_external],
        args_hash: "arguments",
        authorized: true
      },
      %Command.AuthorizeInspected{inv: "invocation", attestation: inspection()},
      %Command.SettleInvocation{inv: "invocation", outcome: :success, resolution: resolution()},
      %Command.CrossOutput{input: cross_input()}
    ]
  end

  test "validates an exact register-tool command before Rustler decoding" do
    assert {:ok, %Command.RegisterTool{tool: "tool"}} =
             Validation.command(%Command.RegisterTool{tool: "tool"})

    for {command, reason, path} <- [
          {nil, :invalid_struct, []},
          {%Command.RegisterTool{tool: ""}, :empty_value, [:tool]},
          {%Command.RegisterTool{tool: <<0xFF>>}, :invalid_utf8, [:tool]},
          {%Command.RegisterTool{tool: String.duplicate("x", 1_025)}, :value_too_large, [:tool]},
          {Map.put(%Command.RegisterTool{tool: "tool"}, :forged, true), :invalid_keys, []}
        ] do
      assert {:error, %Error{class: :boundary, reason: ^reason, path: ^path}} =
               Validation.command(command)
    end
  end

  test "validates every command shape and normalizes every set by fixed tag" do
    assert Enum.all?(commands(), &match?({:ok, _}, Validation.command(&1)))

    begin_command = Enum.find(commands(), &match?(%Command.BeginInvocation{}, &1))
    assert {:ok, normalized} = Validation.command(begin_command)
    assert normalized.policy.required_caps == [:filesystem_read, :ipc]
    assert normalized.policy.declared_egress == [:network_external, :ipc]
    assert normalized.egress == [:network_external, :ipc]

    all_caps = [
      :filesystem_read,
      :filesystem_write,
      :filesystem_delete,
      :network_egress,
      :network_ingress,
      :execution_shell,
      :execution_code,
      :credentials,
      :system_info,
      :system_modify,
      :clipboard,
      :browser_navigate,
      :database_read,
      :database_write,
      :ipc
    ]

    assert {:ok, at_limit} =
             Validation.command(
               begin_with(
                 :policy,
                 %Types.ActionPolicySnapshot{
                   policy()
                   | required_caps: Enum.reverse(all_caps),
                     declared_egress: Enum.reverse(@egress)
                 }
               )
             )

    assert at_limit.policy.required_caps == all_caps
    assert at_limit.policy.declared_egress == @egress

    assert {:ok, %Command.RegisterTool{tool: tool}} =
             Validation.command(%Command.RegisterTool{tool: String.duplicate("x", 1_024)})

    assert byte_size(tool) == 1_024
  end

  test "rejects missing and forged keys on every command and nested input struct" do
    for command <- commands() do
      assert_boundary(
        Validation.command(Map.put(command, :forged, true)),
        :invalid_keys,
        []
      )

      for field <- command |> Map.from_struct() |> Map.keys() do
        assert_boundary(Validation.command(Map.delete(command, field)), :invalid_keys, [])
      end
    end

    nested = [
      {policy(), [:policy],
       fn value ->
         %Command.BeginInvocation{
           agent: "agent",
           inv: "inv",
           challenge: "challenge",
           policy: value,
           egress: [],
           args_hash: "args",
           authorized: true
         }
       end},
      {inspection(), [:attestation],
       fn value ->
         %Command.AuthorizeInspected{inv: "inv", attestation: value}
       end},
      {resolution(), [:resolution],
       fn value ->
         %Command.SettleInvocation{inv: "inv", outcome: :success, resolution: value}
       end},
      {cross_input(), [:input], fn value -> %Command.CrossOutput{input: value} end},
      {evidence(), [:input, :evidence],
       fn value ->
         %Command.CrossOutput{input: %Types.CrossInput{cross_input() | evidence: value}}
       end}
    ]

    for {value, path, wrap} <- nested do
      assert_boundary(
        Validation.command(wrap.(Map.put(value, :forged, true))),
        :invalid_keys,
        path
      )

      for field <- value |> Map.from_struct() |> Map.keys() do
        assert_boundary(
          Validation.command(wrap.(Map.delete(value, field))),
          :invalid_keys,
          path
        )
      end
    end
  end

  test "validates every opaque command field and every malformed binary class" do
    bad = :not_a_binary

    cases =
      [
        {%Command.RegisterTool{tool: bad}, [:tool]},
        {%Command.UnregisterTool{tool: bad}, [:tool]},
        {%Command.Delegate{grantor: bad, grantee: "agent"}, [:grantor]},
        {%Command.Delegate{grantor: "root", grantee: bad}, [:grantee]},
        {%Command.GrantCapability{parent: bad, child: "agent", cap: :ipc}, [:parent]},
        {%Command.GrantCapability{parent: "root", child: bad, cap: :ipc}, [:child]},
        {%Command.GrantCrossing{grantor: bad, agent: "agent", assignment: "a", n: 0}, [:grantor]},
        {%Command.GrantCrossing{grantor: "root", agent: bad, assignment: "a", n: 0}, [:agent]},
        {%Command.GrantCrossing{grantor: "root", agent: "agent", assignment: bad, n: 0},
         [:assignment]},
        {%Command.Revoke{parent: bad, target: "agent"}, [:parent]},
        {%Command.Revoke{parent: "root", target: bad}, [:target]},
        {%Command.CascadeRevoke{child: bad, parent: "root"}, [:child]},
        {%Command.CascadeRevoke{child: "agent", parent: bad}, [:parent]},
        {%Command.Ingest{agent: bad, src: nil, pconf: :public, pinteg: :untrusted}, [:agent]},
        {%Command.Ingest{agent: "agent", src: bad, pconf: :public, pinteg: :untrusted}, [:src]},
        {%Command.BeginInvocation{
           agent: bad,
           inv: "inv",
           challenge: "challenge",
           policy: policy(),
           egress: [],
           args_hash: "args",
           authorized: true
         }, [:agent]},
        {%Command.BeginInvocation{
           agent: "agent",
           inv: bad,
           challenge: "challenge",
           policy: policy(),
           egress: [],
           args_hash: "args",
           authorized: true
         }, [:inv]},
        {%Command.BeginInvocation{
           agent: "agent",
           inv: "inv",
           challenge: bad,
           policy: policy(),
           egress: [],
           args_hash: "args",
           authorized: true
         }, [:challenge]},
        {%Command.BeginInvocation{
           agent: "agent",
           inv: "inv",
           challenge: "challenge",
           policy: %Types.ActionPolicySnapshot{policy() | tool: bad},
           egress: [],
           args_hash: "args",
           authorized: true
         }, [:policy, :tool]},
        {%Command.BeginInvocation{
           agent: "agent",
           inv: "inv",
           challenge: "challenge",
           policy: %Types.ActionPolicySnapshot{policy() | policy_digest: bad},
           egress: [],
           args_hash: "args",
           authorized: true
         }, [:policy, :policy_digest]},
        {%Command.BeginInvocation{
           agent: "agent",
           inv: "inv",
           challenge: "challenge",
           policy: policy(),
           egress: [],
           args_hash: bad,
           authorized: true
         }, [:args_hash]},
        {%Command.AuthorizeInspected{inv: bad, attestation: inspection()}, [:inv]},
        {%Command.SettleInvocation{inv: bad, outcome: :success, resolution: nil}, [:inv]}
      ] ++
        attestation_opaque_cases(bad) ++ resolution_opaque_cases(bad) ++ cross_opaque_cases(bad)

    for {command, path} <- cases do
      assert_boundary(Validation.command(command), :invalid_type, path)
    end

    for {value, reason} <- [
          {"", :empty_value},
          {<<0xFF>>, :invalid_utf8},
          {String.duplicate("x", 1_025), :value_too_large},
          {String.duplicate("x", 1_024) <> <<0xFF>>, :value_too_large}
        ] do
      assert_boundary(
        Validation.command(%Command.RegisterTool{tool: value}),
        reason,
        [:tool]
      )

      command =
        %Command.CrossOutput{
          input: %Types.CrossInput{
            cross_input()
            | evidence: %Types.ConformanceAttestation{evidence() | descriptor: value}
          }
        }

      assert_boundary(Validation.command(command), reason, [:input, :evidence, :descriptor])
    end
  end

  test "validates every enum, boolean, option, integer, and set field" do
    enum_cases = [
      {%Command.GrantCapability{parent: "root", child: "agent", cap: :unknown}, [:cap]},
      {%Command.Ingest{agent: "agent", src: nil, pconf: :unknown, pinteg: :standard}, [:pconf]},
      {%Command.Ingest{agent: "agent", src: nil, pconf: :public, pinteg: :unknown}, [:pinteg]},
      {begin_with_policy(:conf_clearance, :unknown), [:policy, :conf_clearance]},
      {begin_with_policy(:integ_floor, :unknown), [:policy, :integ_floor]},
      {begin_with_policy(:integ_inspect, :unknown), [:policy, :integ_inspect]},
      {begin_with_policy(:output_conf, :unknown), [:policy, :output_conf]},
      {begin_with_policy(:output_integ, :unknown), [:policy, :output_integ]},
      {%Command.SettleInvocation{inv: "inv", outcome: :unknown, resolution: nil}, [:outcome]},
      {%Command.SettleInvocation{
         inv: "inv",
         outcome: :success,
         resolution: %Types.ResolutionAttestation{resolution() | outcome: :unknown}
       }, [:resolution, :outcome]},
      {cross_with(:fallback, :unknown), [:input, :fallback]},
      {cross_with(:t_integ, :unknown), [:input, :t_integ]},
      {cross_with(:t_conf, :unknown), [:input, :t_conf]},
      {cross_with(:released_conf, :unknown), [:input, :released_conf]},
      {cross_with(:released_integ, :unknown), [:input, :released_integ]}
    ]

    for {command, path} <- enum_cases do
      assert_boundary(Validation.command(command), :unknown_enum, path)
    end

    boolean_cases = [
      {%Command.BeginInvocation{
         agent: "agent",
         inv: "inv",
         challenge: "challenge",
         policy: policy(),
         egress: [],
         args_hash: "args",
         authorized: :yes
       }, [:authorized]},
      {%Command.AuthorizeInspected{
         inv: "inv",
         attestation: %Types.InspectionAttestation{inspection() | positive: :yes}
       }, [:attestation, :positive]},
      {%Command.CrossOutput{
         input: %Types.CrossInput{
           cross_input()
           | evidence: %Types.ConformanceAttestation{evidence() | positive: :yes}
         }
       }, [:input, :evidence, :positive]}
    ]

    for {command, path} <- boolean_cases do
      assert_boundary(Validation.command(command), :invalid_type, path)
    end

    assert {:ok, _} = Validation.command(begin_with(:authorized, false))

    assert {:ok, _} =
             Validation.command(%Command.AuthorizeInspected{
               inv: "inv",
               attestation: %Types.InspectionAttestation{inspection() | positive: false}
             })

    assert {:ok, _} =
             Validation.command(
               cross_with(:evidence, %Types.ConformanceAttestation{evidence() | positive: false})
             )

    for level <- [:public, :internal, :sensitive, :restricted] do
      assert {:ok, _} =
               Validation.command(%Command.Ingest{
                 agent: "agent",
                 src: nil,
                 pconf: level,
                 pinteg: :standard
               })

      assert {:ok, _} = Validation.command(cross_with(:t_conf, level))
    end

    for level <- [:untrusted, :standard, :trusted, :attested] do
      assert {:ok, _} =
               Validation.command(%Command.Ingest{
                 agent: "agent",
                 src: nil,
                 pconf: :public,
                 pinteg: level
               })
    end

    for outcome <- [:success, :failure, :ambiguous] do
      assert {:ok, _} =
               Validation.command(%Command.SettleInvocation{
                 inv: "inv",
                 outcome: outcome,
                 resolution: nil
               })
    end

    for fallback <- [:fail, :release_unendorsed] do
      assert {:ok, _} = Validation.command(cross_with(:fallback, fallback))
    end

    option_cases = [
      {%Command.Ingest{agent: "agent", src: 1, pconf: :public, pinteg: :untrusted}, [:src],
       :invalid_type},
      {%Command.SettleInvocation{inv: "inv", outcome: :success, resolution: 1}, [:resolution],
       :invalid_struct},
      {cross_with(:evidence, 1), [:input, :evidence], :invalid_struct}
    ]

    assert match?(
             {:ok, _},
             Validation.command(%Command.Ingest{
               agent: "agent",
               src: nil,
               pconf: :public,
               pinteg: :untrusted
             })
           )

    assert match?(
             {:ok, _},
             Validation.command(%Command.SettleInvocation{
               inv: "inv",
               outcome: :success,
               resolution: nil
             })
           )

    assert match?({:ok, _}, Validation.command(cross_with(:t_conf, nil)))
    assert match?({:ok, _}, Validation.command(cross_with(:evidence, nil)))

    for {command, path, reason} <- option_cases do
      assert_boundary(Validation.command(command), reason, path)
    end

    for n <- [0, 4_294_967_295] do
      assert {:ok, %Command.GrantCrossing{n: ^n}} =
               Validation.command(%Command.GrantCrossing{
                 grantor: "root",
                 agent: "agent",
                 assignment: "assignment",
                 n: n
               })
    end

    for n <- [-1, 4_294_967_296, 1.0, nil] do
      command = %Command.GrantCrossing{
        grantor: "root",
        agent: "agent",
        assignment: "assignment",
        n: n
      }

      assert_boundary(Validation.command(command), :integer_out_of_range, [:n])
    end

    set_cases = [
      {begin_with_policy(:required_caps, :not_a_list), [:policy, :required_caps], :invalid_type},
      {begin_with_policy(:required_caps, [:ipc, :ipc]), [:policy, :required_caps],
       :duplicate_value},
      {begin_with_policy(:required_caps, List.duplicate(:ipc, 16)), [:policy, :required_caps],
       :capacity_exceeded},
      {begin_with_policy(:declared_egress, [:ipc, :ipc]), [:policy, :declared_egress],
       :duplicate_value},
      {begin_with_policy(:declared_egress, List.duplicate(:ipc, 5)), [:policy, :declared_egress],
       :capacity_exceeded},
      {begin_with(:egress, :not_a_list), [:egress], :invalid_type},
      {begin_with(:egress, [:ipc, :ipc]), [:egress], :duplicate_value},
      {begin_with(:egress, List.duplicate(:ipc, 5)), [:egress], :capacity_exceeded},
      {begin_with(:egress, [:unknown]), [:egress, 0], :unknown_enum}
    ]

    for {command, path, reason} <- set_cases do
      assert_boundary(Validation.command(command), reason, path)
    end
  end

  test "bounded set probing rejects improper lists and stops at the capacity boundary" do
    improper_cases = [
      {begin_with(:egress, [:ipc | :improper]), [:egress]},
      {begin_with_policy(:required_caps, [:ipc | :improper]), [:policy, :required_caps]},
      {begin_with_policy(:declared_egress, [:ipc | :improper]), [:policy, :declared_egress]}
    ]

    for {command, path} <- improper_cases do
      assert_boundary(Validation.command(command), :invalid_type, path)
    end

    over_limit_with_improper_tail =
      begin_with(:egress, [:ipc, :ipc, :ipc, :ipc, :unknown | :improper])

    assert_boundary(
      Validation.command(over_limit_with_improper_tail),
      :capacity_exceeded,
      [:egress]
    )
  end

  test "validates the exact background, live instance, wide command kind, and quarantine helper" do
    ceiling = Map.new(@egress, &{&1, nil})
    background = %Background{mode: :enforce, allow_ceiling: ceiling, inspect_ceiling: ceiling}

    assert {:ok, ^background} = Validation.background(background)
    assert_boundary(Validation.background(nil), :invalid_struct, [])
    assert_boundary(Validation.background(%Background{}), :unknown_enum, [:mode])
    assert_boundary(Validation.background(Map.put(background, :forged, true)), :invalid_keys, [])

    for {field, value, reason, path} <- [
          {:mode, :unknown, :unknown_enum, [:mode]},
          {:allow_ceiling, [], :invalid_type, [:allow_ceiling]},
          {:allow_ceiling, %{}, :invalid_keys, [:allow_ceiling]},
          {:allow_ceiling, Map.put(ceiling, :network_external, :unknown), :unknown_enum,
           [:allow_ceiling, :network_external]},
          {:inspect_ceiling, Map.put(ceiling, :ipc, :unknown), :unknown_enum,
           [:inspect_ceiling, :ipc]}
        ] do
      assert_boundary(
        Validation.background(Map.replace!(background, field, value)),
        reason,
        path
      )
    end

    instance = %Instance{resource: make_ref()}
    assert {:ok, resource} = Validation.instance(instance)
    assert is_reference(resource)
    assert_boundary(Validation.instance(nil), :invalid_struct, [])
    assert_boundary(Validation.instance(%Instance{resource: :wrong}), :invalid_type, [:resource])
    assert_boundary(Validation.instance(Map.put(instance, :forged, true)), :invalid_keys, [])

    assert_boundary(
      Validation.command(%Command.BeginInvocation{}, :ingest),
      :invalid_struct,
      []
    )

    settle = %Command.SettleInvocation{inv: "inv", outcome: :failure, resolution: resolution()}
    assert {:ok, ^settle} = Validation.quarantine_resolution(settle)

    assert_boundary(
      Validation.quarantine_resolution(%Command.SettleInvocation{
        inv: "inv",
        outcome: :ambiguous,
        resolution: resolution()
      }),
      :unknown_enum,
      [:outcome]
    )
  end

  test "nested error paths are closed, bounded, and never contain offending values" do
    secret = "secret-caller-content"
    command = begin_with(:egress, [:network_external, secret])

    assert {:error, %Error{} = error} = Validation.command(command)
    assert error.path == [:egress, 1]
    assert length(error.path) <= 3
    assert Enum.all?(error.path, &(is_atom(&1) or &1 in 0..14))
    refute inspect(error) =~ secret
  end

  defp attestation_opaque_cases(bad) do
    fields = [:id, :inv, :challenge, :args_hash, :policy_digest]

    for field <- fields do
      attestation = Map.replace!(inspection(), field, bad)
      {%Command.AuthorizeInspected{inv: "inv", attestation: attestation}, [:attestation, field]}
    end
  end

  defp resolution_opaque_cases(bad) do
    for field <- [:id, :inv] do
      resolution = Map.replace!(resolution(), field, bad)

      {%Command.SettleInvocation{inv: "inv", outcome: :success, resolution: resolution},
       [:resolution, field]}
    end
  end

  defp cross_opaque_cases(bad) do
    input_fields = [:src, :rcv, :crossing, :output_hash, :descriptor, :assignment]
    evidence_fields = [:id, :output, :src, :rcv, :descriptor, :assignment]

    Enum.map(input_fields, fn field ->
      {%Command.CrossOutput{input: Map.replace!(cross_input(), field, bad)}, [:input, field]}
    end) ++
      Enum.map(evidence_fields, fn field ->
        evidence = Map.replace!(evidence(), field, bad)
        input = %Types.CrossInput{cross_input() | evidence: evidence}
        {%Command.CrossOutput{input: input}, [:input, :evidence, field]}
      end)
  end

  defp begin_with(field, value) do
    Map.replace!(
      %Command.BeginInvocation{
        agent: "agent",
        inv: "inv",
        challenge: "challenge",
        policy: policy(),
        egress: [],
        args_hash: "args",
        authorized: true
      },
      field,
      value
    )
  end

  defp begin_with_policy(field, value) do
    begin_with(:policy, Map.replace!(policy(), field, value))
  end

  defp cross_with(field, value) do
    %Command.CrossOutput{input: Map.replace!(cross_input(), field, value)}
  end

  defp assert_boundary(result, reason, path) do
    assert {:error, %Error{class: :boundary, reason: ^reason, path: ^path}} = result
  end
end
