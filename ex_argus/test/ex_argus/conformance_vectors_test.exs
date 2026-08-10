defmodule ExArgus.ConformanceVectorsTest do
  use ExUnit.Case, async: false

  alias ExArgus.{Chain, Command, Envelope, Error, Instance, Limits}
  alias ExArgus.Kernel.{Action, Background, Types}

  @event [:ex_argus, :transition]
  @path Path.expand("../../priv/conformance/v4.json", __DIR__)
  @egress ~w(network_external network_internal filesystem_write ipc)
  @caps ~w(filesystem_read filesystem_write filesystem_delete network_egress network_ingress execution_shell execution_code credentials system_info system_modify clipboard browser_navigate database_read database_write ipc)
  @conf ~w(public internal sensitive restricted)
  @integ ~w(untrusted standard trusted attested)
  @actions ~w(register_tool unregister_tool delegate grant_capability grant_crossing revoke cascade_revoke ingest begin_invocation authorize_inspected settle_invocation cross_output)
  @telemetry_vocabulary @actions ++
                          @caps ++
                          @egress ++
                          @conf ++
                          @integ ++
                          ~w(enforce monitor allow inspection_required deny permitted blocked monitor_bypassed success failure ambiguous fail release_unendorsed endorsed unendorsed plain inspected bypassed)

  @doc false
  def send_event(event, measurements, metadata, pid),
    do: send(pid, {:telemetry, event, measurements, metadata})

  setup do
    id = {__MODULE__, self(), make_ref()}
    :ok = :telemetry.attach(id, @event, &__MODULE__.send_event/4, self())
    on_exit(fn -> :telemetry.detach(id) end)
    :ok
  end

  test "strict parser rejects unknown, missing, extra, duplicate, enum, set, digest, order, and trailing content" do
    input = File.read!(@path)
    corpus = decode_strict!(input)
    assert corpus["schema"] == "ex_argus.v4.conformance"

    malformed = [
      String.replace(
        input,
        ~s("schema": "ex_argus.v4.conformance"),
        ~s("unknown": true, "schema": "ex_argus.v4.conformance"),
        global: false
      ),
      String.replace(input, ~s("version": 5,), "", global: false),
      String.replace(input, ~s("version": 5,), ~s("version": 5, "version": 5,), global: false),
      String.replace(input, ~s("mode": "enforce"), ~s("mode": "unknown"), global: false),
      String.replace(input, ~s("tool": "tool"), ~s("tool": 1), global: false),
      String.replace(input, ~s("required_caps": []), ~s("required_caps": ["ipc", "ipc"]),
        global: false
      ),
      String.replace(input, ~s("head": "), ~s("head": "GG), global: false),
      String.replace(input, ~s("sequence": 1), ~s("sequence": 3), global: false),
      input <> " true"
    ]

    for {value, index} <- Enum.with_index(malformed) do
      try do
        decode_strict!(value)
        flunk("mutation #{index} was accepted")
      rescue
        ArgumentError -> :ok
      end
    end

    [first, second | _] = corpus["semantic_cases"]

    duplicate_id =
      String.replace(input, ~s("id": "#{second["id"]}"), ~s("id": "#{first["id"]}"),
        global: false
      )

    assert_raise ArgumentError, fn -> decode_strict!(duplicate_id) end
  end

  test "public Instance executes exact envelopes, states, statuses, telemetry, and every accepted prefix" do
    corpus = corpus()

    for semantic <- corpus["semantic_cases"] do
      background = background(semantic["background"])
      assert {:ok, instance} = Instance.new(background)
      assert raw_ok(Instance.status(instance)) == semantic["initial_chain"]
      history = []
      checkpoints = []

      {history, checkpoints} =
        Enum.reduce(semantic["steps"], {history, checkpoints}, fn step, {history, checkpoints} ->
          command = command(step["command"])
          expected = step["expected"]
          before_state = raw_ok(Instance.state(instance))
          before_status = raw_ok(Instance.status(instance))
          result = call(instance, command)
          metadata = assert_telemetry(expected["telemetry"])
          refute_content(metadata, command)
          refute_receive {:telemetry, _, _, _}

          case expected["result"] do
            %{"kind" => "accepted", "action" => action} ->
              assert {:ok, %Envelope{} = envelope} = result
              assert raw(envelope.action) == action
              assert raw(envelope.command) == step["command"]
              assert envelope.version == 5
              assert envelope.sequence == expected["chain"]["sequence"]
              assert hex(envelope.previous_digest) == before_status["head"]
              assert hex(envelope.digest) == expected["chain"]["head"]
              next_history = history ++ [envelope]

              next_checkpoints =
                checkpoints ++ [{next_history, expected["chain"], expected["state"]}]

              {next_history, next_checkpoints}

            %{"kind" => "error", "class" => class, "reason" => reason} ->
              assert {:error, %Error{} = error} = result
              assert Atom.to_string(error.class) == class
              assert Atom.to_string(error.reason) == reason
              assert raw_ok(Instance.state(instance)) == before_state
              assert raw_ok(Instance.status(instance)) == before_status
              {history, checkpoints}
          end
          |> tap(fn _ ->
            assert raw_ok(Instance.state(instance)) == expected["state"]
            assert raw_ok(Instance.status(instance)) == expected["chain"]
          end)
        end)

      assert length(history) == List.last(semantic["steps"])["expected"]["chain"]["sequence"]

      assert {:ok, empty} = Instance.recover(background, [], chain(semantic["initial_chain"]))
      assert raw_ok(Instance.status(empty)) == semantic["initial_chain"]
      refute_receive {:telemetry, _, _, _}

      for {prefix, expected_chain, expected_state} <- checkpoints do
        assert {:ok, recovered} = Instance.recover(background, prefix, chain(expected_chain))
        assert raw_ok(Instance.status(recovered)) == expected_chain
        assert raw_ok(Instance.state(recovered)) == expected_state
        refute_receive {:telemetry, _, _, _}
      end
    end
  end

  test "all boundary vector classes return exact public typed errors and one bounded event" do
    for vector <- corpus()["boundary_cases"] do
      {result, command_name} = boundary_attempt(vector["mutation"])
      expected = vector["expected"]
      assert {:error, %Error{} = error} = result
      assert_error(error, expected)

      if command_name do
        assert vector["telemetry"]["command"] == command_name
        assert_telemetry(vector["telemetry"])
      else
        assert is_nil(vector["telemetry"])
        refute_receive {:telemetry, _, _, _}
      end
    end
  end

  test "strict public recovery rejects every corpus corruption with no telemetry" do
    source = Enum.find(corpus()["semantic_cases"], &(&1["id"] == "structural_lifecycle"))
    {background, history, anchor} = accepted_history(source)

    for vector <- corpus()["recovery_cases"] do
      {candidate_background, candidate_history, candidate_anchor} =
        corrupt(vector["mutation"], background, history, anchor)

      assert {:error, %Error{} = error} =
               Instance.recover(candidate_background, candidate_history, candidate_anchor)

      assert_error(error, vector["expected"])
      assert vector["telemetry_events"] == 0
      refute_receive {:telemetry, _, _, _}
    end
  end

  test "coverage audit pins every action, enum, branch, and the unreachable blocked disposition" do
    corpus = corpus()
    vocabulary = corpus["vocabulary"]
    assert vocabulary["actions"] == @actions
    assert vocabulary["capabilities"] == @caps
    assert vocabulary["egress"] == @egress
    assert vocabulary["confidentiality"] == @conf
    assert vocabulary["integrity"] == @integ
    assert vocabulary["dispositions"] == ~w(permitted blocked monitor_bypassed)

    actions =
      for semantic <- corpus["semantic_cases"],
          step <- semantic["steps"],
          step["expected"]["result"]["kind"] == "accepted",
          do: step["command"]["type"]

    assert MapSet.new(actions) == MapSet.new(@actions)

    coverage = corpus["semantic_cases"] |> Enum.flat_map(& &1["covers"]) |> MapSet.new()
    assert Enum.all?(corpus["required_coverage"], &MapSet.member?(coverage, &1))

    dispositions =
      for semantic <- corpus["semantic_cases"],
          step <- semantic["steps"],
          pending <- step["expected"]["state"]["pending"],
          do: pending |> Enum.at(1) |> Map.fetch!("disposition")

    refute "blocked" in dispositions
    assert "blocked" in vocabulary["dispositions"]
  end

  defp corpus, do: @path |> File.read!() |> decode_strict!()

  defp decode_strict!(input) do
    decoded =
      case Jason.decode(input, objects: :ordered_objects) do
        {:ok, value} -> value
        {:error, error} -> raise ArgumentError, Exception.message(error)
      end

    value = ordered_to_map!(decoded)
    validate_corpus!(value)
    value
  end

  defp ordered_to_map!(%Jason.OrderedObject{values: values}) do
    keys = Enum.map(values, &elem(&1, 0))
    if length(keys) != length(Enum.uniq(keys)), do: raise(ArgumentError, "duplicate object key")
    Map.new(values, fn {key, value} -> {key, ordered_to_map!(value)} end)
  end

  defp ordered_to_map!(values) when is_list(values), do: Enum.map(values, &ordered_to_map!/1)
  defp ordered_to_map!(value), do: value

  defp validate_corpus!(corpus) do
    exact!(
      corpus,
      ~w(schema version vocabulary required_coverage semantic_cases boundary_cases recovery_cases goldens)
    )

    truth!(corpus["schema"] == "ex_argus.v4.conformance" and corpus["version"] == 5)
    validate_vocabulary!(corpus["vocabulary"])
    unique!(corpus["required_coverage"])

    all_ids =
      Enum.flat_map(
        ~w(semantic_cases boundary_cases recovery_cases goldens),
        &Enum.map(corpus[&1], fn item -> item["id"] end)
      )

    unique!(all_ids)
    semantic_ids = MapSet.new(Enum.map(corpus["semantic_cases"], & &1["id"]))
    Enum.each(corpus["semantic_cases"], &validate_semantic!/1)

    Enum.each(corpus["boundary_cases"], fn item ->
      exact!(item, ~w(id mutation expected telemetry))
      validate_error!(item["expected"])
      if item["telemetry"], do: validate_telemetry!(item["telemetry"])
    end)

    Enum.each(corpus["recovery_cases"], fn item ->
      exact!(item, ~w(id source_case mutation expected telemetry_events))
      truth!(MapSet.member?(semantic_ids, item["source_case"]))
      truth!(item["telemetry_events"] == 0)
      validate_error!(item["expected"])
    end)

    Enum.each(corpus["goldens"], fn item ->
      exact!(item, ~w(id kind background case_id step_id transcript_hex digest))
      hex!(item["transcript_hex"])
      digest!(item["digest"])
    end)
  end

  defp validate_vocabulary!(value) do
    exact!(
      value,
      ~w(actions capabilities egress confidentiality integrity modes verdicts dispositions outcomes fallbacks cross_branches admissions telemetry_outcomes)
    )

    truth!(value["actions"] == @actions)
    truth!(value["capabilities"] == @caps)
    truth!(value["egress"] == @egress)
    truth!(value["confidentiality"] == @conf)
    truth!(value["integrity"] == @integ)
    truth!(value["modes"] == ~w(enforce monitor))
    truth!(value["verdicts"] == ~w(allow inspection_required deny))
    truth!(value["dispositions"] == ~w(permitted blocked monitor_bypassed))
    truth!(value["outcomes"] == ~w(success failure ambiguous))
    truth!(value["fallbacks"] == ~w(fail release_unendorsed))
    truth!(value["cross_branches"] == ~w(endorsed unendorsed fail))
    truth!(value["admissions"] == ~w(plain inspected bypassed))

    truth!(
      value["telemetry_outcomes"] == ~w(accepted kernel_refused boundary_refused internal_error)
    )
  end

  defp validate_semantic!(semantic) do
    exact!(semantic, ~w(id background initial_chain covers steps))
    unique!(semantic["covers"])
    validate_background!(semantic["background"])
    validate_chain!(semantic["initial_chain"])
    truth!(semantic["initial_chain"]["sequence"] == 0)
    unique!(Enum.map(semantic["steps"], & &1["id"]))

    Enum.reduce(semantic["steps"], {0, semantic["initial_chain"], nil}, fn step,
                                                                           {accepted, prior_chain,
                                                                            prior_state} ->
      exact!(step, ~w(id command expected))
      validate_command!(step["command"])
      expected = step["expected"]
      exact!(expected, ~w(result state chain telemetry transcript_hex))
      validate_state!(expected["state"])
      validate_chain!(expected["chain"])
      validate_telemetry!(expected["telemetry"])
      if expected["transcript_hex"], do: hex!(expected["transcript_hex"])

      validate_semantic_result!(step, expected, accepted, prior_chain, prior_state)
    end)
  end

  defp validate_semantic_result!(
         step,
         %{"result" => %{"kind" => "accepted"}} = expected,
         accepted,
         _prior_chain,
         _prior_state
       ) do
    exact!(expected["result"], ~w(kind action))
    validate_action!(expected["result"]["action"])
    truth!(expected["chain"]["sequence"] == accepted + 1)
    truth!(expected["telemetry"]["command"] == step["command"]["type"])
    truth!(expected["telemetry"]["outcome"] == "accepted")
    truth!(expected["telemetry"]["sequence"] == accepted + 1)
    {accepted + 1, expected["chain"], expected["state"]}
  end

  defp validate_semantic_result!(
         step,
         %{"result" => %{"kind" => "error"}} = expected,
         accepted,
         prior_chain,
         prior_state
       ) do
    exact!(expected["result"], ~w(kind class reason))
    truth!(expected["result"]["class"] == "kernel")
    truth!(expected["chain"] == prior_chain)
    truth!(expected["telemetry"]["command"] == step["command"]["type"])
    truth!(expected["telemetry"]["outcome"] == "kernel_refused")
    truth!(is_nil(expected["telemetry"]["sequence"]))
    if prior_state, do: truth!(expected["state"] == prior_state)
    {accepted, prior_chain, expected["state"]}
  end

  defp validate_semantic_result!(_step, _expected, _accepted, _prior_chain, _prior_state),
    do: raise(ArgumentError, "unknown result kind")

  defp validate_background!(value) do
    exact!(value, ~w(mode allow_ceiling inspect_ceiling))
    enum!(value["mode"], ~w(enforce monitor))
    Enum.each(~w(allow_ceiling inspect_ceiling), &validate_ceiling!(value[&1]))
  end

  defp validate_ceiling!(value) do
    exact!(value, @egress)
    Enum.each(@egress, fn egress -> if value[egress], do: enum!(value[egress], @conf) end)
  end

  defp validate_command!(%{"type" => type} = value) do
    keys = %{
      "register_tool" => ~w(type tool),
      "unregister_tool" => ~w(type tool),
      "delegate" => ~w(type grantor grantee),
      "grant_capability" => ~w(type parent child cap),
      "grant_crossing" => ~w(type grantor agent assignment n),
      "revoke" => ~w(type parent target),
      "cascade_revoke" => ~w(type child parent),
      "ingest" => ~w(type agent src pconf pinteg),
      "begin_invocation" => ~w(type agent inv challenge policy egress args_hash authorized),
      "authorize_inspected" => ~w(type inv attestation),
      "settle_invocation" => ~w(type inv outcome resolution),
      "cross_output" => ~w(type input)
    }

    enum!(type, Map.keys(keys))
    exact!(value, Map.fetch!(keys, type))
    validate_command_fields!(type, value)
  end

  defp validate_command!(_), do: raise(ArgumentError, "invalid command")

  defp validate_command_fields!(type, value)
       when type in ["register_tool", "unregister_tool"] do
    string!(value["tool"])
  end

  defp validate_command_fields!("delegate", value) do
    strings!(value, ~w(grantor grantee))
  end

  defp validate_command_fields!("grant_capability", value) do
    strings!(value, ~w(parent child))
    enum!(value["cap"], @caps)
  end

  defp validate_command_fields!("grant_crossing", value) do
    strings!(value, ~w(grantor agent assignment))
    u32!(value["n"])
  end

  defp validate_command_fields!(type, value) when type in ["revoke", "cascade_revoke"] do
    strings!(value, Map.keys(value) -- ["type"])
  end

  defp validate_command_fields!("ingest", value) do
    string!(value["agent"])
    optional_string!(value["src"])
    enum!(value["pconf"], @conf)
    enum!(value["pinteg"], @integ)
  end

  defp validate_command_fields!("begin_invocation", value) do
    strings!(value, ~w(agent inv challenge args_hash))
    validate_policy!(value["policy"])
    set!(value["egress"], @egress)
    truth!(is_boolean(value["authorized"]))
  end

  defp validate_command_fields!("authorize_inspected", value) do
    string!(value["inv"])
    validate_inspection!(value["attestation"])
  end

  defp validate_command_fields!("settle_invocation", value) do
    string!(value["inv"])
    enum!(value["outcome"], ~w(success failure ambiguous))
    if value["resolution"], do: validate_resolution!(value["resolution"])
  end

  defp validate_command_fields!("cross_output", value), do: validate_cross!(value["input"])
  defp validate_command_fields!(_type, _value), do: :ok

  defp validate_action!(%{"type" => type} = value) do
    keys = %{
      "register_tool" => ~w(type tool),
      "unregister_tool" => ~w(type tool),
      "delegate" => ~w(type grantor grantee),
      "grant_capability" => ~w(type parent child cap),
      "grant_crossing" => ~w(type grantor agent assignment n),
      "revoke" => ~w(type parent target),
      "cascade_revoke" => ~w(type child parent),
      "ingest" => ~w(type agent src pconf pinteg disposition),
      "begin_invocation" => ~w(type agent inv tool verdict authorized),
      "authorize_inspected" => ~w(type inv attestation admitted),
      "settle_invocation" => ~w(type inv agent disposition outcome clvl ilvl resolution),
      "cross_output" => ~w(type src rcv crossing branch disposition)
    }

    enum!(type, Map.keys(keys))
    exact!(value, Map.fetch!(keys, type))
    validate_action_fields!(type, value)
  end

  defp validate_action_fields!(type, value)
       when type in ["register_tool", "unregister_tool"],
       do: string!(value["tool"])

  defp validate_action_fields!(type, value)
       when type in ["delegate", "revoke", "cascade_revoke"],
       do: strings!(value, Map.keys(value) -- ["type"])

  defp validate_action_fields!("grant_capability", value) do
    strings!(value, ~w(parent child))
    enum!(value["cap"], @caps)
  end

  defp validate_action_fields!("grant_crossing", value) do
    strings!(value, ~w(grantor agent assignment))
    u32!(value["n"])
  end

  defp validate_action_fields!("ingest", value) do
    string!(value["agent"])
    optional_string!(value["src"])
    enum!(value["pconf"], @conf)
    enum!(value["pinteg"], @integ)
    disposition!(value["disposition"])
  end

  defp validate_action_fields!("begin_invocation", value) do
    strings!(value, ~w(agent inv tool))
    enum!(value["verdict"], ~w(allow inspection_required deny))
    truth!(is_boolean(value["authorized"]))
  end

  defp validate_action_fields!("authorize_inspected", value) do
    strings!(value, ~w(inv attestation))
    truth!(is_boolean(value["admitted"]))
  end

  defp validate_action_fields!("settle_invocation", value) do
    strings!(value, ~w(inv agent))
    optional_string!(value["resolution"])
    disposition!(value["disposition"])
    enum!(value["outcome"], ~w(success failure ambiguous))
    enum!(value["clvl"], @conf)
    enum!(value["ilvl"], @integ)
  end

  defp validate_action_fields!("cross_output", value) do
    strings!(value, ~w(src rcv crossing))
    enum!(value["branch"], ~w(endorsed unendorsed fail))
    disposition!(value["disposition"])
  end

  defp validate_policy!(value) do
    exact!(
      value,
      ~w(tool required_caps conf_clearance integ_floor integ_inspect output_conf output_integ declared_egress policy_digest)
    )

    strings!(value, ~w(tool policy_digest))
    set!(value["required_caps"], @caps)
    set!(value["declared_egress"], @egress)
    Enum.each(~w(conf_clearance output_conf), &enum!(value[&1], @conf))
    Enum.each(~w(integ_floor integ_inspect output_integ), &enum!(value[&1], @integ))
  end

  defp validate_inspection!(value) do
    exact!(value, ~w(id inv challenge args_hash policy_digest positive))
    strings!(value, ~w(id inv challenge args_hash policy_digest))
    truth!(is_boolean(value["positive"]))
  end

  defp validate_resolution!(value) do
    exact!(value, ~w(id inv outcome))
    strings!(value, ~w(id inv))
    enum!(value["outcome"], ~w(success failure ambiguous))
  end

  defp validate_cross!(value) do
    exact!(
      value,
      ~w(src rcv crossing output_hash descriptor fallback t_integ t_conf assignment evidence released_conf released_integ)
    )

    strings!(value, ~w(src rcv crossing output_hash descriptor assignment))
    enum!(value["fallback"], ~w(fail release_unendorsed))
    Enum.each(~w(t_integ released_integ), &enum!(value[&1], @integ))
    Enum.each(~w(t_conf released_conf), fn key -> if value[key], do: enum!(value[key], @conf) end)

    if value["evidence"] do
      exact!(value["evidence"], ~w(id output src rcv descriptor assignment positive))
      strings!(value["evidence"], ~w(id output src rcv descriptor assignment))
      truth!(is_boolean(value["evidence"]["positive"]))
    end
  end

  defp validate_state!(value) do
    exact!(
      value,
      ~w(agent_active agent_parent agent_cap taint_levels integ_levels pending challenges consumed_ids consumed_attestations consumed_crossings crossing_grants tool_registered)
    )

    Enum.each(
      ~w(agent_active consumed_ids consumed_attestations consumed_crossings tool_registered),
      fn key ->
        unique!(value[key])
        Enum.each(value[key], &string!/1)
      end
    )

    Enum.each(
      ~w(agent_parent agent_cap taint_levels integ_levels pending challenges crossing_grants),
      fn key ->
        unique!(Enum.map(value[key], &hd/1))

        Enum.each(value[key], fn pair ->
          truth!(is_list(pair) and length(pair) == 2)
          pair |> hd() |> validate_state_key!()
        end)
      end
    )

    Enum.each(value["agent_parent"], fn [_key, parent] -> string!(parent) end)
    Enum.each(value["agent_cap"], fn [_key, values] -> set!(values, @caps) end)
    Enum.each(value["taint_levels"], fn [_key, values] -> set!(values, @conf) end)
    Enum.each(value["integ_levels"], fn [_key, values] -> set!(values, @integ) end)

    Enum.each(value["pending"], fn [_key, pending] ->
      exact!(pending, ~w(agent policy egress admission disposition authorized quarantined))
      string!(pending["agent"])
      validate_policy!(pending["policy"])
      set!(pending["egress"], @egress)
      exact!(pending["admission"], ~w(kind attestation))
      enum!(pending["admission"]["kind"], ~w(plain inspected bypassed))
      optional_string!(pending["admission"]["attestation"])

      truth!(
        pending["admission"]["kind"] == "inspected" ==
          is_binary(pending["admission"]["attestation"])
      )

      disposition!(pending["disposition"])
      truth!(is_boolean(pending["authorized"]) and is_boolean(pending["quarantined"]))
    end)

    Enum.each(value["challenges"], fn [_key, challenge] ->
      exact!(challenge, ~w(challenge agent policy egress args_hash authorized))
      strings!(challenge, ~w(challenge agent args_hash))
      validate_policy!(challenge["policy"])
      set!(challenge["egress"], @egress)
      truth!(is_boolean(challenge["authorized"]))
    end)

    Enum.each(value["crossing_grants"], fn [_key, grant] ->
      exact!(grant, ~w(remaining provisioned))
      u32!(grant["remaining"])
      u32!(grant["provisioned"])
      truth!(grant["remaining"] <= grant["provisioned"])
    end)
  end

  defp validate_chain!(value) do
    exact!(value, ~w(version sequence head))
    truth!(value["version"] == 5 and is_integer(value["sequence"]) and value["sequence"] >= 0)
    digest!(value["head"])
  end

  defp validate_telemetry!(value) do
    exact!(value, ~w(command outcome sequence reason verdict disposition branch))
    enum!(value["command"], @actions)
    enum!(value["outcome"], ~w(accepted kernel_refused boundary_refused internal_error))
    truth!(is_nil(value["sequence"]) or (is_integer(value["sequence"]) and value["sequence"] > 0))
    optional_string!(value["reason"])
    if value["verdict"], do: enum!(value["verdict"], ~w(allow inspection_required deny))
    if value["disposition"], do: disposition!(value["disposition"])
    if value["branch"], do: enum!(value["branch"], ~w(endorsed unendorsed fail))
  end

  defp validate_error!(value) do
    exact!(value, ~w(class reason path index cause))
    enum!(value["class"], ~w(boundary kernel recovery internal))
    string!(value["reason"])
    truth!(is_list(value["path"]))
    Enum.each(value["path"], &string!/1)
    truth!(is_nil(value["index"]) or (is_integer(value["index"]) and value["index"] >= 0))
    optional_string!(value["cause"])
  end

  defp exact!(value, keys) when is_map(value) do
    truth!(MapSet.new(Map.keys(value)) == MapSet.new(keys))
  end

  defp exact!(_value, _keys), do: raise(ArgumentError, "invalid object")
  defp truth!(true), do: :ok
  defp truth!(_), do: raise(ArgumentError, "schema validation failed")
  defp string!(value), do: truth!(is_binary(value) and value != "")
  defp strings!(value, keys), do: Enum.each(keys, &string!(value[&1]))
  defp optional_string!(nil), do: :ok
  defp optional_string!(value), do: string!(value)
  defp u32!(value), do: truth!(is_integer(value) and value in 0..4_294_967_295)
  defp disposition!(value), do: enum!(value, ~w(permitted blocked monitor_bypassed))
  defp validate_state_key!(value) when is_binary(value), do: string!(value)

  defp validate_state_key!([left, right]),
    do: strings!(%{"left" => left, "right" => right}, ~w(left right))

  defp validate_state_key!(_value), do: raise(ArgumentError, "invalid state key")

  defp unique!(values) when is_list(values),
    do: truth!(length(values) == length(Enum.uniq(values)))

  defp unique!(_), do: raise(ArgumentError, "invalid list")
  defp enum!(value, allowed), do: truth!(value in allowed)

  defp set!(values, allowed) do
    unique!(values)
    Enum.each(values, &enum!(&1, allowed))
  end

  defp digest!(value),
    do: truth!(is_binary(value) and byte_size(value) == 64 and value =~ ~r/\A[0-9a-f]{64}\z/)

  defp hex!(value),
    do:
      truth!(
        is_binary(value) and byte_size(value) > 0 and rem(byte_size(value), 2) == 0 and
          value =~ ~r/\A[0-9a-f]+\z/
      )

  defp background(value) do
    %Background{
      mode: atom(value["mode"]),
      allow_ceiling: atom_map(value["allow_ceiling"]),
      inspect_ceiling: atom_map(value["inspect_ceiling"])
    }
  end

  defp command(%{"type" => "register_tool", "tool" => tool}),
    do: %Command.RegisterTool{tool: tool}

  defp command(%{"type" => "unregister_tool", "tool" => tool}),
    do: %Command.UnregisterTool{tool: tool}

  defp command(%{"type" => "delegate"} = v),
    do: %Command.Delegate{grantor: v["grantor"], grantee: v["grantee"]}

  defp command(%{"type" => "grant_capability"} = v),
    do: %Command.GrantCapability{parent: v["parent"], child: v["child"], cap: atom(v["cap"])}

  defp command(%{"type" => "grant_crossing"} = v),
    do: %Command.GrantCrossing{
      grantor: v["grantor"],
      agent: v["agent"],
      assignment: v["assignment"],
      n: v["n"]
    }

  defp command(%{"type" => "revoke"} = v),
    do: %Command.Revoke{parent: v["parent"], target: v["target"]}

  defp command(%{"type" => "cascade_revoke"} = v),
    do: %Command.CascadeRevoke{child: v["child"], parent: v["parent"]}

  defp command(%{"type" => "ingest"} = v),
    do: %Command.Ingest{
      agent: v["agent"],
      src: v["src"],
      pconf: atom(v["pconf"]),
      pinteg: atom(v["pinteg"])
    }

  defp command(%{"type" => "begin_invocation"} = v),
    do: %Command.BeginInvocation{
      agent: v["agent"],
      inv: v["inv"],
      challenge: v["challenge"],
      policy: policy(v["policy"]),
      egress: atoms(v["egress"]),
      args_hash: v["args_hash"],
      authorized: v["authorized"]
    }

  defp command(%{"type" => "authorize_inspected"} = v),
    do: %Command.AuthorizeInspected{inv: v["inv"], attestation: inspection(v["attestation"])}

  defp command(%{"type" => "settle_invocation"} = v),
    do: %Command.SettleInvocation{
      inv: v["inv"],
      outcome: atom(v["outcome"]),
      resolution: resolution(v["resolution"])
    }

  defp command(%{"type" => "cross_output", "input" => input}),
    do: %Command.CrossOutput{input: cross(input)}

  defp policy(v) do
    %Types.ActionPolicySnapshot{
      tool: v["tool"],
      required_caps: atoms(v["required_caps"]),
      conf_clearance: atom(v["conf_clearance"]),
      integ_floor: atom(v["integ_floor"]),
      integ_inspect: atom(v["integ_inspect"]),
      output_conf: atom(v["output_conf"]),
      output_integ: atom(v["output_integ"]),
      declared_egress: atoms(v["declared_egress"]),
      policy_digest: v["policy_digest"]
    }
  end

  defp inspection(v) do
    %Types.InspectionAttestation{
      id: v["id"],
      inv: v["inv"],
      challenge: v["challenge"],
      args_hash: v["args_hash"],
      policy_digest: v["policy_digest"],
      positive: v["positive"]
    }
  end

  defp resolution(nil), do: nil

  defp resolution(v),
    do: %Types.ResolutionAttestation{id: v["id"], inv: v["inv"], outcome: atom(v["outcome"])}

  defp evidence(nil), do: nil

  defp evidence(v) do
    %Types.ConformanceAttestation{
      id: v["id"],
      output: v["output"],
      src: v["src"],
      rcv: v["rcv"],
      descriptor: v["descriptor"],
      assignment: v["assignment"],
      positive: v["positive"]
    }
  end

  defp cross(v) do
    %Types.CrossInput{
      src: v["src"],
      rcv: v["rcv"],
      crossing: v["crossing"],
      output_hash: v["output_hash"],
      descriptor: v["descriptor"],
      fallback: atom(v["fallback"]),
      t_integ: atom(v["t_integ"]),
      t_conf: atom(v["t_conf"]),
      assignment: v["assignment"],
      evidence: evidence(v["evidence"]),
      released_conf: atom(v["released_conf"]),
      released_integ: atom(v["released_integ"])
    }
  end

  defp call(instance, %Command.RegisterTool{tool: tool}),
    do: Instance.register_tool(instance, tool)

  defp call(instance, %Command.UnregisterTool{tool: tool}),
    do: Instance.unregister_tool(instance, tool)

  defp call(instance, %Command.Delegate{} = v),
    do: Instance.delegate(instance, v.grantor, v.grantee)

  defp call(instance, %Command.GrantCapability{} = v),
    do: Instance.grant_capability(instance, v.parent, v.child, v.cap)

  defp call(instance, %Command.GrantCrossing{} = v),
    do: Instance.grant_crossing(instance, v.grantor, v.agent, v.assignment, v.n)

  defp call(instance, %Command.Revoke{} = v), do: Instance.revoke(instance, v.parent, v.target)

  defp call(instance, %Command.CascadeRevoke{} = v),
    do: Instance.cascade_revoke(instance, v.child, v.parent)

  defp call(instance, %Command.Ingest{} = v), do: Instance.ingest(instance, v)
  defp call(instance, %Command.BeginInvocation{} = v), do: Instance.begin_invocation(instance, v)

  defp call(instance, %Command.AuthorizeInspected{} = v),
    do: Instance.authorize_inspected(instance, v)

  defp call(instance, %Command.SettleInvocation{} = v),
    do: Instance.settle_invocation(instance, v)

  defp call(instance, %Command.CrossOutput{} = v), do: Instance.cross_output(instance, v)

  defp assert_telemetry(expected) do
    assert_receive {:telemetry, @event, measurements, metadata}
    assert Map.keys(measurements) == [:duration]
    assert is_integer(measurements.duration) and measurements.duration >= 0

    assert Enum.sort(Map.keys(metadata)) ==
             Enum.sort([:command, :outcome, :sequence, :reason, :verdict, :disposition, :branch])

    assert raw(metadata) == expected
    metadata
  end

  defp refute_content(metadata, command) do
    encoded = inspect(metadata)

    command
    |> raw()
    |> collect_strings()
    |> Enum.each(fn value ->
      if byte_size(value) > 8 and value not in @telemetry_vocabulary,
        do: refute(encoded =~ value)
    end)
  end

  defp collect_strings(value) when is_binary(value), do: [value]

  defp collect_strings(value) when is_map(value),
    do: value |> Map.values() |> Enum.flat_map(&collect_strings/1)

  defp collect_strings(value) when is_list(value), do: Enum.flat_map(value, &collect_strings/1)
  defp collect_strings(_), do: []

  defp boundary_attempt(mutation)
       when mutation in ["invalid_shape", "missing_key", "extra_key"] do
    {:ok, instance} = Instance.new(empty_background())

    value =
      case mutation do
        "invalid_shape" ->
          nil

        "missing_key" ->
          %{__struct__: Command.Ingest, agent: "agent"}

        "extra_key" ->
          Map.put(
            %Command.Ingest{agent: "agent", src: nil, pconf: :public, pinteg: :untrusted},
            :extra,
            true
          )
      end

    {Instance.ingest(instance, value), "ingest"}
  end

  defp boundary_attempt(mutation)
       when mutation in ["invalid_type", "invalid_utf8", "empty_value", "oversize_value"] do
    {:ok, instance} = Instance.new(empty_background())

    value =
      %{
        "invalid_type" => nil,
        "invalid_utf8" => <<255>>,
        "empty_value" => "",
        "oversize_value" => String.duplicate("x", 1025)
      }[mutation]

    {Instance.register_tool(instance, value), "register_tool"}
  end

  defp boundary_attempt("unknown_enum") do
    {:ok, instance} = Instance.new(empty_background())
    {Instance.grant_capability(instance, "root", "agent", :unknown), "grant_capability"}
  end

  defp boundary_attempt("duplicate_set_member") do
    {:ok, instance} = Instance.new(empty_background())

    command = %Command.BeginInvocation{
      agent: "agent",
      inv: "inv",
      challenge: "challenge",
      policy: %Types.ActionPolicySnapshot{
        tool: "tool",
        required_caps: [:ipc, :ipc],
        conf_clearance: :restricted,
        integ_floor: :untrusted,
        integ_inspect: :untrusted,
        output_conf: :public,
        output_integ: :attested,
        declared_egress: [],
        policy_digest: "policy"
      },
      egress: [],
      args_hash: "args",
      authorized: true
    }

    {Instance.begin_invocation(instance, command), "begin_invocation"}
  end

  defp boundary_attempt("u32_overflow") do
    {:ok, instance} = Instance.new(empty_background())

    {Instance.grant_crossing(instance, "root", "agent", "assignment", 4_294_967_296),
     "grant_crossing"}
  end

  defp boundary_attempt(mutation) when mutation in ["invalid_digest", "invalid_version"] do
    {background, [envelope], anchor} = one_envelope_history()

    malformed =
      if mutation == "invalid_digest",
        do: %{envelope | digest: <<0>>},
        else: %{envelope | version: 4}

    {Instance.recover(background, [malformed], anchor), nil}
  end

  defp boundary_attempt("recovery_count") do
    {background, [envelope], _anchor} = one_envelope_history()

    history =
      for sequence <- 1..(Limits.max_recovery_envelopes() + 1),
          do: %{envelope | sequence: sequence, previous_digest: <<0::256>>, digest: <<0::256>>}

    anchor = %Chain{version: 5, sequence: length(history), head: <<0::256>>}
    {Instance.recover(background, history, anchor), nil}
  end

  defp boundary_attempt("recovery_content") do
    background = empty_background()
    text = String.duplicate("x", Limits.max_opaque_utf8_bytes())
    count = div(Limits.max_replay_content_bytes(), 64 + 2 * byte_size(text)) + 1

    history =
      for sequence <- 1..count,
          do: %Envelope{
            version: 5,
            sequence: sequence,
            previous_digest: <<0::256>>,
            digest: <<0::256>>,
            command: %Command.RegisterTool{tool: text},
            action: %Action.RegisterTool{tool: text}
          }

    anchor = %Chain{version: 5, sequence: count, head: <<0::256>>}
    {Instance.recover(background, history, anchor), nil}
  end

  defp one_envelope_history do
    background = empty_background()
    {:ok, instance} = Instance.new(background)
    {:ok, envelope} = Instance.register_tool(instance, "tool")

    assert_telemetry(%{
      "command" => "register_tool",
      "outcome" => "accepted",
      "sequence" => 1,
      "reason" => nil,
      "verdict" => nil,
      "disposition" => nil,
      "branch" => nil
    })

    {:ok, anchor} = Instance.status(instance)
    {background, [envelope], anchor}
  end

  defp accepted_history(source) do
    background = background(source["background"])
    {:ok, instance} = Instance.new(background)

    history =
      Enum.map(source["steps"], fn step ->
        {:ok, envelope} = call(instance, command(step["command"]))
        assert_telemetry(step["expected"]["telemetry"])
        envelope
      end)

    {:ok, anchor} = Instance.status(instance)
    {background, history, anchor}
  end

  defp corrupt("edit", background, history, anchor),
    do:
      {background,
       List.update_at(history, 2, &%{&1 | command: %Command.RegisterTool{tool: "tool"}}), anchor}

  defp corrupt("insertion", background, history, anchor),
    do: {background, List.insert_at(history, 2, Enum.at(history, 1)), anchor}

  defp corrupt("deletion", background, history, anchor),
    do: {background, List.delete_at(history, 1), anchor}

  defp corrupt("reorder", background, [a, b | rest], anchor),
    do: {background, [b, a | rest], anchor}

  defp corrupt("duplicate", background, history, anchor),
    do: {background, List.insert_at(history, 1, hd(history)), anchor}

  defp corrupt("gap", background, history, anchor),
    do: {background, List.update_at(history, 1, &%{&1 | sequence: 3}), anchor}

  defp corrupt("wrong_background", %Background{} = background, history, anchor),
    do: {%Background{background | mode: :monitor}, history, anchor}

  defp corrupt("wrong_action", background, history, anchor),
    do:
      {background,
       List.update_at(history, 0, &%{&1 | action: %Action.RegisterTool{tool: "edited"}}), anchor}

  defp corrupt("wrong_digest", background, history, anchor) do
    history =
      history
      |> List.update_at(2, &%{&1 | digest: <<0::256>>})
      |> List.update_at(3, &%{&1 | previous_digest: <<0::256>>})

    {background, history, anchor}
  end

  defp corrupt("replay_refusal", background, history, anchor),
    do:
      {background,
       List.update_at(history, 1, &%{&1 | command: %Command.RegisterTool{tool: "tool"}}), anchor}

  defp corrupt("stale_anchor", background, history, %Chain{} = anchor),
    do: {background, history, %Chain{anchor | sequence: anchor.sequence - 1}}

  defp corrupt("truncated_anchor", background, history, anchor),
    do: {background, [hd(history)], anchor}

  defp assert_error(error, expected) do
    assert Atom.to_string(error.class) == expected["class"]
    assert Atom.to_string(error.reason) == expected["reason"]
    assert Enum.map(error.path, &to_string/1) == expected["path"]
    assert error.index == expected["index"]
    assert if(error.cause, do: Atom.to_string(error.cause), else: nil) == expected["cause"]
  end

  defp empty_background do
    ceiling = Map.new(Enum.map(@egress, &atom/1), &{&1, nil})
    %Background{mode: :enforce, allow_ceiling: ceiling, inspect_ceiling: ceiling}
  end

  defp chain(value),
    do: %Chain{
      version: value["version"],
      sequence: value["sequence"],
      head: Base.decode16!(value["head"], case: :lower)
    }

  defp raw_ok({:ok, value}), do: raw(value)
  defp hex(value), do: Base.encode16(value, case: :lower)
  defp atoms(values), do: Enum.map(values, &atom/1)
  defp atom(nil), do: nil
  defp atom(value), do: String.to_atom(value)
  defp atom_map(value), do: Map.new(value, fn {key, item} -> {atom(key), atom_value(item)} end)
  defp atom_value(value) when is_binary(value), do: atom(value)
  defp atom_value(value) when is_list(value), do: atoms(value)
  defp atom_value(value), do: value

  defp raw(%Chain{} = value),
    do: %{"version" => value.version, "sequence" => value.sequence, "head" => hex(value.head)}

  defp raw(%{__struct__: module} = value) do
    map = value |> Map.from_struct() |> raw()

    if command_or_action?(module),
      do: Map.put(map, "type", module |> Module.split() |> List.last() |> Macro.underscore()),
      else: map
  end

  defp raw({:inspected, id}), do: %{"kind" => "inspected", "attestation" => id}

  defp raw(value) when value in [:plain, :bypassed],
    do: %{"kind" => Atom.to_string(value), "attestation" => nil}

  defp raw(nil), do: nil
  defp raw(value) when is_boolean(value), do: value
  defp raw(value) when is_atom(value), do: Atom.to_string(value)
  defp raw(value) when is_binary(value), do: value
  defp raw(value) when is_list(value), do: Enum.map(value, &raw/1)
  defp raw(value) when is_tuple(value), do: value |> Tuple.to_list() |> Enum.map(&raw/1)

  defp raw(value) when is_map(value),
    do: Map.new(value, fn {key, item} -> {to_string(key), raw(item)} end)

  defp raw(value), do: value

  defp command_or_action?(module) do
    name = Atom.to_string(module)
    String.contains?(name, "ExArgus.Command.") or String.contains?(name, "ExArgus.Kernel.Action.")
  end
end
