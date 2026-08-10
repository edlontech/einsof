defmodule ExArgusTest do
  use ExUnit.Case, async: true

  alias ExArgus.Kernel.{Action, Background, State, Types}

  @struct_fields %{
    Background => [:mode, :allow_ceiling, :inspect_ceiling],
    State => [
      :agent_active,
      :agent_parent,
      :agent_cap,
      :taint_levels,
      :integ_levels,
      :pending,
      :challenges,
      :consumed_ids,
      :consumed_attestations,
      :consumed_crossings,
      :crossing_grants,
      :tool_registered
    ],
    Types.ActionPolicySnapshot => [
      :tool,
      :required_caps,
      :conf_clearance,
      :integ_floor,
      :integ_inspect,
      :output_conf,
      :output_integ,
      :declared_egress,
      :policy_digest
    ],
    Types.InspectionAttestation => [
      :id,
      :inv,
      :challenge,
      :args_hash,
      :policy_digest,
      :positive
    ],
    Types.ResolutionAttestation => [:id, :inv, :outcome],
    Types.ConformanceAttestation => [
      :id,
      :output,
      :src,
      :rcv,
      :descriptor,
      :assignment,
      :positive
    ],
    Types.CrossInput => [
      :src,
      :rcv,
      :crossing,
      :output_hash,
      :descriptor,
      :fallback,
      :t_integ,
      :t_conf,
      :assignment,
      :evidence,
      :released_conf,
      :released_integ
    ],
    Types.PendingInvocation => [
      :agent,
      :policy,
      :egress,
      :admission,
      :disposition,
      :authorized,
      :quarantined
    ],
    Types.ChallengeScope => [:challenge, :agent, :policy, :egress, :args_hash, :authorized],
    Types.CrossingGrant => [:remaining, :provisioned],
    ExArgus.Command.RegisterTool => [:tool],
    ExArgus.Command.UnregisterTool => [:tool],
    ExArgus.Command.Delegate => [:grantor, :grantee],
    ExArgus.Command.GrantCapability => [:parent, :child, :cap],
    ExArgus.Command.GrantCrossing => [:grantor, :agent, :assignment, :n],
    ExArgus.Command.Revoke => [:parent, :target],
    ExArgus.Command.CascadeRevoke => [:child, :parent],
    ExArgus.Command.Ingest => [:agent, :src, :pconf, :pinteg],
    ExArgus.Command.BeginInvocation => [
      :agent,
      :inv,
      :challenge,
      :policy,
      :egress,
      :args_hash,
      :authorized
    ],
    ExArgus.Command.AuthorizeInspected => [:inv, :attestation],
    ExArgus.Command.SettleInvocation => [:inv, :outcome, :resolution],
    ExArgus.Command.CrossOutput => [:input],
    Action.RegisterTool => [:tool],
    Action.UnregisterTool => [:tool],
    Action.Delegate => [:grantor, :grantee],
    Action.GrantCapability => [:parent, :child, :cap],
    Action.GrantCrossing => [:grantor, :agent, :assignment, :n],
    Action.Revoke => [:parent, :target],
    Action.CascadeRevoke => [:child, :parent],
    Action.Ingest => [:agent, :src, :pconf, :pinteg, :disposition],
    Action.BeginInvocation => [:agent, :inv, :tool, :verdict, :authorized],
    Action.AuthorizeInspected => [:inv, :attestation, :admitted],
    Action.SettleInvocation => [
      :inv,
      :agent,
      :disposition,
      :outcome,
      :clvl,
      :ilvl,
      :resolution
    ],
    Action.CrossOutput => [:src, :rcv, :crossing, :branch, :disposition],
    ExArgus.Envelope => [:version, :sequence, :previous_digest, :digest, :command, :action],
    ExArgus.Chain => [:version, :sequence, :head],
    ExArgus.Error => [:class, :reason, :path, :index, :cause]
  }

  @limits %{
    max_opaque_utf8_bytes: 1_024,
    max_agents: 4_096,
    max_parent_or_label_keys: 4_096,
    max_tools: 1_024,
    max_pending: 4_096,
    max_challenges: 4_096,
    max_crossing_grants: 16_384,
    max_consumed_ids: 65_536,
    max_consumed_attestations: 65_536,
    max_consumed_crossings: 65_536,
    max_retained_utf8_bytes: 16 * 1024 * 1024,
    max_accepted_sequence: 100_000,
    max_recovery_envelopes: 100_000,
    max_replay_content_bytes: 64 * 1024 * 1024,
    max_capabilities: 15,
    max_egress_kinds: 4,
    max_conf_levels: 4,
    max_integ_levels: 4
  }

  @vocabulary %{
    conf_level: [:public, :internal, :sensitive, :restricted],
    integ_level: [:untrusted, :standard, :trusted, :attested],
    egress_kind: [:network_external, :network_internal, :filesystem_write, :ipc],
    cap_kind: [
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
    ],
    verdict: [:allow, :inspection_required, :deny],
    disposition: [:permitted, :blocked, :monitor_bypassed],
    mode: [:enforce, :monitor],
    outcome: [:success, :failure, :ambiguous],
    fallback: [:fail, :release_unendorsed],
    cross_branch: [:endorsed, :unendorsed, :fail]
  }

  test "publishes only the V5 protocol version" do
    assert ExArgus.state_version() == 5
    refute function_exported?(ExArgus, :log_header, 0)
    refute function_exported?(ExArgus, :strip_log_header, 1)
  end

  test "publishes the exact closed V4 vocabulary" do
    {:ok, types} = Code.Typespec.fetch_types(Types)

    for {name, expected} <- @vocabulary do
      assert type_atoms(types, name) == expected
    end
  end

  test "mirrors every native struct module and field in declaration order" do
    for {module, expected} <- @struct_fields do
      assert struct_fields(module) == expected
    end
  end

  test "state is the canonical twelve-field read-only projection" do
    assert struct_fields(State) == @struct_fields[State]
    assert State.__info__(:functions) == [__struct__: 0, __struct__: 1]
  end

  test "public capacity limits exactly agree with the native source manifest" do
    native_source =
      __DIR__
      |> Path.join("../native/argus_nif/src/limits.rs")
      |> Path.expand()
      |> File.read!()

    for {name, expected} <- @limits do
      assert apply(ExArgus.Limits, name, []) == expected

      native_name = name |> Atom.to_string() |> String.upcase()
      pattern = ~r/pub const #{native_name}: [^=]+ = ([^;]+);/
      assert [_, expression] = Regex.run(pattern, native_source)
      assert rust_integer_expression(expression) == expected
    end
  end

  defp rust_integer_expression(expression) do
    expression
    |> String.replace("_", "")
    |> String.split("*", trim: true)
    |> Enum.map(&(&1 |> String.trim() |> String.to_integer()))
    |> Enum.product()
  end

  defp struct_fields(module) do
    module.__info__(:struct)
    |> Enum.map(& &1.field)
  end

  defp type_atoms(types, name) do
    {:type, {^name, ast, []}} = Enum.find(types, &match?({:type, {^name, _, []}}, &1))

    case ast do
      {:type, _, :union, values} -> Enum.map(values, fn {:atom, _, value} -> value end)
      {:atom, _, value} -> [value]
    end
  end
end
