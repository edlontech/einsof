defmodule ExArgus.Validation do
  @moduledoc false

  alias ExArgus.{Chain, Command, Envelope, Error, Instance, Limits}
  alias ExArgus.Kernel.{Action, Background}
  alias ExArgus.Kernel.Types

  @u32_max 4_294_967_295

  @conf_levels [:public, :internal, :sensitive, :restricted]
  @integ_levels [:untrusted, :standard, :trusted, :attested]
  @egress_kinds [:network_external, :network_internal, :filesystem_write, :ipc]
  @capabilities [
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
  @outcomes [:success, :failure, :ambiguous]

  @command_names [
    :register_tool,
    :unregister_tool,
    :delegate,
    :grant_capability,
    :grant_crossing,
    :revoke,
    :cascade_revoke,
    :ingest,
    :begin_invocation,
    :authorize_inspected,
    :settle_invocation,
    :cross_output
  ]

  @doc false
  def background(%Background{} = background) do
    with :ok <- exact_keys(background, [:__struct__, :mode, :allow_ceiling, :inspect_ceiling], []),
         :ok <- enum(background.mode, [:enforce, :monitor], [:mode]),
         :ok <- ceiling(background.allow_ceiling, [:allow_ceiling]),
         :ok <- ceiling(background.inspect_ceiling, [:inspect_ceiling]) do
      {:ok, background}
    end
  end

  def background(_background), do: boundary_error(:invalid_struct, [])

  @doc false
  def recovery(background, history, expected) do
    with {:ok, normalized_background} <- background(background),
         {:ok, normalized_history, length, last_digest} <- history(history),
         {:ok, normalized_expected} <- chain(expected),
         :ok <- expected_sequence(normalized_expected.sequence, length),
         :ok <- expected_head(normalized_expected.head, last_digest) do
      {:ok, {normalized_background, normalized_history, normalized_expected}}
    end
  end

  @doc false
  def checked_recovery_count(index) when is_integer(index) and index >= 0 do
    if index < Limits.max_recovery_envelopes() do
      :ok
    else
      boundary_error(:capacity_exceeded, [], index)
    end
  end

  def checked_recovery_count(_index), do: boundary_error(:invalid_type, [])

  @doc false
  def checked_replay_content(total, bytes)
      when is_integer(total) and total >= 0 and is_integer(bytes) and bytes >= 0 do
    maximum = Limits.max_replay_content_bytes()

    if total <= maximum and bytes <= maximum - total do
      {:ok, total + bytes}
    else
      boundary_error(:capacity_exceeded, [])
    end
  end

  def checked_replay_content(_total, _bytes), do: boundary_error(:invalid_type, [])

  @doc false
  def replay_envelope_content(envelope) do
    case envelope(envelope, 0) do
      {:ok, _normalized, content} -> {:ok, content}
      {:error, %Error{} = error} -> {:error, error}
    end
  end

  @doc false
  def instance(%Instance{} = instance) do
    with :ok <- exact_keys(instance, [:__struct__, :resource], []),
         true <- is_reference(instance.resource) do
      {:ok, instance.resource}
    else
      false -> boundary_error(:invalid_type, [:resource])
      {:error, %Error{}} = error -> error
    end
  end

  def instance(_instance), do: boundary_error(:invalid_struct, [])

  @doc false
  def command(%Command.RegisterTool{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :tool], []),
         :ok <- opaque(command.tool, [:tool]) do
      {:ok, command}
    end
  end

  def command(%Command.UnregisterTool{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :tool], []),
         :ok <- opaque(command.tool, [:tool]) do
      {:ok, command}
    end
  end

  def command(%Command.Delegate{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :grantor, :grantee], []),
         :ok <- opaque(command.grantor, [:grantor]),
         :ok <- opaque(command.grantee, [:grantee]) do
      {:ok, command}
    end
  end

  def command(%Command.GrantCapability{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :parent, :child, :cap], []),
         :ok <- opaque(command.parent, [:parent]),
         :ok <- opaque(command.child, [:child]),
         :ok <- enum(command.cap, @capabilities, [:cap]) do
      {:ok, command}
    end
  end

  def command(%Command.GrantCrossing{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :grantor, :agent, :assignment, :n], []),
         :ok <- opaque(command.grantor, [:grantor]),
         :ok <- opaque(command.agent, [:agent]),
         :ok <- opaque(command.assignment, [:assignment]),
         :ok <- u32(command.n, [:n]) do
      {:ok, command}
    end
  end

  def command(%Command.Revoke{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :parent, :target], []),
         :ok <- opaque(command.parent, [:parent]),
         :ok <- opaque(command.target, [:target]) do
      {:ok, command}
    end
  end

  def command(%Command.CascadeRevoke{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :child, :parent], []),
         :ok <- opaque(command.child, [:child]),
         :ok <- opaque(command.parent, [:parent]) do
      {:ok, command}
    end
  end

  def command(%Command.Ingest{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :agent, :src, :pconf, :pinteg], []),
         :ok <- opaque(command.agent, [:agent]),
         :ok <- optional_opaque(command.src, [:src]),
         :ok <- enum(command.pconf, @conf_levels, [:pconf]),
         :ok <- enum(command.pinteg, @integ_levels, [:pinteg]) do
      {:ok, command}
    end
  end

  def command(%Command.BeginInvocation{} = command) do
    with :ok <-
           exact_keys(
             command,
             [
               :__struct__,
               :agent,
               :inv,
               :challenge,
               :policy,
               :egress,
               :args_hash,
               :authorized
             ],
             []
           ),
         :ok <- opaque(command.agent, [:agent]),
         :ok <- opaque(command.inv, [:inv]),
         :ok <- opaque(command.challenge, [:challenge]),
         {:ok, policy} <- policy(command.policy, [:policy]),
         {:ok, egress} <-
           set(command.egress, @egress_kinds, Limits.max_egress_kinds(), [:egress]),
         :ok <- opaque(command.args_hash, [:args_hash]),
         :ok <- boolean(command.authorized, [:authorized]) do
      {:ok, %Command.BeginInvocation{command | policy: policy, egress: egress}}
    end
  end

  def command(%Command.AuthorizeInspected{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :inv, :attestation], []),
         :ok <- opaque(command.inv, [:inv]),
         {:ok, attestation} <- inspection(command.attestation, [:attestation]) do
      {:ok, %Command.AuthorizeInspected{command | attestation: attestation}}
    end
  end

  def command(%Command.SettleInvocation{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :inv, :outcome, :resolution], []),
         :ok <- opaque(command.inv, [:inv]),
         :ok <- enum(command.outcome, @outcomes, [:outcome]),
         {:ok, resolution} <- optional_resolution(command.resolution, [:resolution]) do
      {:ok, %Command.SettleInvocation{command | resolution: resolution}}
    end
  end

  def command(%Command.CrossOutput{} = command) do
    with :ok <- exact_keys(command, [:__struct__, :input], []),
         {:ok, input} <- cross_input(command.input, [:input]) do
      {:ok, %Command.CrossOutput{command | input: input}}
    end
  end

  def command(_command), do: boundary_error(:invalid_struct, [])

  @doc false
  for command_name <- @command_names do
    module =
      command_name
      |> Atom.to_string()
      |> Macro.camelize()
      |> then(&Module.concat(Command, &1))

    def command(%unquote(module){} = command, unquote(command_name)), do: command(command)
  end

  def command(_command, expected) when expected in @command_names do
    boundary_error(:invalid_struct, [])
  end

  @doc false
  def action(%Action.RegisterTool{} = action, path) do
    with :ok <- exact_keys(action, [:__struct__, :tool], path),
         :ok <- opaque(action.tool, path ++ [:tool]) do
      {:ok, action}
    end
  end

  def action(%Action.UnregisterTool{} = action, path) do
    with :ok <- exact_keys(action, [:__struct__, :tool], path),
         :ok <- opaque(action.tool, path ++ [:tool]) do
      {:ok, action}
    end
  end

  def action(%Action.Delegate{} = action, path) do
    with :ok <- exact_keys(action, [:__struct__, :grantor, :grantee], path),
         :ok <- opaque(action.grantor, path ++ [:grantor]),
         :ok <- opaque(action.grantee, path ++ [:grantee]) do
      {:ok, action}
    end
  end

  def action(%Action.GrantCapability{} = action, path) do
    with :ok <- exact_keys(action, [:__struct__, :parent, :child, :cap], path),
         :ok <- opaque(action.parent, path ++ [:parent]),
         :ok <- opaque(action.child, path ++ [:child]),
         :ok <- enum(action.cap, @capabilities, path ++ [:cap]) do
      {:ok, action}
    end
  end

  def action(%Action.GrantCrossing{} = action, path) do
    with :ok <-
           exact_keys(action, [:__struct__, :grantor, :agent, :assignment, :n], path),
         :ok <- opaque(action.grantor, path ++ [:grantor]),
         :ok <- opaque(action.agent, path ++ [:agent]),
         :ok <- opaque(action.assignment, path ++ [:assignment]),
         :ok <- u32(action.n, path ++ [:n]) do
      {:ok, action}
    end
  end

  def action(%Action.Revoke{} = action, path) do
    with :ok <- exact_keys(action, [:__struct__, :parent, :target], path),
         :ok <- opaque(action.parent, path ++ [:parent]),
         :ok <- opaque(action.target, path ++ [:target]) do
      {:ok, action}
    end
  end

  def action(%Action.CascadeRevoke{} = action, path) do
    with :ok <- exact_keys(action, [:__struct__, :child, :parent], path),
         :ok <- opaque(action.child, path ++ [:child]),
         :ok <- opaque(action.parent, path ++ [:parent]) do
      {:ok, action}
    end
  end

  def action(%Action.Ingest{} = action, path) do
    with :ok <-
           exact_keys(
             action,
             [:__struct__, :agent, :src, :pconf, :pinteg, :disposition],
             path
           ),
         :ok <- opaque(action.agent, path ++ [:agent]),
         :ok <- optional_opaque(action.src, path ++ [:src]),
         :ok <- enum(action.pconf, @conf_levels, path ++ [:pconf]),
         :ok <- enum(action.pinteg, @integ_levels, path ++ [:pinteg]),
         :ok <-
           enum(
             action.disposition,
             [:permitted, :blocked, :monitor_bypassed],
             path ++ [:disposition]
           ) do
      {:ok, action}
    end
  end

  def action(%Action.BeginInvocation{} = action, path) do
    with :ok <-
           exact_keys(
             action,
             [:__struct__, :agent, :inv, :tool, :verdict, :authorized],
             path
           ),
         :ok <- opaque(action.agent, path ++ [:agent]),
         :ok <- opaque(action.inv, path ++ [:inv]),
         :ok <- opaque(action.tool, path ++ [:tool]),
         :ok <- enum(action.verdict, [:allow, :inspection_required, :deny], path ++ [:verdict]),
         :ok <- boolean(action.authorized, path ++ [:authorized]) do
      {:ok, action}
    end
  end

  def action(%Action.AuthorizeInspected{} = action, path) do
    with :ok <-
           exact_keys(action, [:__struct__, :inv, :attestation, :admitted], path),
         :ok <- opaque(action.inv, path ++ [:inv]),
         :ok <- opaque(action.attestation, path ++ [:attestation]),
         :ok <- boolean(action.admitted, path ++ [:admitted]) do
      {:ok, action}
    end
  end

  def action(%Action.SettleInvocation{} = action, path) do
    with :ok <-
           exact_keys(
             action,
             [
               :__struct__,
               :inv,
               :agent,
               :disposition,
               :outcome,
               :clvl,
               :ilvl,
               :resolution
             ],
             path
           ),
         :ok <- opaque(action.inv, path ++ [:inv]),
         :ok <- opaque(action.agent, path ++ [:agent]),
         :ok <-
           enum(
             action.disposition,
             [:permitted, :blocked, :monitor_bypassed],
             path ++ [:disposition]
           ),
         :ok <- enum(action.outcome, @outcomes, path ++ [:outcome]),
         :ok <- enum(action.clvl, @conf_levels, path ++ [:clvl]),
         :ok <- enum(action.ilvl, @integ_levels, path ++ [:ilvl]),
         :ok <- optional_opaque(action.resolution, path ++ [:resolution]) do
      {:ok, action}
    end
  end

  def action(%Action.CrossOutput{} = action, path) do
    with :ok <-
           exact_keys(
             action,
             [:__struct__, :src, :rcv, :crossing, :branch, :disposition],
             path
           ),
         :ok <- opaque(action.src, path ++ [:src]),
         :ok <- opaque(action.rcv, path ++ [:rcv]),
         :ok <- opaque(action.crossing, path ++ [:crossing]),
         :ok <- enum(action.branch, [:endorsed, :unendorsed, :fail], path ++ [:branch]),
         :ok <-
           enum(
             action.disposition,
             [:permitted, :blocked, :monitor_bypassed],
             path ++ [:disposition]
           ) do
      {:ok, action}
    end
  end

  def action(_action, path), do: boundary_error(:invalid_struct, path)

  @doc false
  def quarantine_resolution(%Command.SettleInvocation{} = command) do
    with {:ok, normalized} <- command(command, :settle_invocation),
         :ok <- enum(normalized.outcome, [:success, :failure], [:outcome]) do
      {:ok, normalized}
    end
  end

  def quarantine_resolution(_command), do: boundary_error(:invalid_struct, [])

  defp policy(%Types.ActionPolicySnapshot{} = policy, path) do
    with :ok <-
           exact_keys(
             policy,
             [
               :__struct__,
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
             path
           ),
         :ok <- opaque(policy.tool, path ++ [:tool]),
         {:ok, required_caps} <-
           set(
             policy.required_caps,
             @capabilities,
             Limits.max_capabilities(),
             path ++ [:required_caps]
           ),
         :ok <- enum(policy.conf_clearance, @conf_levels, path ++ [:conf_clearance]),
         :ok <- enum(policy.integ_floor, @integ_levels, path ++ [:integ_floor]),
         :ok <- enum(policy.integ_inspect, @integ_levels, path ++ [:integ_inspect]),
         :ok <- enum(policy.output_conf, @conf_levels, path ++ [:output_conf]),
         :ok <- enum(policy.output_integ, @integ_levels, path ++ [:output_integ]),
         {:ok, declared_egress} <-
           set(
             policy.declared_egress,
             @egress_kinds,
             Limits.max_egress_kinds(),
             path ++ [:declared_egress]
           ),
         :ok <- opaque(policy.policy_digest, path ++ [:policy_digest]) do
      {:ok,
       %Types.ActionPolicySnapshot{
         policy
         | required_caps: required_caps,
           declared_egress: declared_egress
       }}
    end
  end

  defp policy(_policy, path), do: boundary_error(:invalid_struct, path)

  defp inspection(%Types.InspectionAttestation{} = attestation, path) do
    with :ok <-
           exact_keys(
             attestation,
             [:__struct__, :id, :inv, :challenge, :args_hash, :policy_digest, :positive],
             path
           ),
         :ok <- opaque(attestation.id, path ++ [:id]),
         :ok <- opaque(attestation.inv, path ++ [:inv]),
         :ok <- opaque(attestation.challenge, path ++ [:challenge]),
         :ok <- opaque(attestation.args_hash, path ++ [:args_hash]),
         :ok <- opaque(attestation.policy_digest, path ++ [:policy_digest]),
         :ok <- boolean(attestation.positive, path ++ [:positive]) do
      {:ok, attestation}
    end
  end

  defp inspection(_attestation, path), do: boundary_error(:invalid_struct, path)

  defp optional_resolution(nil, _path), do: {:ok, nil}
  defp optional_resolution(value, path), do: resolution(value, path)

  defp resolution(%Types.ResolutionAttestation{} = resolution, path) do
    with :ok <- exact_keys(resolution, [:__struct__, :id, :inv, :outcome], path),
         :ok <- opaque(resolution.id, path ++ [:id]),
         :ok <- opaque(resolution.inv, path ++ [:inv]),
         :ok <- enum(resolution.outcome, @outcomes, path ++ [:outcome]) do
      {:ok, resolution}
    end
  end

  defp resolution(_resolution, path), do: boundary_error(:invalid_struct, path)

  defp cross_input(%Types.CrossInput{} = input, path) do
    with :ok <-
           exact_keys(
             input,
             [
               :__struct__,
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
             path
           ),
         :ok <- opaque(input.src, path ++ [:src]),
         :ok <- opaque(input.rcv, path ++ [:rcv]),
         :ok <- opaque(input.crossing, path ++ [:crossing]),
         :ok <- opaque(input.output_hash, path ++ [:output_hash]),
         :ok <- opaque(input.descriptor, path ++ [:descriptor]),
         :ok <- enum(input.fallback, [:fail, :release_unendorsed], path ++ [:fallback]),
         :ok <- enum(input.t_integ, @integ_levels, path ++ [:t_integ]),
         :ok <- optional_enum(input.t_conf, @conf_levels, path ++ [:t_conf]),
         :ok <- opaque(input.assignment, path ++ [:assignment]),
         {:ok, evidence} <- optional_evidence(input.evidence, path ++ [:evidence]),
         :ok <- enum(input.released_conf, @conf_levels, path ++ [:released_conf]),
         :ok <- enum(input.released_integ, @integ_levels, path ++ [:released_integ]) do
      {:ok, %Types.CrossInput{input | evidence: evidence}}
    end
  end

  defp cross_input(_input, path), do: boundary_error(:invalid_struct, path)

  defp optional_evidence(nil, _path), do: {:ok, nil}
  defp optional_evidence(value, path), do: evidence(value, path)

  defp evidence(%Types.ConformanceAttestation{} = evidence, path) do
    with :ok <-
           exact_keys(
             evidence,
             [:__struct__, :id, :output, :src, :rcv, :descriptor, :assignment, :positive],
             path
           ),
         :ok <- opaque(evidence.id, path ++ [:id]),
         :ok <- opaque(evidence.output, path ++ [:output]),
         :ok <- opaque(evidence.src, path ++ [:src]),
         :ok <- opaque(evidence.rcv, path ++ [:rcv]),
         :ok <- opaque(evidence.descriptor, path ++ [:descriptor]),
         :ok <- opaque(evidence.assignment, path ++ [:assignment]),
         :ok <- boolean(evidence.positive, path ++ [:positive]) do
      {:ok, evidence}
    end
  end

  defp evidence(_evidence, path), do: boundary_error(:invalid_struct, path)

  defp ceiling(value, path) when is_map(value) do
    with :ok <- exact_keys(value, @egress_kinds, path) do
      case Enum.find(@egress_kinds, &(value[&1] not in [nil | @conf_levels])) do
        nil -> :ok
        kind -> boundary_error(:unknown_enum, path ++ [kind])
      end
    end
  end

  defp ceiling(_value, path), do: boundary_error(:invalid_type, path)

  defp history(value), do: history(value, 0, nil, 0, [])

  defp history([], index, last_digest, _content, normalized) do
    {:ok, Enum.reverse(normalized), index, last_digest}
  end

  defp history([envelope | tail], index, last_digest, content, normalized) do
    with :ok <- checked_recovery_count(index) do
      validate_history_envelope(envelope, tail, index, last_digest, content, normalized)
    end
  end

  defp history(_improper, index, _last_digest, _content, _normalized) do
    boundary_error(:invalid_type, [], index)
  end

  defp validate_history_envelope(envelope, tail, index, last_digest, content, normalized) do
    with {:ok, normalized_envelope, envelope_content} <- envelope(envelope, index),
         :ok <- declared_sequence(normalized_envelope.sequence, index),
         :ok <- predecessor(normalized_envelope.previous_digest, last_digest, index),
         {:ok, next_content} <-
           checked_replay_content(content, envelope_content) |> put_index(index) do
      history(
        tail,
        index + 1,
        normalized_envelope.digest,
        next_content,
        [normalized_envelope | normalized]
      )
    end
  end

  defp envelope(%Envelope{} = envelope, index) do
    result =
      with :ok <-
             exact_keys(
               envelope,
               [
                 :__struct__,
                 :version,
                 :sequence,
                 :previous_digest,
                 :digest,
                 :command,
                 :action
               ],
               []
             ),
           :ok <- recovery_version(envelope.version, index),
           :ok <- envelope_sequence(envelope.sequence),
           :ok <- digest(envelope.previous_digest, [:previous_digest]),
           :ok <- digest(envelope.digest, [:digest]),
           {:ok, normalized_command} <- envelope_command(envelope.command),
           {:ok, normalized_action} <- action(envelope.action, [:action]),
           {:ok, content} <- envelope_content(normalized_command, normalized_action) do
        {:ok,
         %Envelope{
           envelope
           | command: normalized_command,
             action: normalized_action
         }, content}
      end

    put_index(result, index)
  end

  defp envelope(_envelope, index), do: boundary_error(:invalid_struct, [], index)

  defp envelope_command(command) do
    case command(command) do
      {:ok, normalized} -> {:ok, normalized}
      {:error, %Error{} = error} -> {:error, %Error{error | path: [:command | error.path]}}
    end
  end

  defp chain(%Chain{} = chain) do
    with :ok <- exact_keys(chain, [:__struct__, :version, :sequence, :head], []),
         :ok <- recovery_version(chain.version, nil),
         :ok <- chain_sequence(chain.sequence),
         :ok <- digest(chain.head, [:head]) do
      {:ok, chain}
    end
  end

  defp chain(_chain), do: boundary_error(:invalid_struct, [])

  defp declared_sequence(sequence, index) when sequence == index + 1, do: :ok

  defp declared_sequence(_sequence, index) do
    {:error, %Error{class: :recovery, reason: :sequence_mismatch, index: index}}
  end

  defp predecessor(_previous_digest, nil, 0), do: :ok
  defp predecessor(previous_digest, previous_digest, _index), do: :ok

  defp predecessor(_previous_digest, _expected, index) do
    {:error, %Error{class: :recovery, reason: :previous_digest_mismatch, index: index}}
  end

  defp envelope_content(command, action) do
    with {:ok, content} <- checked_replay_content(0, 64),
         {:ok, content} <- checked_replay_content(content, command_content(command)) do
      checked_replay_content(content, action_content(action))
    end
  end

  defp command_content(%Command.RegisterTool{tool: tool}), do: bytes(tool)
  defp command_content(%Command.UnregisterTool{tool: tool}), do: bytes(tool)

  defp command_content(%Command.Delegate{grantor: grantor, grantee: grantee}) do
    bytes(grantor) + bytes(grantee)
  end

  defp command_content(%Command.GrantCapability{parent: parent, child: child}) do
    bytes(parent) + bytes(child)
  end

  defp command_content(%Command.GrantCrossing{} = command) do
    bytes(command.grantor) + bytes(command.agent) + bytes(command.assignment)
  end

  defp command_content(%Command.Revoke{parent: parent, target: target}) do
    bytes(parent) + bytes(target)
  end

  defp command_content(%Command.CascadeRevoke{child: child, parent: parent}) do
    bytes(child) + bytes(parent)
  end

  defp command_content(%Command.Ingest{agent: agent, src: src}) do
    bytes(agent) + optional_bytes(src)
  end

  defp command_content(%Command.BeginInvocation{} = command) do
    bytes(command.agent) +
      bytes(command.inv) +
      bytes(command.challenge) +
      policy_content(command.policy) +
      bytes(command.args_hash)
  end

  defp command_content(%Command.AuthorizeInspected{} = command) do
    bytes(command.inv) + inspection_content(command.attestation)
  end

  defp command_content(%Command.SettleInvocation{} = command) do
    bytes(command.inv) + resolution_content(command.resolution)
  end

  defp command_content(%Command.CrossOutput{input: input}), do: cross_content(input)

  defp action_content(%Action.RegisterTool{tool: tool}), do: bytes(tool)
  defp action_content(%Action.UnregisterTool{tool: tool}), do: bytes(tool)

  defp action_content(%Action.Delegate{grantor: grantor, grantee: grantee}) do
    bytes(grantor) + bytes(grantee)
  end

  defp action_content(%Action.GrantCapability{parent: parent, child: child}) do
    bytes(parent) + bytes(child)
  end

  defp action_content(%Action.GrantCrossing{} = action) do
    bytes(action.grantor) + bytes(action.agent) + bytes(action.assignment)
  end

  defp action_content(%Action.Revoke{parent: parent, target: target}) do
    bytes(parent) + bytes(target)
  end

  defp action_content(%Action.CascadeRevoke{child: child, parent: parent}) do
    bytes(child) + bytes(parent)
  end

  defp action_content(%Action.Ingest{agent: agent, src: src}) do
    bytes(agent) + optional_bytes(src)
  end

  defp action_content(%Action.BeginInvocation{} = action) do
    bytes(action.agent) + bytes(action.inv) + bytes(action.tool)
  end

  defp action_content(%Action.AuthorizeInspected{} = action) do
    bytes(action.inv) + bytes(action.attestation)
  end

  defp action_content(%Action.SettleInvocation{} = action) do
    bytes(action.inv) + bytes(action.agent) + optional_bytes(action.resolution)
  end

  defp action_content(%Action.CrossOutput{} = action) do
    bytes(action.src) + bytes(action.rcv) + bytes(action.crossing)
  end

  defp policy_content(policy) do
    bytes(policy.tool) + bytes(policy.policy_digest)
  end

  defp inspection_content(attestation) do
    bytes(attestation.id) +
      bytes(attestation.inv) +
      bytes(attestation.challenge) +
      bytes(attestation.args_hash) +
      bytes(attestation.policy_digest)
  end

  defp resolution_content(nil), do: 0

  defp resolution_content(resolution) do
    bytes(resolution.id) + bytes(resolution.inv)
  end

  defp cross_content(input) do
    bytes(input.src) +
      bytes(input.rcv) +
      bytes(input.crossing) +
      bytes(input.output_hash) +
      bytes(input.descriptor) +
      bytes(input.assignment) + evidence_content(input.evidence)
  end

  defp evidence_content(nil), do: 0

  defp evidence_content(evidence) do
    bytes(evidence.id) +
      bytes(evidence.output) +
      bytes(evidence.src) +
      bytes(evidence.rcv) +
      bytes(evidence.descriptor) +
      bytes(evidence.assignment)
  end

  defp bytes(value), do: byte_size(value)
  defp optional_bytes(nil), do: 0
  defp optional_bytes(value), do: bytes(value)

  defp put_index({:error, %Error{} = error}, index), do: {:error, %Error{error | index: index}}
  defp put_index(result, _index), do: result

  defp recovery_version(5, _index), do: :ok

  defp recovery_version(_version, index) do
    {:error, %Error{class: :recovery, reason: :invalid_version, index: index}}
  end

  defp envelope_sequence(value) when is_integer(value) and value > 0 do
    if value <= Limits.max_accepted_sequence() do
      :ok
    else
      boundary_error(:integer_out_of_range, [:sequence])
    end
  end

  defp envelope_sequence(_value), do: boundary_error(:integer_out_of_range, [:sequence])

  defp chain_sequence(value) when is_integer(value) and value >= 0 do
    if value <= Limits.max_accepted_sequence() do
      :ok
    else
      boundary_error(:integer_out_of_range, [:sequence])
    end
  end

  defp chain_sequence(_value), do: boundary_error(:integer_out_of_range, [:sequence])

  defp expected_sequence(sequence, sequence), do: :ok

  defp expected_sequence(_declared, _actual) do
    {:error, %Error{class: :recovery, reason: :sequence_mismatch}}
  end

  defp expected_head(_head, nil), do: :ok
  defp expected_head(head, head), do: :ok

  defp expected_head(_head, _last_digest) do
    {:error, %Error{class: :recovery, reason: :final_anchor_mismatch}}
  end

  defp digest(value, _path) when is_binary(value) and byte_size(value) == 32, do: :ok
  defp digest(_value, path), do: boundary_error(:invalid_type, path)

  defp optional_opaque(nil, _path), do: :ok
  defp optional_opaque(value, path), do: opaque(value, path)

  defp opaque(value, path) when is_binary(value) do
    cond do
      value == "" -> boundary_error(:empty_value, path)
      byte_size(value) > Limits.max_opaque_utf8_bytes() -> boundary_error(:value_too_large, path)
      not String.valid?(value) -> boundary_error(:invalid_utf8, path)
      true -> :ok
    end
  end

  defp opaque(_value, path), do: boundary_error(:invalid_type, path)

  defp optional_enum(nil, _allowed, _path), do: :ok
  defp optional_enum(value, allowed, path), do: enum(value, allowed, path)

  defp enum(value, allowed, path) do
    if value in allowed, do: :ok, else: boundary_error(:unknown_enum, path)
  end

  defp boolean(value, _path) when is_boolean(value), do: :ok
  defp boolean(_value, path), do: boundary_error(:invalid_type, path)

  defp u32(value, _path) when is_integer(value) and value >= 0 and value <= @u32_max, do: :ok
  defp u32(_value, path), do: boundary_error(:integer_out_of_range, path)

  defp set(value, allowed, maximum, path) do
    case bounded_proper_list(value, maximum) do
      :proper ->
        with :ok <- set_members(value, allowed, path),
             false <- length(Enum.uniq(value)) != length(value) do
          order = allowed |> Enum.with_index() |> Map.new()
          {:ok, Enum.sort_by(value, &Map.fetch!(order, &1))}
        else
          true -> boundary_error(:duplicate_value, path)
          {:error, %Error{}} = error -> error
        end

      :over_limit ->
        boundary_error(:capacity_exceeded, path)

      :improper ->
        boundary_error(:invalid_type, path)
    end
  end

  defp bounded_proper_list(value, maximum), do: bounded_proper_list(value, maximum, 0)

  defp bounded_proper_list([], _maximum, _count), do: :proper
  defp bounded_proper_list([_head | _tail], maximum, maximum), do: :over_limit

  defp bounded_proper_list([_head | tail], maximum, count),
    do: bounded_proper_list(tail, maximum, count + 1)

  defp bounded_proper_list(_value, _maximum, _count), do: :improper

  defp set_members(value, allowed, path) do
    value
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn {member, index}, :ok ->
      case enum(member, allowed, path ++ [index]) do
        :ok -> {:cont, :ok}
        error -> {:halt, error}
      end
    end)
  end

  defp exact_keys(value, expected, path) do
    if map_size(value) == length(expected) and Enum.all?(expected, &Map.has_key?(value, &1)) do
      :ok
    else
      boundary_error(:invalid_keys, path)
    end
  end

  defp boundary_error(reason, path, index \\ nil) do
    {:error, %Error{class: :boundary, reason: reason, path: path, index: index}}
  end
end
