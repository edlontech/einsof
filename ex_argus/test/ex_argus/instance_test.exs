defmodule ExArgus.InstanceTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias ExArgus.Instance
  alias ExArgus.Kernel.Background

  @agreement_setup [
    {:register_tool, ["read_file"]},
    {:delegate, ["root", "a1"]},
    {:delegate, ["root", "a2"]},
    {:grant_capability, ["root", "a1", :filesystem_read]},
    {:grant_capability, ["root", "a1", :declassify]},
    {:grant_capability, ["root", "a2", :filesystem_read]},
    {:grant_capability, ["root", "a2", :declassify]}
  ]

  @recover_log [
    {:register_tool, ["read_file"]},
    {:delegate, ["root", "a1"]},
    {:grant_capability, ["root", "a1", :filesystem_read]},
    {:grant_capability, ["root", "a1", :declassify]},
    {:invoke_start, ["a1", "read_file", "inv-1", true, %{"inv-1" => true}, []]},
    {:invoke_complete, ["a1", "inv-1", true]}
  ]

  defp bg do
    %Background{
      tools: %{
        "read_file" => %{
          capabilities: [:filesystem_read],
          egress: [],
          conf_floor: :sensitive,
          output_bounded: false,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{network_external: :public},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "new -> transitions -> projection threads a live trajectory" do
    h = Instance.new(bg())
    assert Instance.seq(h) == 0

    assert {:ok, 1, {:register_tool, "read_file"}} = Instance.register_tool(h, "read_file")
    assert {:ok, 2, {:delegate, "root", "a1"}} = Instance.delegate(h, "root", "a1")
    assert {:ok, 3, _} = Instance.grant_capability(h, "root", "a1", :filesystem_read)
    assert {:ok, 4, _} = Instance.grant_capability(h, "root", "a1", :declassify)

    assert {:ok, 5, _} =
             Instance.invoke_start(h, "a1", "read_file", "inv-1", true, %{"inv-1" => true}, [])

    assert {:ok, 6, _} = Instance.invoke_complete(h, "a1", "inv-1", true)

    s = Instance.state(h)
    assert :sensitive in Map.fetch!(s.taint_levels, "a1")
    assert Instance.seq(h) == 6
  end

  test "invoke_start/6 threads an {authorized?, attested} tuple from attest/4" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "read_file")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_read)

    assert {:ok, _, {:invoke_start, "a1", "read_file", "inv-1"}} =
             Instance.invoke_start(h, "a1", "read_file", "inv-1", {true, []}, %{"inv-1" => true})

    assert "inv-1" in Map.fetch!(Instance.state(h).in_flight, "a1")
  end

  test "invoke_start/6 propagates a denied authorized? through the underlying call" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "read_file")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_read)

    assert {:error, :authorizer_denied} =
             Instance.invoke_start(h, "a1", "read_file", "inv-1", {false, []}, %{
               "inv-1" => true
             })
  end

  test "a refused transition leaves state and seq unchanged" do
    h = Instance.new(bg())
    {:ok, 1, _} = Instance.register_tool(h, "read_file")
    before = Instance.state(h)

    assert {:error, :tool_already_registered} = Instance.register_tool(h, "read_file")

    assert Instance.state(h) == before
    assert Instance.seq(h) == 1
  end

  test "seq increments only on accepted transitions and is dense" do
    h = Instance.new(bg())
    {:ok, 1, _} = Instance.register_tool(h, "read_file")
    {:error, :tool_already_registered} = Instance.register_tool(h, "read_file")
    {:ok, 2, _} = Instance.delegate(h, "root", "a1")
    assert Instance.seq(h) == 2
  end

  test "recover replays an accepted-call log to an identical projection + dense seq" do
    {:ok, h} = Instance.recover(bg(), [ExArgus.log_header() | @recover_log])
    assert Instance.seq(h) == length(@recover_log)

    live = Instance.new(bg())

    Enum.each(@recover_log, fn {fun, args} ->
      {:ok, _seq, _action} = apply(Instance, fun, [live | args])
    end)

    assert Instance.state(h) == Instance.state(live)
  end

  test "recover aborts strictly on the first refused entry, returning index + reason" do
    corrupt = List.insert_at(@recover_log, 1, {:register_tool, ["read_file"]})

    assert {:error,
            %{index: 1, entry: {:register_tool, ["read_file"]}, reason: :tool_already_registered}} =
             Instance.recover(bg(), [ExArgus.log_header() | corrupt])
  end

  test "recover of an empty log yields a fresh instance at seq 0" do
    assert {:ok, h} = Instance.recover(bg(), [ExArgus.log_header()])
    assert Instance.seq(h) == 0
    assert Instance.state(h) == Instance.state(Instance.new(bg()))
  end

  test "recover aborts on an entry naming an unknown/non-transition function" do
    log = [{:register_tool, ["read_file"]}, {:bogus_fun, []}]

    assert {:error, %{index: 1, entry: {:bogus_fun, []}, reason: :unknown_transition}} =
             Instance.recover(bg(), [ExArgus.log_header() | log])
  end

  test "recover aborts on an entry naming a non-transition Instance function" do
    log = [{:register_tool, ["read_file"]}, {:state, []}]

    assert {:error, %{index: 1, entry: {:state, []}, reason: :unknown_transition}} =
             Instance.recover(bg(), [ExArgus.log_header() | log])
  end

  test "recover rejects a headerless log without creating an instance or replaying any entry" do
    assert {:error, %{reason: :state_version_mismatch}} = Instance.recover(bg(), @recover_log)
  end

  test "recover rejects a log stamped for a prior state version" do
    log = [{:state_version, 3} | @recover_log]
    assert {:error, %{reason: :state_version_mismatch}} = Instance.recover(bg(), log)
  end

  test "recover succeeds on a stamped-4 log containing the two new V3 transitions" do
    log = [
      ExArgus.log_header(),
      {:register_tool, ["read_file"]},
      {:delegate, ["root", "a1"]},
      {:sentinel_degrade_integrity, ["a1", :standard, %{}]},
      {:unregister_tool, ["read_file"]}
    ]

    assert {:ok, h} = Instance.recover(bg(), log)
    assert Instance.seq(h) == 4
    refute "read_file" in Instance.state(h).tool_registered
  end

  test "instance explain on live state matches offline explain on the projected snapshot" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "read_file")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")

    snapshot = Instance.state(h)
    gate = %{"inv-1" => true}

    live = Instance.explain_invoke(h, "a1", "read_file", "inv-1", true, gate, [])

    offline =
      ExArgus.Explain.explain_invoke(snapshot, bg(), "a1", "read_file", "inv-1", true, gate, [])

    assert live == offline
    assert Instance.denied?(live) == (live.verdict != nil)
  end

  test "instance explain_sentinel_degrade_integrity matches offline explain on the projection" do
    h = Instance.new(integ_bg())
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "delete_repo", "inv-1", true, %{"inv-1" => true}, [])

    snapshot = Instance.state(h)

    live = Instance.explain_sentinel_degrade_integrity(h, "a1", :untrusted, %{})

    offline =
      ExArgus.Explain.explain_sentinel_degrade_integrity(
        snapshot,
        integ_bg(),
        "a1",
        :untrusted,
        %{}
      )

    assert live == offline
    assert live.verdict == :integrity_floor_denied
  end

  test "instance explain_return_endorsed and explain_grant_override match offline explain" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :declassify)

    snapshot = Instance.state(h)

    live = Instance.explain_return_endorsed(h, "a1", "root", true, :public, :attested)

    offline =
      ExArgus.Explain.explain_return_endorsed(
        snapshot,
        bg(),
        "a1",
        "root",
        true,
        :public,
        :attested
      )

    assert live == offline
    assert live.verdict == nil

    live_override = Instance.explain_grant_override(h, "root", "a1", :sensitive)

    offline_override =
      ExArgus.Explain.explain_grant_override(snapshot, bg(), "root", "a1", :sensitive)

    assert live_override == offline_override
    assert live_override.verdict == nil
  end

  test "invoke_start with a reused invocation id returns :invocation_exists" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "read_file")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_read)

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "read_file", "inv-1", true, %{"inv-1" => true}, [])

    assert {:error, :invocation_exists} =
             Instance.invoke_start(h, "a1", "read_file", "inv-1", true, %{"inv-1" => true}, [])
  end

  test "unregister_tool removes a registered, idle tool" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "read_file")

    assert {:ok, _, {:unregister_tool, "read_file"}} = Instance.unregister_tool(h, "read_file")
    refute "read_file" in Instance.state(h).tool_registered
  end

  test "unregister_tool is denied with :tool_in_flight while the tool has an in-flight invocation" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "read_file")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_read)

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "read_file", "inv-1", true, %{"inv-1" => true}, [])

    assert {:error, :tool_in_flight} = Instance.unregister_tool(h, "read_file")
  end

  test "sentinel_degrade_integrity degrades an idle agent's held integrity" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.delegate(h, "root", "a1")

    assert {:ok, _, {:sentinel_degrade_integrity, "a1", :standard}} =
             Instance.sentinel_degrade_integrity(h, "a1", :standard, %{})

    assert :standard in Map.fetch!(Instance.state(h).integ_levels, "a1")
  end

  test "sentinel_degrade_integrity is denied when an in-flight tool's floor would be violated" do
    h = Instance.new(integ_bg())
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "delete_repo", "inv-1", true, %{"inv-1" => true}, [])

    # "delete_repo"'s integ_floor and integ_inspect_floor are both :trusted; degrading a1 to
    # :untrusted sits below both, so no gate vouch could rescue it.
    assert {:error, :integrity_floor_denied} =
             Instance.sentinel_degrade_integrity(h, "a1", :untrusted, %{})
  end

  defp integ_bg do
    %Background{
      tools: %{
        "delete_repo" => %{
          capabilities: [],
          egress: [],
          conf_floor: :public,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :trusted,
          integ_inspect_floor: :trusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  defp offline_decision({:ok, _state, action}), do: {:ok, action}
  defp offline_decision({:error, reason}), do: {:error, reason}
  defp instance_decision({:ok, _seq, action}), do: {:ok, action}
  defp instance_decision({:error, reason}), do: {:error, reason}

  defp entry_gen do
    agent = StreamData.member_of(["root", "a1", "a2"])

    StreamData.one_of([
      StreamData.constant({:register_tool, ["read_file"]}),
      StreamData.bind(agent, fn g -> StreamData.constant({:delegate, ["root", g]}) end),
      StreamData.bind(agent, fn g ->
        StreamData.constant({:grant_capability, ["root", g, :filesystem_read]})
      end),
      StreamData.bind(agent, fn g ->
        StreamData.constant({:grant_capability, ["root", g, :declassify]})
      end),
      StreamData.bind(agent, fn g ->
        StreamData.constant(
          {:invoke_start, [g, "read_file", "inv-#{g}", true, %{"inv-#{g}" => true}, []]}
        )
      end),
      StreamData.bind(agent, fn g ->
        StreamData.constant({:invoke_complete, [g, "inv-#{g}", true]})
      end),
      StreamData.bind(agent, fn g -> StreamData.constant({:revoke, ["root", g]}) end)
    ])
  end

  property "Instance and Offline agree on every decision and the final projection" do
    check all(tail <- StreamData.list_of(entry_gen(), max_length: 20)) do
      log = @agreement_setup ++ tail

      offline_outcomes = ExArgus.Replay.run([ExArgus.log_header() | log], bg())

      handle = Instance.new(bg())

      instance_outcomes =
        Enum.map(log, fn {fun, args} -> apply(Instance, fun, [handle | args]) end)

      assert Enum.map(offline_outcomes, &offline_decision/1) ==
               Enum.map(instance_outcomes, &instance_decision/1)

      offline_final =
        Enum.reduce(log, ExArgus.Offline.initial_state(), fn {fun, args}, st ->
          case apply(ExArgus.Offline, fun, [st, bg() | args]) do
            {:ok, ns, _a} -> ns
            {:error, _} -> st
          end
        end)

      assert offline_final == Instance.state(handle)
    end
  end

  defp flow_bg do
    %Background{
      tools: %{
        "send_email" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :public,
          output_bounded: false,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{network_external: :public},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "grant_override arms a flow override that rescues one denied invocation" do
    h = Instance.new(flow_bg())
    {:ok, _, _} = Instance.register_tool(h, "send_email")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "a1", :sensitive, %{})

    {:ok, _, _} = Instance.grant_override(h, "root", "a1", "send_email", :sensitive)

    assert {:ok, _, {:invoke_start, "a1", "send_email", _}} =
             Instance.invoke_start(h, "a1", "send_email", "inv-1", true, %{"inv-1" => true}, [
               :network_external
             ])

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "inv-1", true)

    assert {:error, :flow_gate_blocked} =
             Instance.invoke_start(h, "a1", "send_email", "inv-2", true, %{"inv-2" => true}, [
               :network_external
             ])
  end

  test "grant_override re-arm refused while target has in-flight invocation" do
    h = Instance.new(flow_bg())
    {:ok, _, _} = Instance.register_tool(h, "send_email")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.grant_override(h, "root", "a1", "send_email", :sensitive)
    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "a1", :sensitive, %{})

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "send_email", "inv-1", true, %{"inv-1" => true}, [
        :network_external
      ])

    assert {:error, :target_has_in_flight} =
             Instance.grant_override(h, "root", "a1", "send_email", :sensitive)
  end

  test "grant_override re-arm works after invoke_complete clears the flight" do
    h = Instance.new(flow_bg())
    {:ok, _, _} = Instance.register_tool(h, "send_email")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.grant_override(h, "root", "a1", "send_email", :sensitive)
    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "a1", :sensitive, %{})

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "send_email", "inv-1", true, %{"inv-1" => true}, [
        :network_external
      ])

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "inv-1", true)

    {:ok, _, _} = Instance.grant_override(h, "root", "a1", "send_email", :sensitive)

    assert {:ok, _, {:invoke_start, "a1", "send_email", _}} =
             Instance.invoke_start(h, "a1", "send_email", "inv-2", true, %{"inv-2" => true}, [
               :network_external
             ])
  end

  test "recovery replays a log containing grant_override and reproduces state" do
    recovery_log = [
      {:register_tool, ["send_email"]},
      {:delegate, ["root", "a1"]},
      {:grant_capability, ["root", "a1", :network_egress]},
      {:grant_override, ["root", "a1", "send_email", :sensitive]}
    ]

    {:ok, h} = Instance.recover(flow_bg(), [ExArgus.log_header() | recovery_log])
    assert Instance.seq(h) == length(recovery_log)

    live = Instance.new(flow_bg())

    Enum.each(recovery_log, fn {fun, args} ->
      {:ok, _seq, _action} = apply(Instance, fun, [live | args])
    end)

    assert Instance.state(h) == Instance.state(live)
  end

  test "concurrent transitions against one instance serialize: dense seq, no torn state" do
    h = Instance.new(bg())
    grantees = for i <- 1..50, do: "a#{i}"

    results =
      grantees
      |> Task.async_stream(fn g -> Instance.delegate(h, "root", g) end, max_concurrency: 16)
      |> Enum.map(fn {:ok, r} -> r end)

    assert Enum.all?(results, &match?({:ok, _seq, {:delegate, "root", _}}, &1))

    s = Instance.state(h)
    assert Enum.all?(grantees, &(&1 in s.agent_active))
    assert Instance.seq(h) == 50
    seqs = Enum.map(results, fn {:ok, seq, _} -> seq end)
    assert Enum.sort(seqs) == Enum.to_list(1..50)
  end
end
