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
    {:invoke_start, ["a1", "read_file", "inv-1", true, %{"read_file" => true}]},
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
          issuer: "trusted"
        }
      },
      flow_policy: %{{:public, :network_external} => :allow},
      flow_overrides: [],
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
             Instance.invoke_start(h, "a1", "read_file", "inv-1", true, %{"read_file" => true})

    assert {:ok, 6, _} = Instance.invoke_complete(h, "a1", "inv-1", true)

    s = Instance.state(h)
    assert :sensitive in Map.fetch!(s.taint_levels, "a1")
    assert Instance.seq(h) == 6
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
    {:ok, h} = Instance.recover(bg(), @recover_log)
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
             Instance.recover(bg(), corrupt)
  end

  test "recover of an empty log yields a fresh instance at seq 0" do
    assert {:ok, h} = Instance.recover(bg(), [])
    assert Instance.seq(h) == 0
    assert Instance.state(h) == Instance.state(Instance.new(bg()))
  end

  test "recover aborts on an entry naming an unknown/non-transition function" do
    log = [{:register_tool, ["read_file"]}, {:bogus_fun, []}]

    assert {:error, %{index: 1, entry: {:bogus_fun, []}, reason: :unknown_transition}} =
             Instance.recover(bg(), log)
  end

  test "recover aborts on an entry naming a non-transition Instance function" do
    log = [{:register_tool, ["read_file"]}, {:state, []}]

    assert {:error, %{index: 1, entry: {:state, []}, reason: :unknown_transition}} =
             Instance.recover(bg(), log)
  end

  test "instance explain on live state matches offline explain on the projected snapshot" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "read_file")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")

    snapshot = Instance.state(h)
    gate = %{"read_file" => true}

    live = Instance.explain_invoke(h, "a1", "read_file", "inv-1", true, gate)

    offline =
      ExArgus.Explain.explain_invoke(snapshot, bg(), "a1", "read_file", "inv-1", true, gate)

    assert live == offline
    assert Instance.denied?(live) == (live.verdict != nil)
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
          {:invoke_start, [g, "read_file", "inv-#{g}", true, %{"read_file" => true}]}
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

      offline_outcomes = ExArgus.Replay.run(log, bg())

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
