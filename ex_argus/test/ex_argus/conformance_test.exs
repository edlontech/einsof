defmodule ExArgus.ConformanceTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias ExArgus.Offline
  alias ExArgus.Kernel.Background
  alias ExArgus.Kernel.State

  defp bg do
    %Background{
      tools: %{
        "t" => %{
          capabilities: [],
          egress: [],
          conf_floor: :internal,
          output_bounded: false,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  # A small grammar of always-attemptable actions over a tiny fixed namespace. Each is applied
  # and, if it succeeds, the new state is kept; on `{:error, _}` the state is unchanged. The
  # point is to reach many distinct states, not to force success.
  defp gen_action do
    agents = ["a1", "a2"]
    invs = ["i1", "i2"]

    StreamData.one_of([
      StreamData.constant({:register_tool, "t"}),
      StreamData.bind(StreamData.member_of(agents), fn a ->
        StreamData.constant({:delegate, "root", a})
      end),
      StreamData.bind(StreamData.member_of(agents), fn a ->
        StreamData.bind(StreamData.member_of(invs), fn i ->
          StreamData.constant({:invoke_start, a, "t", i})
        end)
      end),
      StreamData.bind(StreamData.member_of(agents), fn a ->
        StreamData.bind(StreamData.member_of(invs), fn i ->
          StreamData.constant({:invoke_complete, a, i})
        end)
      end),
      StreamData.bind(StreamData.member_of(agents), fn a ->
        StreamData.constant({:revoke, "root", a})
      end)
    ])
  end

  defp apply_action(state, bg, {:register_tool, t}), do: Offline.register_tool(state, bg, t)
  defp apply_action(state, bg, {:delegate, g, c}), do: Offline.delegate(state, bg, g, c)

  defp apply_action(state, bg, {:invoke_start, a, t, i}),
    do: Offline.invoke_start(state, bg, a, t, i, true, %{i => true}, [])

  defp apply_action(state, bg, {:invoke_complete, a, i}),
    do: Offline.invoke_complete(state, bg, a, i, true)

  defp apply_action(state, bg, {:revoke, p, t}), do: Offline.revoke(state, bg, p, t)

  defp step(state, bg, action) do
    case apply_action(state, bg, action) do
      {:ok, next, _action} -> next
      {:error, _reason} -> state
    end
  end

  defp assert_invariants(%State{} = s) do
    # 1. root is always active and never has a parent.
    assert "root" in s.agent_active
    refute Map.has_key?(s.agent_parent, "root")

    # 2. no agent is its own parent.
    for {child, parent} <- s.agent_parent, do: assert(child != parent)

    # 3. every in-flight invocation has a tool binding.
    for {_agent, invs} <- s.in_flight, inv <- invs do
      assert Map.has_key?(s.invocation_tool, inv)
    end

    # 4. taint levels are valid atoms.
    for {_agent, levels} <- s.taint_levels, level <- levels do
      assert level in [:public, :internal, :sensitive, :restricted]
    end

    # 5. budgets are integers within the meter range (absence == capacity == 16).
    for {_agent, budget} <- s.agent_budget do
      assert is_integer(budget) and budget in 0..16
    end
  end

  property "random action sequences preserve the structural safety invariants" do
    bg = bg()

    check all(actions <- StreamData.list_of(gen_action(), max_length: 25)) do
      final = Enum.reduce(actions, Offline.initial_state(), &step(&2, bg, &1))
      assert_invariants(final)
    end
  end

  property "every transition returns {:ok, state, action} or {:error, atom}" do
    bg = bg()

    check all(action <- gen_action()) do
      case apply_action(Offline.initial_state(), bg, action) do
        {:ok, %State{}, tuple} -> assert is_tuple(tuple)
        {:error, reason} -> assert is_atom(reason)
      end
    end
  end

  # CHECK 2b's content-gate vouch re-examines an IN-FLIGHT invocation's stored egress against
  # a NEW invocation's tool floor -- the vouch must be keyed by the in-flight invocation id,
  # never by the tool id (the V2 shape). read_file's floor (sensitive) against send_email's
  # stored network_external egress sits in the inspect band (allow public, inspect sensitive),
  # so admission depends entirely on the flight invocation's content-gate verdict.
  defp check2b_bg do
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
        },
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
      inspect_ceiling: %{network_external: :sensitive},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  defp check2b_setup do
    bg = check2b_bg()
    s = Offline.initial_state()
    {:ok, s, _} = Offline.register_tool(s, bg, "read_file")
    {:ok, s, _} = Offline.register_tool(s, bg, "send_email")
    {:ok, s, _} = Offline.delegate(s, bg, "root", "a1")
    {:ok, s, _} = Offline.grant_capability(s, bg, "root", "a1", :filesystem_read)
    {:ok, s, _} = Offline.grant_capability(s, bg, "root", "a1", :network_egress)

    {:ok, s, _} =
      Offline.invoke_start(s, bg, "a1", "send_email", "email-inv", true, %{"email-inv" => true}, [
        :network_external
      ])

    {s, bg}
  end

  test "content_gate_targets for the pending invoke_start includes both the new and the in-flight invocation id" do
    {s, _bg} = check2b_setup()

    assert {"a1", invs} =
             Offline.content_gate_targets(s, {:invoke_start, "a1", "read_file", "new-inv"})

    assert Enum.sort(invs) == Enum.sort(["new-inv", "email-inv"])
  end

  test "CHECK 2b vouch admits the flow when keyed by the in-flight invocation id" do
    {s, bg} = check2b_setup()

    assert {:ok, _, {:invoke_start, "a1", "read_file", "new-inv"}} =
             Offline.invoke_start(
               s,
               bg,
               "a1",
               "read_file",
               "new-inv",
               true,
               %{
                 "email-inv" => true
               },
               []
             )
  end

  test "CHECK 2b vouch keyed by the tool id (the V2 shape) fails to rescue the flow" do
    {s, bg} = check2b_setup()

    assert {:error, :flow_gate_blocked} =
             Offline.invoke_start(
               s,
               bg,
               "a1",
               "read_file",
               "new-inv",
               true,
               %{
                 "send_email" => true
               },
               []
             )
  end

  test "an empty content-gate map fails closed on a CHECK 2b vouch requirement" do
    {s, bg} = check2b_setup()

    assert {:error, :flow_gate_blocked} =
             Offline.invoke_start(s, bg, "a1", "read_file", "new-inv", true, %{}, [])
  end
end
