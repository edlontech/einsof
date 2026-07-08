defmodule ExArgus.BudgetTest do
  @moduledoc """
  Behavior of the numeric declassification budget: weighted endorsement debit,
  `return_endorsed` conformance gating, `sentinel_credit_budget` saturation, and the
  no-debit-when-neither-crossing-dimension-helps rule. Budget is read from the projected state
  (`agent_budget`); absence == capacity == 16, EXCEPT `delegate` spawns every grantee with
  an explicit 0 entry (budget-zero children, design §5/§6) -- a fresh child must be credited
  via `sentinel_credit_budget` before it can afford any endorsement debit.
  """
  use ExUnit.Case, async: true

  alias ExArgus.Instance
  alias ExArgus.Kernel.Background

  # A bounded, conforming Sensitive tool (declass_weight 2), no capability/egress gates.
  defp bg do
    %Background{
      tools: %{
        "summarize" => %{
          capabilities: [],
          egress: [],
          conf_floor: :sensitive,
          output_bounded: true,
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

  defp budget(handle, agent), do: Map.get(Instance.state(handle).agent_budget, agent, 16)

  test "a bounded+conforming Sensitive endorsement debits 2 and adds no taint" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "summarize")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :declassify)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :credit_budget)
    {:ok, _, _} = Instance.sentinel_credit_budget(h, "a1", 16)

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "summarize", "inv-1", true, %{"inv-1" => true}, [])

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "inv-1", true)

    assert budget(h, "a1") == 14
    refute Map.has_key?(Instance.state(h).taint_levels, "a1")
  end

  test "return_endorsed is refused with :not_conforming when the verdict is false" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :declassify)

    assert {:error, :not_conforming} =
             Instance.return_endorsed(h, "a1", "root", false, :sensitive, :attested)

    assert budget(h, "root") == 16
  end

  test "sentinel_credit_budget saturates at the capacity of 16" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "summarize")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :credit_budget)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :declassify)
    {:ok, _, _} = Instance.sentinel_credit_budget(h, "a1", 16)

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "summarize", "inv-1", true, %{"inv-1" => true}, [])

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "inv-1", true)
    assert budget(h, "a1") == 14

    {:ok, _, _} = Instance.sentinel_credit_budget(h, "a1", 100)
    assert budget(h, "a1") == 16
  end

  test "an endorsement against an agent already holding both crossing dimensions does not debit, even when capable and funded" do
    h = Instance.new(bg())
    {:ok, _, _} = Instance.register_tool(h, "summarize")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :declassify)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :credit_budget)
    {:ok, _, _} = Instance.sentinel_credit_budget(h, "a1", 16)

    # a1 already holds the tool's conf_floor (:sensitive) AND its output_integ (:attested):
    # neither dimension "helps", so the crossing eligibility conjunct
    # `(conf_helps || integ_helps)` is false regardless of the capability/budget conjuncts
    # above -- this isolates the taint/integ-blocks-debit rule from the cap/budget gates.
    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "a1", :sensitive, %{})
    {:ok, _, _} = Instance.sentinel_degrade_integrity(h, "a1", :attested, %{})

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "summarize", "inv-1", true, %{"inv-1" => true}, [])

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "inv-1", true)

    assert budget(h, "a1") == 16
    assert :sensitive in Map.fetch!(Instance.state(h).taint_levels, "a1")
    assert :attested in Map.fetch!(Instance.state(h).integ_levels, "a1")
  end

  test "recovery replays a log with sentinel_credit_budget and an endorsed return_endorsed" do
    recovery_log = [
      {:delegate, ["root", "a1"]},
      {:grant_capability, ["root", "a1", :declassify]},
      {:grant_capability, ["root", "a1", :credit_budget]},
      {:return_endorsed, ["a1", "root", true, :sensitive, :attested]},
      {:sentinel_credit_budget, ["a1", 5]}
    ]

    {:ok, h} = Instance.recover(bg(), recovery_log)
    assert Instance.seq(h) == length(recovery_log)

    live = Instance.new(bg())

    Enum.each(recovery_log, fn {fun, args} ->
      {:ok, _seq, _action} = apply(Instance, fun, [live | args])
    end)

    assert Instance.state(h) == Instance.state(live)
  end
end
