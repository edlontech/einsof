defmodule ExArgus.SafetyScenariosTest do
  @moduledoc """
  Elixir twin of argus-kernel's design §7 safety-scenario suite
  (`argus/crates/argus-kernel/tests/safety_properties.rs`, scenarios 1-16), driven through
  `ExArgus.Instance` (the live path). Fixtures, levels and weights mirror the Rust `v3_kernel`
  helper and its scenario-specific variants one-to-one.
  """
  use ExUnit.Case, async: true

  alias ExArgus.Instance
  alias ExArgus.Kernel.Background

  @budget_capacity 16

  defp declass_weight(:sensitive), do: 2
  defp declass_weight(:restricted), do: 4

  defp integ_weight(:standard), do: 2
  defp integ_weight(:untrusted), do: 4

  # Mirrors `v3_kernel()`: web_fetch (floor untrusted / emission untrusted, egress
  # network_external), delete_repo (floor trusted / emission attested, destructive, no
  # egress) and send_email (floor untrusted / emission attested, egress network_external),
  # lever floors trusted, network_external ceiling allowing up to sensitive.
  defp v3_bg do
    %Background{
      tools: %{
        "web_fetch" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :public,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :untrusted
        },
        "delete_repo" => %{
          capabilities: [:filesystem_delete],
          egress: [],
          conf_floor: :public,
          output_bounded: false,
          issuer: "trusted",
          integ_floor: :trusted,
          integ_inspect_floor: :trusted,
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
      allow_ceiling: %{network_external: :sensitive},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{},
      lever_integ_floor: :trusted,
      lever_integ_inspect_floor: :trusted
    }
  end

  test "scenario 1: unendorsed web_fetch then delete_repo denied at CHECK 4a" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_delete)

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "web_fetch", "i1", true, %{"i1" => true}, [
        :network_external
      ])

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "i1", true)

    assert :untrusted in Map.fetch!(Instance.state(h).integ_levels, "a1")

    assert {:error, :integrity_floor_denied} =
             Instance.invoke_start(h, "a1", "delete_repo", "i2", true, %{"i2" => true}, [])
  end

  test "scenario 2: delete_repo in flight blocks web_fetch at CHECK 4b" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_delete)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)

    {:ok, _, _} = Instance.invoke_start(h, "a1", "delete_repo", "i1", true, %{"i1" => true}, [])

    assert {:error, :integrity_floor_denied} =
             Instance.invoke_start(h, "a1", "web_fetch", "i2", true, %{"i2" => true}, [
               :network_external
             ])
  end

  test "scenario 3: endorsed web_fetch keeps delete_repo path open and debits integ_weight" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_delete)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :declassify)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :credit_budget)
    {:ok, _, _} = Instance.sentinel_credit_budget(h, "a1", @budget_capacity)

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "web_fetch", "i1", true, %{"i1" => true}, [
        :network_external
      ])

    assert {:ok, _, {:invoke_complete, "a1", "i1", true}} =
             Instance.invoke_complete(h, "a1", "i1", true)

    assert Map.fetch!(Instance.state(h).agent_budget, "a1") ==
             @budget_capacity - integ_weight(:untrusted)

    refute Map.has_key?(Instance.state(h).integ_levels, "a1")

    assert {:ok, _, _} =
             Instance.invoke_start(h, "a1", "delete_repo", "i2", true, %{"i2" => true}, [])
  end

  test "scenario 4: injected child below the lever floor -- return_endorsed denied" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.delegate(h, "root", "child")
    {:ok, _, _} = Instance.grant_capability(h, "root", "child", :declassify)
    {:ok, _, _} = Instance.sentinel_degrade_integrity(h, "child", :untrusted, %{})

    assert {:error, :lever_integrity_denied} =
             Instance.return_endorsed(h, "child", "root", true, :public, :untrusted)
  end

  test "scenario 5: degraded granter -- grant_override denied strict" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "send_email")
    {:ok, _, _} = Instance.delegate(h, "root", "granter")
    {:ok, _, _} = Instance.grant_capability(h, "root", "granter", :grant_override)
    {:ok, _, _} = Instance.sentinel_degrade_integrity(h, "granter", :untrusted, %{})
    {:ok, _, _} = Instance.delegate(h, "root", "target")

    assert {:error, :lever_integrity_denied} =
             Instance.grant_override(h, "granter", "target", "send_email", :public)
  end

  test "scenario 6: sentinel degrade blocked with destructive tool in flight, succeeds after completion" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_delete)

    {:ok, _, _} = Instance.invoke_start(h, "a1", "delete_repo", "i1", true, %{"i1" => true}, [])

    assert {:error, :integrity_floor_denied} =
             Instance.sentinel_degrade_integrity(h, "a1", :untrusted, %{})

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "i1", true)

    assert {:ok, _, _} = Instance.sentinel_degrade_integrity(h, "a1", :untrusted, %{})
  end

  test "scenario 7: delegated child starts clean and at budget 0; endorse-before-credit routes unendorsed" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")
    {:ok, _, _} = Instance.delegate(h, "root", "child")

    assert Map.get(Instance.state(h).agent_budget, "child") == 0
    refute Map.has_key?(Instance.state(h).taint_levels, "child")
    refute Map.has_key?(Instance.state(h).integ_levels, "child")

    {:ok, _, _} = Instance.grant_capability(h, "root", "child", :network_egress)
    {:ok, _, _} = Instance.grant_capability(h, "root", "child", :declassify)

    {:ok, _, _} =
      Instance.invoke_start(h, "child", "web_fetch", "i1", true, %{"i1" => true}, [
        :network_external
      ])

    assert {:ok, _, {:invoke_complete, "child", "i1", false}} =
             Instance.invoke_complete(h, "child", "i1", true)

    assert :untrusted in Map.fetch!(Instance.state(h).integ_levels, "child")
  end

  test "scenario 8: budget-mint replay -- an uncredited child cannot self-fund, a credited one can" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")

    {:ok, _, _} = Instance.delegate(h, "root", "uncredited")
    {:ok, _, _} = Instance.grant_capability(h, "root", "uncredited", :network_egress)
    {:ok, _, _} = Instance.grant_capability(h, "root", "uncredited", :declassify)
    assert Map.get(Instance.state(h).agent_budget, "uncredited") == 0

    {:ok, _, _} =
      Instance.invoke_start(h, "uncredited", "web_fetch", "i1", true, %{"i1" => true}, [
        :network_external
      ])

    assert {:ok, _, {:invoke_complete, "uncredited", "i1", false}} =
             Instance.invoke_complete(h, "uncredited", "i1", true)

    assert :untrusted in Map.fetch!(Instance.state(h).integ_levels, "uncredited")

    {:ok, _, _} = Instance.delegate(h, "root", "credited")
    {:ok, _, _} = Instance.grant_capability(h, "root", "credited", :network_egress)
    {:ok, _, _} = Instance.grant_capability(h, "root", "credited", :declassify)
    {:ok, _, _} = Instance.grant_capability(h, "root", "credited", :credit_budget)
    {:ok, _, _} = Instance.sentinel_credit_budget(h, "credited", @budget_capacity)

    {:ok, _, _} =
      Instance.invoke_start(h, "credited", "web_fetch", "i2", true, %{"i2" => true}, [
        :network_external
      ])

    assert {:ok, _, {:invoke_complete, "credited", "i2", true}} =
             Instance.invoke_complete(h, "credited", "i2", true)
  end

  defp scenario9_bg do
    %Background{
      tools: %{
        "web_fetch" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :internal,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :untrusted
        }
      },
      allow_ceiling: %{network_external: :internal},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "scenario 9: dimension-adjusted debit pays only integ_weight when conf already tainted" do
    h = Instance.new(scenario9_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :declassify)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :credit_budget)
    {:ok, _, _} = Instance.sentinel_credit_budget(h, "a1", @budget_capacity)

    # Already conf-tainted at the tool's own floor -- the conf dimension cannot help.
    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "a1", :internal, %{})

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "web_fetch", "i1", true, %{"i1" => true}, [
        :network_external
      ])

    assert {:ok, _, {:invoke_complete, "a1", "i1", true}} =
             Instance.invoke_complete(h, "a1", "i1", true)

    # declass_weight(internal) = 1 would apply if the conf dimension had helped; only
    # integ_weight(untrusted) = 4 is charged.
    assert Map.fetch!(Instance.state(h).agent_budget, "a1") ==
             @budget_capacity - integ_weight(:untrusted)
  end

  # The Elixir `Background` struct defaults `lever_integ_floor`/`lever_integ_inspect_floor` to
  # `:attested` (fail-closed top of lattice), unlike the Rust builder's ungated `:untrusted`
  # default (see `ExArgus.Kernel.Background` moduledoc) -- set explicitly here so this scenario
  # isolates the coverage guard, not the lever floor (scenario 4 covers the lever floor).
  defp empty_bg do
    %Background{
      tools: %{},
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: [],
      instruction_issuer: %{},
      lever_integ_floor: :untrusted,
      lever_integ_inspect_floor: :untrusted
    }
  end

  test "scenario 10: return_endorsed coverage denial; restricted return costs declass_weight + integ_weight" do
    h = Instance.new(empty_bg())
    {:ok, _, _} = Instance.delegate(h, "root", "child")
    {:ok, _, _} = Instance.grant_capability(h, "root", "child", :declassify)

    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "child", :restricted, %{})
    {:ok, _, _} = Instance.sentinel_degrade_integrity(h, "child", :standard, %{})

    assert {:error, :declaration_not_covering} =
             Instance.return_endorsed(h, "child", "root", true, :sensitive, :attested)

    budget_before = Map.get(Instance.state(h).agent_budget, "root", @budget_capacity)

    assert {:ok, _, _} =
             Instance.return_endorsed(h, "child", "root", true, :restricted, :standard)

    budget_after = Map.get(Instance.state(h).agent_budget, "root", @budget_capacity)

    assert budget_before - budget_after == declass_weight(:restricted) + integ_weight(:standard)
  end

  defp scenario11_bg do
    %Background{
      tools: %{
        "http_request" => %{
          capabilities: [:network_egress],
          egress: [:network_external, :network_internal],
          conf_floor: :public,
          output_bounded: false,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{network_internal: :sensitive, network_external: :public},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "scenario 11: attested egress precision beats the static worst case" do
    h = Instance.new(scenario11_bg())
    {:ok, _, _} = Instance.register_tool(h, "http_request")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "a1", :sensitive, %{})

    assert {:error, :flow_gate_blocked} =
             Instance.invoke_start(h, "a1", "http_request", "i1", true, %{"i1" => true}, [
               :network_external,
               :network_internal
             ])

    assert {:ok, _, _} =
             Instance.invoke_start(h, "a1", "http_request", "i2", true, %{"i2" => true}, [
               :network_internal
             ])
  end

  test "scenario 12: attested egress outside the declared set denied (narrowing); empty attestation on egress-bearing tool denied (coverage)" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)

    assert {:error, :attestation_invalid} =
             Instance.invoke_start(h, "a1", "web_fetch", "i1", true, %{"i1" => true}, [
               :network_internal
             ])

    assert {:error, :attestation_invalid} =
             Instance.invoke_start(h, "a1", "web_fetch", "i2", true, %{"i2" => true}, [])
  end

  test "scenario 13: invocation-id replay denied; through Instance surfaces :invocation_exists" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_delete)

    {:ok, _, _} = Instance.invoke_start(h, "a1", "delete_repo", "i1", true, %{"i1" => true}, [])
    {:ok, _, _} = Instance.invoke_complete(h, "a1", "i1", true)

    # invocation_tool and invocation_used are both set together at invoke_start, so replaying
    # the exact id a completed invocation used trips the pre-existing InvocationExists guard
    # before the dedicated freshness (:invocation_replayed) check is reached -- replay is
    # still denied (design §6).
    assert {:error, :invocation_exists} =
             Instance.invoke_start(h, "a1", "delete_repo", "i1", true, %{"i1" => true}, [])
  end

  test "scenario 14: missing cap_declassify at completion routes unendorsed, fail-safe (no error)" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "web_fetch")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :credit_budget)
    {:ok, _, _} = Instance.sentinel_credit_budget(h, "a1", @budget_capacity)

    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "web_fetch", "i1", true, %{"i1" => true}, [
        :network_external
      ])

    assert {:ok, _, {:invoke_complete, "a1", "i1", false}} =
             Instance.invoke_complete(h, "a1", "i1", true)

    assert :untrusted in Map.fetch!(Instance.state(h).integ_levels, "a1")
  end

  test "scenario 15: override consumed eagerly via ALLOW, re-armed via grant_override at weighted price" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "send_email")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :network_egress)

    {:ok, _, _} = Instance.grant_override(h, "root", "a1", "send_email", :sensitive)

    budget_after_first_arm = Map.get(Instance.state(h).agent_budget, "root", @budget_capacity)
    assert budget_after_first_arm == @budget_capacity - declass_weight(:sensitive)

    {:ok, _, _} = Instance.sentinel_elevate_taint(h, "a1", :sensitive, %{})

    # The flow is admissible via ALLOW (the ceiling covers sensitive) -- the override is not
    # needed to justify admission, but eager consumption spends it anyway.
    {:ok, _, _} =
      Instance.invoke_start(h, "a1", "send_email", "i1", true, %{"i1" => true}, [
        :network_external
      ])

    assert {"send_email", :sensitive} in Map.get(Instance.state(h).override_used, "a1", [])

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "i1", true)

    {:ok, _, _} = Instance.grant_override(h, "root", "a1", "send_email", :sensitive)

    assert Map.get(Instance.state(h).agent_budget, "root", @budget_capacity) ==
             budget_after_first_arm - declass_weight(:sensitive)

    refute {"send_email", :sensitive} in Map.get(Instance.state(h).override_used, "a1", [])
  end

  test "scenario 16: unregister_tool -- in-flight denies, completion allows, then invoke denies" do
    h = Instance.new(v3_bg())
    {:ok, _, _} = Instance.register_tool(h, "delete_repo")
    {:ok, _, _} = Instance.delegate(h, "root", "a1")
    {:ok, _, _} = Instance.grant_capability(h, "root", "a1", :filesystem_delete)

    {:ok, _, _} = Instance.invoke_start(h, "a1", "delete_repo", "i1", true, %{"i1" => true}, [])

    assert {:error, :tool_in_flight} = Instance.unregister_tool(h, "delete_repo")

    {:ok, _, _} = Instance.invoke_complete(h, "a1", "i1", true)
    assert {:ok, _, _} = Instance.unregister_tool(h, "delete_repo")

    assert {:error, :tool_not_registered} =
             Instance.invoke_start(h, "a1", "delete_repo", "i2", true, %{"i2" => true}, [])
  end
end
