import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `grant_override` preserves the unified `R`

`grant_override` (the 13th, Campaign-A action) arms/re-arms a single-use flow override for
`(target, tool, level)`: it (1) inserts `{tool, level}` into `target`'s `flow_override` set, (2)
removes that same key from `target`'s `override_used` set, then (3) debits `granter`'s budget by the
flat weight one. The five gates mirror `return_endorsed`'s — `granter`/`target` active (`VecSet.contains`), the
`GrantOverride` cap (`set_contains`, bridged via `R.ndCap` like `sentinel_credit_budget`'s
`CreditBudget` gate), `affordable granter 1`, and the re-arm guard `target` has no in-flight
invocations (`set_nonempty target = false`, exactly `return_endorsed`'s child-no-in-flight guard).

The two override writes use the last-match `vmsMemLast` specs (`vecMapKVecSetInsertInto_vmLast_spec` /
`vecMapKVecSetRemoveFrom_spec`) with the `OverrideKey` instances, characterising the post-images as a
point-add / point-remove at `(target, {tool, confC (confA level)})` (the `confC`/`confA` roundtrip
collapses the level component). `debitBudget_full` then frames every other field and re-establishes
`R.budget`/`R.ndBudget` (the `return_endorsed` budget walk), threaded through the intermediate state
`{ st with override_used := vm1, flow_override := vm }` whose `agent_budget` is `st.agent_budget`. The
write nodup posts re-establish `R.ndOverride`/`R.ndFlowOverride`. No flow-gate reads ⇒ `ceilingAdmits`
irrelevant; no root naming ⇒ no `AgentId.root` axiom. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Comprehensive inversion for a successful `grant_override` step: the five gates plus the structural
    three-write post-state (`flow_override` point-add, `override_used` point-remove, `granter` budget
    debit) and the two override-key nodup posts. -/
theorem grant_override_inv_full
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (granter target : types.AgentId) (tool : types.ToolId) (level : types.ConfLevel)
    (hcapFoE : st.flow_override.entries.val.length < Usize.max)
    (hcapFoS : ∀ p ∈ st.flow_override.entries.val, p.2.items.val.length < Usize.max)
    (hcapBud : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_override st bg granter target tool level = .ok (.Ok (st', ev))) :
    ∃ vmFo vmOu vmBud,
      vsMem st.agent_active granter ∧
      vsMem st.agent_active target ∧
      vmsMem st.agent_cap granter capability.CapKind.GrantOverride ∧
      (1#u8 : Std.U8) ≤ budgetReadC st.agent_budget granter ∧
      (∀ inv, ¬ vmsMemLast st.in_flight target inv) ∧
      (∀ k v, vmsMemLast vmFo k v ↔
        vmsMemLast st.flow_override k v ∨ (k = target ∧ v = { tool := tool, level := level })) ∧
      (∀ k v, vmsMemLast vmOu k v ↔
        vmsMemLast st.override_used k v ∧ ¬ (k = target ∧ v = { tool := tool, level := level })) ∧
      st' = { st with override_used := vmOu, flow_override := vmFo, agent_budget := vmBud } ∧
      (∀ G, budgetReadC vmBud G =
        if G = granter then core.num.U8.saturating_sub (budgetReadC st.agent_budget granter) 1#u8
        else budgetReadC st.agent_budget G) ∧
      (vmNodupKeys st.flow_override → vmNodupKeys vmFo) ∧
      (vmNodupKeys st.override_used → vmNodupKeys vmOu) ∧
      (vmNodupKeys st.agent_budget → vmNodupKeys vmBud) := by
  simp only [transitions.grant_override] at hok
  -- Gate 1: `granter` active.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active granter)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- Gate 2: `target` active.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active target)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  -- Gate 3: `granter` holds the `GrantOverride` cap.
  obtain ⟨b2, hb2Eq, hb2Imp⟩ := spec_imp_exists
    (vecMapKVecSetSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap granter capability.CapKind.GrantOverride)
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  -- Gate 4: `granter` can afford the weight-1 debit.
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists (affordable_spec st granter 1#u8)
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = true := by cases b3 with | true => rfl | false => simp at hok
  simp only [hb3, reduceIte] at hok
  have hAfford : (1#u8 : Std.U8) ≤ budgetReadC st.agent_budget granter := hb3Iff.mp hb3
  -- Gate 5: re-arm guard — `target` has no in-flight invocations.
  obtain ⟨b4, hb4Eq, hb4Iff⟩ := spec_imp_exists
    (vecMapKVecSetSetNonempty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight target)
  rw [hb4Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb4 : b4 = false := by cases b4 with | false => rfl | true => simp at hok
  simp only [hb4, reduceIte, Bool.false_eq_true] at hok
  have hNoFlight : ∀ inv, ¬ vmsMemLast st.in_flight target inv := by
    intro inv hc
    have : b4 = true := hb4Iff.mpr ⟨inv, hc⟩
    rw [hb4] at this; simp at this
  -- clones of target / tool
  rw [agentId_clone_spec, bind_tc_ok, toolId_clone_spec, bind_tc_ok] at hok
  -- Write 1: insert `{tool, level}` into `target`'s flow_override.
  obtain ⟨vmFo, hvmFoEq, hvmFoMem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
      overrideKey_eq_spec overrideKey_clone_spec st.flow_override target
      { tool := tool, level := level } hcapFoE hcapFoS)
  obtain ⟨vmFoNd, hvmFoNdEq, hvmFoNd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
      overrideKey_eq_spec overrideKey_clone_spec st.flow_override target
      { tool := tool, level := level } hcapFoE hcapFoS)
  have hFoEq : vmFoNd = vmFo := Result.ok.inj (hvmFoNdEq.symm.trans hvmFoEq)
  rw [hvmFoEq] at hok
  simp only [bind_tc_ok] at hok
  -- Write 2: remove `{tool, level}` from `target`'s override_used.
  obtain ⟨vmOu, hvmOuEq, hvmOuMem⟩ := spec_imp_exists
    (vecMapKVecSetRemoveFrom_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec agentId_clone_spec
      types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
      overrideKey_ne_spec overrideKey_clone_spec st.override_used target
      { tool := tool, level := level })
  obtain ⟨vmOuNd, hvmOuNdEq, hvmOuNd⟩ := spec_imp_exists
    (vecMapKVecSetRemoveFrom_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec agentId_clone_spec
      types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
      overrideKey_ne_spec overrideKey_clone_spec st.override_used target
      { tool := tool, level := level })
  have hOuEq : vmOuNd = vmOu := Result.ok.inj (hvmOuNdEq.symm.trans hvmOuEq)
  rw [hvmOuEq] at hok
  simp only [bind_tc_ok] at hok
  -- Write 3: debit `granter`'s budget on the intermediate state.
  obtain ⟨st1, hst1Eq, vmBud, hStruct, hBud, hBudNd⟩ := spec_imp_exists
    (debitBudget_full { st with override_used := vmOu, flow_override := vmFo } granter 1#u8 hcapBud)
  rw [hst1Eq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  refine ⟨vmFo, vmOu, vmBud, hbIff.mp hb, hb1Iff.mp hb1, hb2Imp hb2, hAfford, hNoFlight,
    hvmFoMem, hvmOuMem, ?_, ?_, ?_, hOuEq ▸ hvmOuNd, hBudNd⟩
  · rw [← hStateEq, hStruct]
  · -- `budgetReadC vmBud` debits `granter`; the intermediate's budget is `st.agent_budget`
    intro G; exact hBud G
  · exact fun h => hFoEq ▸ hvmFoNd h

/-- `grant_override` preserves the unified `R`. -/
theorem grant_override_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (granter target : types.AgentId) (tool : types.ToolId) (level : types.ConfLevel)
    (hR : R st bg a)
    (hcapFoE : st.flow_override.entries.val.length < Usize.max)
    (hcapFoS : ∀ p ∈ st.flow_override.entries.val, p.2.items.val.length < Usize.max)
    (hcapBud : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_override st bg granter target tool level = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.grant_override granter target tool (confA level)).guard a ∧
          (Tzimtzum.grant_override granter target tool (confA level)).next a a' ∧ R st' bg a' := by
  obtain ⟨vmFo, vmOu, vmBud, hGranterActive, hTargetActive, hGranterCap, hAfford, hNoFlight,
      hFoMem, hOuMem, rfl, hBud, hFoNd, hOuNd, hBudNd⟩ :=
    grant_override_inv_full st bg granter target tool level hcapFoE hcapFoS hcapBud st' ev hok
  have hGranterActiveA : a.agent_active granter := (hR.active granter).mpr hGranterActive
  refine ⟨{ a with
      flow_override := fun A T L =>
        a.flow_override A T L ∨ (A = target ∧ T = tool ∧ L = confA level)
      override_used := fun A T L =>
        a.override_used A T L ∧ ¬ (A = target ∧ T = tool ∧ L = confA level)
      agent_budget := fun A L =>
        (A = granter ∧ ∀ b, a.agent_budget granter b → L = b - 1)
        ∨ (A ≠ granter ∧ a.agent_budget A L) }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.grant_override]
    refine ⟨hGranterActiveA, (hR.active target).mpr hTargetActive, ?_, ?_, ?_⟩
    · rw [hR.cap_grantov]
      exact (hR.cap granter capability.CapKind.GrantOverride).mpr
        ((vmsMem_iff_vmsMemLast st.agent_cap hR.ndCap granter capability.CapKind.GrantOverride).mp
          hGranterCap)
    · -- affordable granter 1: the abstract budget covers weight 1
      refine ⟨(budgetReadC st.agent_budget granter).val,
        (hR.budget granter _ hGranterActiveA).mpr rfl, ?_⟩
      have : (1#u8 : Std.U8).val ≤ (budgetReadC st.agent_budget granter).val := by scalar_tac
      simpa using this
    · intro I hc
      exact hNoFlight I ((hR.inflight target I).mp hc)
  · -- next
    simp [Tzimtzum.grant_override]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg,
      hR.parent, hR.cap, hR.instr, hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, ?_, ?_,
      hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss,
      hR.instrIssuer, hR.flowAllows, hR.flowInspects, ?_, hR.invTool, hR.ndParent, hR.ndCap,
      hR.ndInstr, hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, ?_, ?_, ?_,
      hR.wfInflight⟩
    · -- override (point-remove at (target, tool, level))
      intro ag t L
      have hkey : (t = tool ∧ L = confA level) ↔
          ({ tool := t, level := confC L } : types.OverrideKey) = { tool := tool, level := level } := by
        rw [types.OverrideKey.mk.injEq]
        constructor
        · rintro ⟨ht, hL⟩; exact ⟨ht, by rw [hL]; exact confC_confA level⟩
        · rintro ⟨ht, hl⟩; exact ⟨ht, by rw [← confA_confC L, hl]⟩
      show (a.override_used ag t L ∧ ¬ (ag = target ∧ t = tool ∧ L = confA level)) ↔
        vmsMemLast vmOu ag { tool := t, level := confC L }
      rw [hOuMem ag { tool := t, level := confC L }, hR.override ag t L, hkey]
    · -- budget (granter debit by weight 1; numeric Nat subtraction collapse)
      intro G L hactiveG
      show ((G = granter ∧ ∀ b, a.agent_budget granter b → L = b - 1) ∨ (G ≠ granter ∧ a.agent_budget G L))
        ↔ (budgetReadC vmBud G).val = L
      rw [hBud G]
      by_cases hG : G = granter
      · subst hG
        simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false, if_true,
          saturatingSub_val]
        have hone : (1#u8 : Std.U8).val = 1 := by rfl
        rw [hone]
        constructor
        · intro h
          exact (h (budgetReadC st.agent_budget G).val ((hR.budget G _ hactiveG).mpr rfl)).symm
        · intro hread b hab
          have : (budgetReadC st.agent_budget G).val = b := (hR.budget G b hactiveG).mp hab
          omega
      · rw [if_neg hG]
        constructor
        · rintro (⟨hp, _⟩ | ⟨_, hab⟩)
          · exact absurd hp hG
          · rw [← hR.budget G L hactiveG]; exact hab
        · intro hread
          exact Or.inr ⟨hG, (hR.budget G L hactiveG).mpr hread⟩
    · -- flowOverride (point-add at (target, tool, level))
      intro A T L
      have hkey : (T = tool ∧ L = confA level) ↔
          ({ tool := T, level := confC L } : types.OverrideKey) = { tool := tool, level := level } := by
        rw [types.OverrideKey.mk.injEq]
        constructor
        · rintro ⟨hT, hL⟩; exact ⟨hT, by rw [hL]; exact confC_confA level⟩
        · rintro ⟨hT, hl⟩; exact ⟨hT, by rw [← confA_confC L, hl]⟩
      show (a.flow_override A T L ∨ (A = target ∧ T = tool ∧ L = confA level)) ↔
        vmsMemLast vmFo A { tool := T, level := confC L }
      rw [hFoMem A { tool := T, level := confC L }, hR.flowOverride A T L]
      apply or_congr_right
      rw [hkey]
    · -- ndOverride
      exact hOuNd hR.ndOverride
    · -- ndFlowOverride
      exact hFoNd hR.ndFlowOverride
    · -- ndBudget
      exact hBudNd hR.ndBudget

end ArgusLean.Refinement
