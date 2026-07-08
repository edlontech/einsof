import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `sentinel_credit_budget` preserves the unified `R`

`sentinel_credit_budget` (Campaign B; replaced the old full-refresh action that deleted the budget entry)
credits `agent`'s `agent_budget` cell by `amount`, saturating at `BUDGET_CAPACITY` (`VecMap.insert` via
the numeric `credit_budget`), framing everything else as `{ st with agent_budget := vm }` (via
`creditBudget_full`). The only **credit** action: `R`'s canonical budget view is the active-guarded
get-style `budgetReadC`; the abstract post `budget_saturating_credit b n = min budget_capacity (b + n)`
matches the kernel's `min (saturating_add …) BUDGET_CAPACITY` via the `saturatingAddMin_val` collapse.
The cap read-gate (`vmsMem`) is bridged to `R`'s `vmsMemLast` cap view via `R.ndCap`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Inversion lemma for a successful `sentinel_credit_budget` step. Peels the two gates (active via
    `VecSet.contains`, the `CreditBudget` cap via `set_contains`'s forward direction) and reads off the
    single `agent_budget` credit write (`credit_budget`) as the get-style saturating post plus nodup. -/
theorem sentinel_credit_budget_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (agent : types.AgentId) (amount : Std.U8)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_credit_budget st bg agent amount = .ok (.Ok (st', ev))) :
    ∃ vm,
      vsMem st.agent_active agent ∧
      vmsMem st.agent_cap agent capability.CapKind.CreditBudget ∧
      st' = { st with agent_budget := vm } ∧
      (∀ G, budgetReadC vm G =
        if G = agent then
          core.cmp.impls.OrdU8.min (core.num.U8.saturating_add (budgetReadC st.agent_budget agent) amount)
            types.BUDGET_CAPACITY
        else budgetReadC st.agent_budget G) ∧
      (vmNodupKeys st.agent_budget → vmNodupKeys vm) := by
  simp only [transitions.sentinel_credit_budget] at hok
  -- Gate 1: `agent` active.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- Gate 2: `agent` holds the `CreditBudget` capability.
  obtain ⟨b1, hb1Eq, hb1Imp⟩ := spec_imp_exists
    (vecMapKVecSetSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap agent capability.CapKind.CreditBudget)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  -- Body: credit `agent`'s budget by `amount` (saturating at capacity).
  obtain ⟨st1, hst1Eq, vm, hStruct, hBud, hBudNd⟩ :=
    spec_imp_exists (creditBudget_full st agent amount hcap)
  rw [hst1Eq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨vm, hbIff.mp hb, hb1Imp hb1, hStateEq.symm.trans hStruct, hBud, hBudNd⟩

/-- `sentinel_credit_budget` preserves the unified `R`. -/
theorem sentinel_credit_budget_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (agent : types.AgentId) (amount : Std.U8)
    (hR : R st bg a)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_credit_budget st bg agent amount = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_credit_budget agent amount.val).guard a ∧
          (Tzimtzum.sentinel_credit_budget agent amount.val).next a a' ∧ R st' bg a' := by
  obtain ⟨vm, hAgentActive, hAgentCap, rfl, hBud, hBudNd⟩ :=
    sentinel_credit_budget_ok_inv st bg agent amount hcap st' ev hok
  refine ⟨{ a with agent_budget :=
      fun A => if A = agent then Tzimtzum.budget_saturating_credit (a.agent_budget agent) amount.val
        else a.agent_budget A },
    ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.sentinel_credit_budget]
    refine ⟨(hR.active agent).mpr hAgentActive, ?_⟩
    rw [hR.cap_refresh]
    exact (hR.cap agent capability.CapKind.CreditBudget).mpr
      ((vmsMem_iff_vmsMemLast st.agent_cap hR.ndCap agent capability.CapKind.CreditBudget).mp hAgentCap)
  · -- next: the classical `ite` at `AgentId`'s abstract type needs a decidable-irrelevant
    -- case split instead of syntactic `rfl` (same shape as `Delegate`'s budget conjunct).
    simp [Tzimtzum.sentinel_credit_budget]
    funext G; by_cases hG : G = agent <;> simp [hG]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg,
      hR.parent, hR.cap, hR.instr, hR.taint, hR.integ, hR.inflight, hR.override, ?_, hR.invUsed,
      hR.invEgress, hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor,
      hR.toolIntegInspectFloor, hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss,
      hR.instrIssuer, hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor,
      hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr, hR.ndTaint, hR.ndInteg,
      hR.ndInflight, hR.ndOverride, hR.ndFlowOverride, ?_, hR.wfInflight⟩
    · -- budget (agent credit, saturating; numeric collapse, no active-guard)
      intro G
      show (if G = agent then Tzimtzum.budget_saturating_credit (a.agent_budget agent) amount.val
          else a.agent_budget G) = (budgetReadC vm G).val
      rw [hBud G]
      by_cases hG : G = agent
      · rw [if_pos hG, if_pos hG, saturatingAddMin_val, hR.budget agent,
          Tzimtzum.budget_saturating_credit]
      · rw [if_neg hG, if_neg hG, hR.budget G]
    · -- ndBudget
      exact hBudNd hR.ndBudget

end ArgusLean.Refinement
