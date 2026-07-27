import ArgusLean.Refinement.Unified.Relation

/-! # Layer 1 — shared bridges for per-action `R`-preservation

Small reused facts that connect the unified `R`'s field views to the forms the per-action `_ok_inv` /
`_refines` lemmas expose. Kept out of `Relation.lean` so the relation file stays a pure definition. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

/-- `bg.tool_metadata` is deterministic and computes `toolMetaC`, so a `.ok (some tm)` lookup pins
    `toolMetaC bg t = some tm`. Bridges `Rtool`'s `tool_metadata`-phrased clause to `R`'s
    `toolMetaC`-phrased `toolIssuer`/`toolFloor`/`toolBounded`/`toolCap` conjuncts. -/
theorem toolMetaC_of_metadata {bg : background.BackgroundTheory} {t : types.ToolId}
    {tm : background.ToolMetadata} (h : bg.tool_metadata t = .ok (some tm)) :
    toolMetaC bg t = some tm := by
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists (toolMetadata_spec bg t)
  rw [h] at hoEq
  rw [← ho]
  exact (Result.ok.inj hoEq).symm

set_option maxHeartbeats 1000000

/-- `debit_budget agent w` returns a record update `{ st with agent_budget := vm }` whose get-style
    budget read subtracts the sensitivity weight `w` from `agent` (saturating at `0`) and frames every
    other agent, and whose key-uniqueness is preserved. The numeric (Campaign B) strengthening of
    `debitBudget_spec` with the `vmNodupKeys` conjunct that the `return_endorsed` / `invoke_complete` /
    `grant_override` unified-`R` preservations need (so all non-budget fields transport definitionally
    and `R.ndBudget` re-establishes). -/
theorem debitBudget_full (st : state.KernelState) (agent : types.AgentId) (w : Std.U8)
    (hcap : st.agent_budget.entries.val.length < Usize.max) :
    state.KernelState.debit_budget st agent w ⦃ st1 =>
      ∃ vm, st1 = { st with agent_budget := vm } ∧
        (∀ G, budgetReadC vm G =
          if G = agent then core.num.U8.saturating_sub (budgetReadC st.agent_budget agent) w
          else budgetReadC st.agent_budget G) ∧
        (vmNodupKeys st.agent_budget → vmNodupKeys vm) ⦄ := by
  unfold state.KernelState.debit_budget
  obtain ⟨bl, hblEq, hbl⟩ := spec_imp_exists (budget_spec st agent)
  rw [hblEq]
  simp only [bind_tc_ok, core.num.U8.saturating_sub, lift, agentId_clone_spec]
  obtain ⟨vm, hvmEq, hvmLast⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      core.clone.CloneU8 st.agent_budget agent (UScalar.saturating_sub bl w) hcap)
  obtain ⟨vm2, hvm2Eq, hvm2nd⟩ := spec_imp_exists
    (vecMapInsert_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      core.clone.CloneU8 st.agent_budget agent (UScalar.saturating_sub bl w) hcap)
  have hvv : vm2 = vm := Result.ok.inj (hvm2Eq.symm.trans hvmEq)
  rw [hvmEq]
  simp only [bind_tc_ok, spec_ok]
  refine ⟨vm, rfl, fun G => ?_, hvv ▸ hvm2nd⟩
  show budgetReadC vm G =
    if G = agent then core.num.U8.saturating_sub (budgetReadC st.agent_budget agent) w
    else budgetReadC st.agent_budget G
  by_cases hG : G = agent
  · rw [if_pos hG]
    have hvr : budgetReadC vm G = UScalar.saturating_sub bl w := by
      unfold budgetReadC; rw [hvmLast G, if_pos hG]
    rw [hvr, hbl]; rfl
  · rw [if_neg hG]
    unfold budgetReadC; rw [hvmLast G, if_neg hG]

/-- `credit_budget agent n` returns a record update `{ st with agent_budget := vm }` whose get-style
    budget read credits `agent` by `n` (saturating at `BUDGET_CAPACITY`) and frames every other agent,
    and whose key-uniqueness is preserved. The numeric `vmNodupKeys`-strengthening of `creditBudget_spec`
    that the `sentinel_credit_budget` unified-`R` preservation needs. -/
theorem creditBudget_full (st : state.KernelState) (agent : types.AgentId) (n : Std.U8)
    (hcap : st.agent_budget.entries.val.length < Usize.max) :
    state.KernelState.credit_budget st agent n ⦃ st1 =>
      ∃ vm, st1 = { st with agent_budget := vm } ∧
        (∀ G, budgetReadC vm G =
          if G = agent then
            core.cmp.impls.OrdU8.min (core.num.U8.saturating_add (budgetReadC st.agent_budget agent) n)
              types.BUDGET_CAPACITY
          else budgetReadC st.agent_budget G) ∧
        (vmNodupKeys st.agent_budget → vmNodupKeys vm) ⦄ := by
  unfold state.KernelState.credit_budget
  obtain ⟨bl, hblEq, hbl⟩ := spec_imp_exists (budget_spec st agent)
  rw [hblEq]
  simp only [bind_tc_ok, core.num.U8.saturating_add, lift, agentId_clone_spec]
  step*
  rw [next_post]
  obtain ⟨vm, hvmEq, hvmLast⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec core.clone.CloneU8 st.agent_budget
      agent (core.cmp.impls.OrdU8.min (UScalar.saturating_add bl n) types.BUDGET_CAPACITY) hcap)
  obtain ⟨vm2, hvm2Eq, hvm2nd⟩ := spec_imp_exists
    (vecMapInsert_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec core.clone.CloneU8 st.agent_budget
      agent (core.cmp.impls.OrdU8.min (UScalar.saturating_add bl n) types.BUDGET_CAPACITY) hcap)
  have hvv : vm2 = vm := Result.ok.inj (hvm2Eq.symm.trans hvmEq)
  rw [hvmEq]
  simp only [bind_tc_ok, spec_ok]
  refine ⟨vm, rfl, fun G => ?_, hvv ▸ hvm2nd⟩
  show budgetReadC vm G =
    if G = agent then
      core.cmp.impls.OrdU8.min (core.num.U8.saturating_add (budgetReadC st.agent_budget agent) n)
        types.BUDGET_CAPACITY
    else budgetReadC st.agent_budget G
  by_cases hG : G = agent
  · rw [if_pos hG]
    have hvr : budgetReadC vm G =
        core.cmp.impls.OrdU8.min (UScalar.saturating_add bl n) types.BUDGET_CAPACITY := by
      unfold budgetReadC; rw [hvmLast G, if_pos hG]
    rw [hvr, hbl]; rfl
  · rw [if_neg hG]
    unfold budgetReadC; rw [hvmLast G, if_neg hG]


/-- `le_integ` with the abstracted concrete level on the LEFT is the kernel's rank compare —
    the mirrored companion of `le_integ_integLeC`, for floor guards where the concrete side is
    the floor (`return_endorsed`/`return_unendorsed`/`sentinel_degrade_integrity`). -/
theorem le_integ_integLeC' (c : types.IntegLevel) (L : Tzimtzum.IntegLevel) :
    Tzimtzum.le_integ (integA c) L ↔ integLeC c (integC L) = true := by
  cases c <;> cases L <;> simp [Tzimtzum.le_integ, Tzimtzum.integRank, integA, integC, integLeC]

end ArgusLean.Refinement
