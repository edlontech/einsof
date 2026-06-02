import ArgusLean.Refinement.StateRelation

/-! # Refinement — `grant_capability`

`grant_capability prnt child cap` is the incremental-capability action: four read gates (`prnt`
active, `child` active, `child`'s parent edge is `prnt`, `prnt` already holds `cap`) followed by a
single nested write — `child`'s cap-set gains `cap` via `VecMapKVecSet.insert_into`. No agent is
added or removed, so only `agent_cap` changes.

It refines against `Rgrant`, whose `agent_cap` clause is the nested membership `vmsMem` (the view
`set_contains` / `insert_into` operate in, shared with `load_instruction`'s `agent_instruction`). The
body reuses the existing `vecMapKVecSetInsertInto_spec`; the capability gate uses the new
`vecMapKVecSetSetContains_spec` (forward direction → nested membership) and the `VecMap.get`
parent-edge gate. New `CapKind` eq/clone specs are *proved* (a nullary enum), not trusted; the only
extractor residual beyond the `register_tool` set is `optionAgentId_ne_spec` (the parent-edge gate),
and `grant_capability` never names the root, so it carries **no** `sorryAx`/`AgentId.root` baseline. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Inversion lemma for a successful `grant_capability` step. Peels the two active gates, the
    `VecMap.get` parent-edge gate, and the `set_contains` capability gate (forward → `vmsMem`), then
    reads off the single `agent_cap` nested insert. The capacity side conditions feed `insert_into`. -/
theorem grant_capability_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (parent child : types.AgentId) (cap : capability.CapKind)
    (hcapE : st.agent_cap.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_capability st bg parent child cap = .ok (.Ok (st', ev))) :
    ∃ vmAfter,
      vsMem st.agent_active parent ∧
      vsMem st.agent_active child ∧
      vmLastEntry st.agent_parent.entries.val child = some (child, parent) ∧
      vmsMem st.agent_cap parent cap ∧
      st' = { st with agent_cap := vmAfter } ∧
      (∀ N C, vmsMem vmAfter N C ↔ vmsMem st.agent_cap N C ∨ (N = child ∧ C = cap)) := by
  simp only [transitions.grant_capability] at hok
  -- Gate 1: parent active.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- Gate 2: child active.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  -- Gate 3: the parent edge `child → parent`.
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :
      ∃ bb, core.option.Option.Insts.CoreCmpPartialEqOption.ne
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId) o (some parent) =
        .ok bb ∧ (bb = true ↔ o ≠ some parent) :=
    ⟨_, optionAgentId_ne_spec o (some parent), by simp⟩
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = false := by cases b2 with | false => rfl | true => simp at hok
  simp only [hb2, reduceIte, Bool.false_eq_true] at hok
  have hoP : o = some parent := by
    by_contra hc
    have := hb2Iff.mpr hc; rw [hb2] at this; simp at this
  have hlast : vmLastEntry st.agent_parent.entries.val child = some (child, parent) := by
    have hoP' : (vmLastEntry st.agent_parent.entries.val child).map Prod.snd = some parent := by
      rw [← ho]; exact hoP
    cases hL : vmLastEntry st.agent_parent.entries.val child with
    | none => rw [hL] at hoP'; simp at hoP'
    | some p =>
      have hp1 : p.1 = child := vmLastEntry_fst _ _ _ hL
      rw [hL, Option.map_some] at hoP'
      obtain ⟨x, y⟩ := p
      simp only [Option.some_inj] at hoP'
      simp_all
  -- Gate 4: the parent already holds `cap`.
  obtain ⟨b3, hb3Eq, hb3Imp⟩ := spec_imp_exists
    (vecMapKVecSetSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap parent cap)
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = true := by cases b3 with | true => rfl | false => simp at hok
  simp only [hb3, reduceIte] at hok
  -- Body: clone child, then the nested insert.
  simp only [agentId_clone_spec, bind_tc_ok] at hok
  obtain ⟨vmAfter, hInsertEq, hInsertMem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap child cap hcapE hcapS)
  rw [hInsertEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨vmAfter, hbIff.mp hb, hb1Iff.mp hb1, hlast, hb3Imp hb3, hStateEq.symm, hInsertMem⟩

/-- Forward simulation: a successful `grant_capability` step is matched by the abstract action,
    preserving `Rgrant`. The witness adds `(child, cap)` to `agent_cap`; everything else is framed. -/
theorem grant_capability_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (parent child : types.AgentId) (cap : capability.CapKind)
    (hR : Rgrant st a)
    (hcapE : st.agent_cap.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_capability st bg parent child cap = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.grant_capability parent child cap).guard a ∧
          (Tzimtzum.grant_capability parent child cap).next a a' ∧ Rgrant st' a' := by
  obtain ⟨hRactive, hRparent, hRcap⟩ := hR
  obtain ⟨vmAfter, hParentActive, hChildActive, hParentEdge, hParentCap, hStEq, hNewCap⟩ :=
    grant_capability_ok_inv st bg parent child cap hcapE hcapS st' ev hok
  refine ⟨{a with agent_cap := fun N C => (N = child ∧ C = cap) ∨ a.agent_cap N C}, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.grant_capability]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hRactive parent).mpr hParentActive
    · exact (hRactive child).mpr hChildActive
    · exact (hRparent child parent).mpr hParentEdge
    · exact (hRcap parent cap).mpr hParentCap
  · -- next
    simp [Tzimtzum.grant_capability]
  · -- Rgrant st' a'
    subst hStEq
    refine ⟨hRactive, hRparent, ?_⟩
    intro N C
    show ((N = child ∧ C = cap) ∨ a.agent_cap N C) ↔ vmsMem vmAfter N C
    have h1 := hRcap N C
    have h2 := hNewCap N C
    tauto

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id residuals plus
-- `optionAgentId_ne_spec` (the `Option AgentId` parent-edge gate, `agentId_ne_spec` class). The
-- `CapKind` eq/clone facts are PROVED (nullary enum), not trusted. Unlike the tree actions,
-- `grant_capability` never gates on the root, so it carries NO `sorryAx`/`AgentId.root` residual.
#print axioms ArgusLean.Refinement.grant_capability_ok_inv
#print axioms ArgusLean.Refinement.grant_capability_refines
