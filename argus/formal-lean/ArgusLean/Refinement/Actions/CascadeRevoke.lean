import ArgusLean.Refinement.StateRelation

/-! # Refinement — `cascade_revoke` (10/10 fields)

`cascade_revoke child prnt` is a *removal* action: four gates (child's parent edge is `prnt`,
`prnt` is **inactive**, `child` is active, `child ≠ root`) followed by a `VecSet.remove` of `child`
from `agent_active`, an `agent_parent_drop_child` (a pure key-filter — no re-appended edge, unlike
`delegate`'s `drop_endpoint`), a `VecMap.remove` of `child`'s caps, and a `clear_agent_state` wipe of
the seven per-agent maps. Every mutable field becomes `… ∧ · ≠ child` (or the key-filter), so the
post-image is *uniformly* "drop `child`".

It refines against `Rcasc` — the same ten-field slice as `Rdel`, but with the `agent_budget` clause
guarded by `agent_active`. The guard is forced: the kernel's "absent key = `bl5`" budget convention
disagrees with the abstract "removed ⇒ `False`" exactly on the just-removed (now inactive) agent, so
the faithful relation relates budget on active agents only (see `Rcasc`). The new bridging
(`vecMapGet_spec`, `vecSetRemove_spec`, `agentParentDropChild_spec`, `vmLastEntry_filter_removeKept`,
`optionAgentId_ne_spec`) lives in `Collections.lean`; the only new axiom beyond the `register_tool`
exemplar's residuals is `optionAgentId_ne_spec` (the `Option AgentId` disequality, same extractor
status as `agentId_ne_spec`), plus the pre-existing `AgentId.root` baseline shared by every
root-checking action. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- Inversion lemma for a successful `cascade_revoke` step. Peels the four gates — the parent-edge
    via `VecMap.get` + `Option.ne` (decoded to the get-style `vmLastEntry`), `prnt` inactive,
    `child` active, `child ≠ root` — and decodes the post-state's ten fields as the uniform
    "drop `child`" image: the `agent_active` remove, the `agent_parent` key-filter (needs the carried
    `vmNodupKeys` so the `drop_child` rebuild is the plain filter), the `agent_cap` remove, and the
    seven `clear_agent_state` removes. -/
theorem cascade_revoke_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (child prnt : types.AgentId)
    (hNodupP : vmNodupKeys st.agent_parent)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.cascade_revoke st bg child prnt = .ok (.Ok (st', ev))) :
    ∃ (rootVal : types.AgentId),
      vmLastEntry st.agent_parent.entries.val child = some (child, prnt) ∧
      ¬ vsMem st.agent_active prnt ∧
      vsMem st.agent_active child ∧
      types.AgentId.root = .ok rootVal ∧ child ≠ rootVal ∧
      (∀ y, vsMem st'.agent_active y ↔ vsMem st.agent_active y ∧ y ≠ child) ∧
      st'.agent_cap.entries.val = st.agent_cap.entries.val.filter (removeKept child) ∧
      st'.agent_parent.entries.val = st.agent_parent.entries.val.filter (removeKept child) ∧
      st'.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept child) ∧
      st'.in_flight.entries.val = st.in_flight.entries.val.filter (removeKept child) ∧
      st'.gh_taint_invoked.entries.val =
        st.gh_taint_invoked.entries.val.filter (removeKept child) ∧
      st'.gh_taint_received.entries.val =
        st.gh_taint_received.entries.val.filter (removeKept child) ∧
      st'.agent_instruction.entries.val =
        st.agent_instruction.entries.val.filter (removeKept child) ∧
      st'.override_used.entries.val = st.override_used.entries.val.filter (removeKept child) ∧
      st'.agent_budget.entries.val = st.agent_budget.entries.val.filter (removeKept child) := by
  simp only [transitions.cascade_revoke] at hok
  -- Gate 1: parent edge — `VecMap.get child = some prnt`.
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b, hbEq, hbIff⟩ :
      ∃ bb, core.option.Option.Insts.CoreCmpPartialEqOption.ne
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId) o (some prnt) =
        .ok bb ∧ (bb = true ↔ o ≠ some prnt) :=
    ⟨_, optionAgentId_ne_spec o (some prnt), by simp⟩
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = false := by cases b with | false => rfl | true => simp at hok
  simp only [hb, reduceIte, Bool.false_eq_true] at hok
  have hoP : o = some prnt := by
    by_contra hc
    have := hbIff.mpr hc; rw [hb] at this; simp at this
  have hlast : vmLastEntry st.agent_parent.entries.val child = some (child, prnt) := by
    have hoP' : (vmLastEntry st.agent_parent.entries.val child).map Prod.snd = some prnt := by
      rw [← ho]; exact hoP
    cases hL : vmLastEntry st.agent_parent.entries.val child with
    | none => rw [hL] at hoP'; simp at hoP'
    | some p =>
      have hp1 : p.1 = child := vmLastEntry_fst _ _ _ hL
      rw [hL, Option.map_some] at hoP'
      obtain ⟨a, c⟩ := p
      simp only [Option.some_inj] at hoP'
      simp_all
  -- Gate 2: `prnt` inactive.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active prnt)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = false := by cases b1 with | false => rfl | true => simp at hok
  simp only [hb1, reduceIte, Bool.false_eq_true] at hok
  -- Gate 3: `child` active.
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  -- Gate 4: `child ≠ root`.
  obtain ⟨rootVal, hrootEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hrootEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b3, hb3Eq, hb3Iff⟩ :
      ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq child rootVal = .ok bb ∧
        (bb = true ↔ child = rootVal) :=
    ⟨_, agentId_eq_spec child rootVal, by simp⟩
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  -- Body: remove active, drop-child parent, remove caps, clear.
  obtain ⟨vs, hvsEq, hvsMem⟩ :=
    spec_imp_exists (vecSetRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec agentId_clone_spec
      st.agent_active child)
  rw [hvsEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmChar⟩ :=
    spec_imp_exists (agentParentDropChild_spec st.agent_parent child hNodupP)
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, hvm1Char⟩ :=
    spec_imp_exists (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      st.agent_cap child)
  rw [hvm1Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨st1, hclearEq, hActiveF, hParentF, hCapF, hInvocF, hToolF, hTaint, hInflight,
    hGhInv, hGhRec, hInstr, hOverride, hBudget⟩ :=
    spec_imp_exists (clearAgentState_spec
      { st with agent_active := vs, agent_parent := vm, agent_cap := vm1 } child)
  rw [hclearEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _hev⟩ := hok
  subst hst
  refine ⟨rootVal, hlast, (by rw [← hb1Iff, hb1]; simp), hb2Iff.mp hb2, hrootEq,
    (fun h => by simp [hb3Iff.mpr h] at hb3),
    (fun y => by rw [hActiveF]; exact hvsMem y),
    (by rw [hCapF]; exact hvm1Char), (by rw [hParentF]; exact hvmChar),
    hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hBudget⟩

/-- Forward simulation: a successful `cascade_revoke` step is matched by the abstract action,
    preserving `Rcasc`. The witness `a'` is the uniform "drop `child`" image on all ten fields;
    `Rcasc`'s active-guarded budget clause is what makes the removed agent's budget mismatch
    (concrete reads `bl5` for the now-absent key, abstract drops it to `False`) unobservable. -/
theorem cascade_revoke_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (child prnt : types.AgentId)
    (hR : Rcasc st a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.cascade_revoke st bg child prnt = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.cascade_revoke child prnt).guard a ∧
          (Tzimtzum.cascade_revoke child prnt).next a a' ∧ Rcasc st' a' := by
  obtain ⟨hRroot, hRactive, hRcap, hRinstr, hRinflight, hRtaint, hRghinv, hRghrec,
    hRoverride, hRbudget, hRparent, hRnodup⟩ := hR
  obtain ⟨rootVal, hParentEdge, hPrntInactive, hChildActive, hrootEq, hchildNe,
    hActive, hCap, hParent, hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hBudget⟩ :=
    cascade_revoke_ok_inv st bg child prnt hRnodup st' ev hok
  have hrootId : a.root_agent = rootVal := by rw [hRroot] at hrootEq; exact Result.ok.inj hrootEq
  refine ⟨{ a with
      agent_active := fun A => a.agent_active A ∧ A ≠ child
      agent_parent := fun C P => a.agent_parent C P ∧ C ≠ child
      agent_cap := fun N C => a.agent_cap N C ∧ N ≠ child
      agent_instruction := fun A I => a.agent_instruction A I ∧ A ≠ child
      taint_levels := fun A L => a.taint_levels A L ∧ A ≠ child
      agent_budget := fun G L => a.agent_budget G L ∧ G ≠ child
      in_flight := fun A I => a.in_flight A I ∧ A ≠ child
      gh_taint_invoked := fun A L => a.gh_taint_invoked A L ∧ A ≠ child
      gh_taint_received := fun A L => a.gh_taint_received A L ∧ A ≠ child
      override_used := fun A T L => a.override_used A T L ∧ A ≠ child }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.cascade_revoke]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hRparent child prnt).mpr hParentEdge
    · exact fun h => hPrntInactive ((hRactive prnt).mp h)
    · exact (hRactive child).mpr hChildActive
    · rw [hrootId]; exact hchildNe
  · -- next
    simp [Tzimtzum.cascade_revoke]
  · -- Rcasc st' a'
    refine ⟨hRroot, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- agent_active
      intro x
      show (a.agent_active x ∧ x ≠ child) ↔ vsMem st'.agent_active x
      rw [hActive x, hRactive x]
    · -- agent_cap
      intro N C
      show (a.agent_cap N C ∧ N ≠ child) ↔ capMem st'.agent_cap N C
      rw [capMem_filter_removeKept st'.agent_cap st.agent_cap child hCap N C, hRcap N C]
    · -- agent_instruction
      intro ag ins
      show (a.agent_instruction ag ins ∧ ag ≠ child) ↔ vmsMem st'.agent_instruction ag ins
      rw [vmsMem_filter_removeKept _ _ _ hInstr, hRinstr]
    · -- in_flight
      intro ag inv
      show (a.in_flight ag inv ∧ ag ≠ child) ↔ vmsMem st'.in_flight ag inv
      rw [vmsMem_filter_removeKept _ _ _ hInflight, hRinflight]
    · -- taint_levels
      intro ag L
      show (a.taint_levels ag L ∧ ag ≠ child) ↔ vmsMem st'.taint_levels ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hTaint, hRtaint]
    · -- gh_taint_invoked
      intro ag L
      show (a.gh_taint_invoked ag L ∧ ag ≠ child) ↔ vmsMem st'.gh_taint_invoked ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hGhInv, hRghinv]
    · -- gh_taint_received
      intro ag L
      show (a.gh_taint_received ag L ∧ ag ≠ child) ↔ vmsMem st'.gh_taint_received ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hGhRec, hRghrec]
    · -- override_used
      intro ag t L
      show (a.override_used ag t L ∧ ag ≠ child) ↔
        vmsMem st'.override_used ag { tool := t, level := confC L }
      rw [vmsMem_filter_removeKept _ _ _ hOverride, hRoverride]
    · -- agent_budget (active-guarded)
      intro G L hactive'
      obtain ⟨hGactive, hGne⟩ := hactive'
      show (a.agent_budget G L ∧ G ≠ child) ↔
        ((G, budgetC L) ∈ st'.agent_budget.entries.val) ∨
        ((∀ bl, (G, bl) ∉ st'.agent_budget.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5)
      rw [hBudget]
      have hL : (a.agent_budget G L ∧ G ≠ child) ↔ a.agent_budget G L :=
        ⟨fun h => h.1, fun h => ⟨h, hGne⟩⟩
      rw [hL, hRbudget G L hGactive]
      constructor
      · rintro (hmem | ⟨hab, h5⟩)
        · exact Or.inl ((mem_filter_removeKept _ _ _ _).mpr ⟨hmem, hGne⟩)
        · exact Or.inr ⟨fun bl hc => hab bl ((mem_filter_removeKept _ _ _ _).mp hc).1, h5⟩
      · rintro (hmem | ⟨hab, h5⟩)
        · exact Or.inl ((mem_filter_removeKept _ _ _ _).mp hmem).1
        · exact Or.inr ⟨fun bl hc => hab bl ((mem_filter_removeKept _ _ _ _).mpr ⟨hc, hGne⟩), h5⟩
    · -- agent_parent (get-based, faithful under the carried key-uniqueness invariant)
      intro C P
      show (a.agent_parent C P ∧ C ≠ child) ↔
        vmLastEntry st'.agent_parent.entries.val C = some (C, P)
      rw [hParent, vmLastEntry_filter_removeKept]
      by_cases hC : C = child
      · simp [hC]
      · rw [if_neg hC, ← hRparent C P]; simp [hC]
    · -- agent_parent keys stay unique (filtering preserves key-Nodup)
      show vmNodupKeys st'.agent_parent
      unfold vmNodupKeys
      rw [hParent]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hRnodup

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms, the residuals are:
--   * The `register_tool` exemplar's `String`/id extractor residuals (`string_eq_spec` /
--     `string_clone_spec` / `agentId_ne_spec` + the opaque `String`/`AgentId` ops they pin), plus
--     one NEW residual of the same class: `optionAgentId_ne_spec` — the `Option AgentId`
--     disequality the parent-edge gate uses (`PartialEq::ne` is a default trait method Charon emits
--     as a bare axiom). No solver.
--   * From the EXTRACTED MODEL itself (not this proof): `sorryAx`,
--     `AgentId.root._native.decide.ax_1`, `…String.to_owned` are carried by the extracted
--     `types.AgentId.root` constant (Aeneas' String-literal model has a `sorry` placeholder), so
--     `transitions.cascade_revoke` — which gates on the root — depends on them a priori. The same
--     baseline every root-checking action inherits (`delegate` / `revoke` / `cascade_revoke`).
--     Verify with `#print axioms argus_kernel.types.AgentId.root`.
#print axioms ArgusLean.Refinement.cascade_revoke_ok_inv
#print axioms ArgusLean.Refinement.cascade_revoke_refines
