import ArgusLean.Refinement.StateRelation

/-! # Refinement — `revoke` (10/10 fields)

`revoke prnt target` is the *direct* removal action — the sibling of `cascade_revoke`. The four
gates differ only in one polarity: `prnt` must be **active** (a live parent revoking its own child),
whereas `cascade_revoke` requires `prnt` *inactive* (cleaning up under an already-revoked parent).
Otherwise it is identical: parent edge `target → prnt`, `target` active, `target ≠ root`, then the
uniform "drop `target`" image (`VecSet.remove`, `agent_parent_drop_child`, `VecMap.remove`,
`clear_agent_state`).

It refines against the same `Rcasc` as `cascade_revoke` (the active-guarded-budget variant of `Rdel`):
`target` ends inactive, so the kernel's "absent ⇒ `bl5`" budget convention is again only observable on
active agents. All bridging is shared with `cascade_revoke` (`vecMapGet_spec`, `vecSetRemove_spec`,
`agentParentDropChild_spec`, `vmLastEntry_filter_removeKept`, `optionAgentId_ne_spec`); this file adds
no new axioms. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- Inversion lemma for a successful `revoke` step. Peels the four gates — the parent-edge via
    `VecMap.get` + `Option.ne`, `prnt` **active**, `target` active, `target ≠ root` — and decodes the
    post-state's ten fields as the uniform "drop `target`" image (needs the carried `vmNodupKeys` for
    the `agent_parent_drop_child` rebuild). -/
theorem revoke_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (prnt target : types.AgentId)
    (hNodupP : vmNodupKeys st.agent_parent)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.revoke st bg prnt target = .ok (.Ok (st', ev))) :
    ∃ (rootVal : types.AgentId),
      vmLastEntry st.agent_parent.entries.val target = some (target, prnt) ∧
      vsMem st.agent_active prnt ∧
      vsMem st.agent_active target ∧
      types.AgentId.root = .ok rootVal ∧ target ≠ rootVal ∧
      (∀ y, vsMem st'.agent_active y ↔ vsMem st.agent_active y ∧ y ≠ target) ∧
      st'.agent_cap.entries.val = st.agent_cap.entries.val.filter (removeKept target) ∧
      st'.agent_parent.entries.val = st.agent_parent.entries.val.filter (removeKept target) ∧
      st'.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept target) ∧
      st'.in_flight.entries.val = st.in_flight.entries.val.filter (removeKept target) ∧
      st'.gh_taint_invoked.entries.val =
        st.gh_taint_invoked.entries.val.filter (removeKept target) ∧
      st'.gh_taint_received.entries.val =
        st.gh_taint_received.entries.val.filter (removeKept target) ∧
      st'.agent_instruction.entries.val =
        st.agent_instruction.entries.val.filter (removeKept target) ∧
      st'.override_used.entries.val = st.override_used.entries.val.filter (removeKept target) ∧
      st'.agent_budget.entries.val = st.agent_budget.entries.val.filter (removeKept target) := by
  simp only [transitions.revoke] at hok
  -- Gate 1: parent edge — `VecMap.get target = some prnt`.
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent target)
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
  have hlast : vmLastEntry st.agent_parent.entries.val target = some (target, prnt) := by
    have hoP' : (vmLastEntry st.agent_parent.entries.val target).map Prod.snd = some prnt := by
      rw [← ho]; exact hoP
    cases hL : vmLastEntry st.agent_parent.entries.val target with
    | none => rw [hL] at hoP'; simp at hoP'
    | some p =>
      have hp1 : p.1 = target := vmLastEntry_fst _ _ _ hL
      rw [hL, Option.map_some] at hoP'
      obtain ⟨a, c⟩ := p
      simp only [Option.some_inj] at hoP'
      simp_all
  -- Gate 2: `prnt` active.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active prnt)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  -- Gate 3: `target` active.
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active target)
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  -- Gate 4: `target ≠ root`.
  obtain ⟨rootVal, hrootEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hrootEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b3, hb3Eq, hb3Iff⟩ :
      ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq target rootVal = .ok bb ∧
        (bb = true ↔ target = rootVal) :=
    ⟨_, agentId_eq_spec target rootVal, by simp⟩
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  -- Body: remove active, drop-child parent, remove caps, clear.
  obtain ⟨vs, hvsEq, hvsMem⟩ :=
    spec_imp_exists (vecSetRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec agentId_clone_spec
      st.agent_active target)
  rw [hvsEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmChar⟩ :=
    spec_imp_exists (agentParentDropChild_spec st.agent_parent target hNodupP)
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, hvm1Char⟩ :=
    spec_imp_exists (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      st.agent_cap target)
  rw [hvm1Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨st1, hclearEq, hActiveF, hParentF, hCapF, hInvocF, hToolF, hTaint, hInflight,
    hGhInv, hGhRec, hInstr, hOverride, hBudget⟩ :=
    spec_imp_exists (clearAgentState_spec
      { st with agent_active := vs, agent_parent := vm, agent_cap := vm1 } target)
  rw [hclearEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _hev⟩ := hok
  subst hst
  refine ⟨rootVal, hlast, hb1Iff.mp hb1, hb2Iff.mp hb2, hrootEq,
    (fun h => by simp [hb3Iff.mpr h] at hb3),
    (fun y => by rw [hActiveF]; exact hvsMem y),
    (by rw [hCapF]; exact hvm1Char), (by rw [hParentF]; exact hvmChar),
    hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hBudget⟩

/-- Forward simulation: a successful `revoke` step is matched by the abstract action, preserving
    `Rcasc` (shared with `cascade_revoke`; the witness `a'` is the uniform "drop `target`" image and
    the active-guarded budget clause absorbs the removed agent's `bl5`-vs-`False` mismatch). -/
theorem revoke_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (prnt target : types.AgentId)
    (hR : Rcasc st a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.revoke st bg prnt target = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.revoke prnt target).guard a ∧
          (Tzimtzum.revoke prnt target).next a a' ∧ Rcasc st' a' := by
  obtain ⟨hRroot, hRactive, hRcap, hRinstr, hRinflight, hRtaint, hRghinv, hRghrec,
    hRoverride, hRbudget, hRparent, hRnodup⟩ := hR
  obtain ⟨rootVal, hParentEdge, hPrntActive, hTargetActive, hrootEq, htargetNe,
    hActive, hCap, hParent, hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hBudget⟩ :=
    revoke_ok_inv st bg prnt target hRnodup st' ev hok
  have hrootId : a.root_agent = rootVal := by rw [hRroot] at hrootEq; exact Result.ok.inj hrootEq
  refine ⟨{ a with
      agent_active := fun A => a.agent_active A ∧ A ≠ target
      agent_parent := fun C P => a.agent_parent C P ∧ C ≠ target
      agent_cap := fun N C => a.agent_cap N C ∧ N ≠ target
      agent_instruction := fun A I => a.agent_instruction A I ∧ A ≠ target
      taint_levels := fun A L => a.taint_levels A L ∧ A ≠ target
      agent_budget := fun G L => a.agent_budget G L ∧ G ≠ target
      in_flight := fun A I => a.in_flight A I ∧ A ≠ target
      gh_taint_invoked := fun A L => a.gh_taint_invoked A L ∧ A ≠ target
      gh_taint_received := fun A L => a.gh_taint_received A L ∧ A ≠ target
      override_used := fun A T L => a.override_used A T L ∧ A ≠ target }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.revoke]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hRparent target prnt).mpr hParentEdge
    · exact (hRactive prnt).mpr hPrntActive
    · exact (hRactive target).mpr hTargetActive
    · rw [hrootId]; exact htargetNe
  · -- next
    simp [Tzimtzum.revoke]
  · -- Rcasc st' a'
    refine ⟨hRroot, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- agent_active
      intro x
      show (a.agent_active x ∧ x ≠ target) ↔ vsMem st'.agent_active x
      rw [hActive x, hRactive x]
    · -- agent_cap
      intro N C
      show (a.agent_cap N C ∧ N ≠ target) ↔ capMem st'.agent_cap N C
      rw [capMem_filter_removeKept st'.agent_cap st.agent_cap target hCap N C, hRcap N C]
    · -- agent_instruction
      intro ag ins
      show (a.agent_instruction ag ins ∧ ag ≠ target) ↔ vmsMem st'.agent_instruction ag ins
      rw [vmsMem_filter_removeKept _ _ _ hInstr, hRinstr]
    · -- in_flight
      intro ag inv
      show (a.in_flight ag inv ∧ ag ≠ target) ↔ vmsMem st'.in_flight ag inv
      rw [vmsMem_filter_removeKept _ _ _ hInflight, hRinflight]
    · -- taint_levels
      intro ag L
      show (a.taint_levels ag L ∧ ag ≠ target) ↔ vmsMem st'.taint_levels ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hTaint, hRtaint]
    · -- gh_taint_invoked
      intro ag L
      show (a.gh_taint_invoked ag L ∧ ag ≠ target) ↔ vmsMem st'.gh_taint_invoked ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hGhInv, hRghinv]
    · -- gh_taint_received
      intro ag L
      show (a.gh_taint_received ag L ∧ ag ≠ target) ↔ vmsMem st'.gh_taint_received ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hGhRec, hRghrec]
    · -- override_used
      intro ag t L
      show (a.override_used ag t L ∧ ag ≠ target) ↔
        vmsMem st'.override_used ag { tool := t, level := confC L }
      rw [vmsMem_filter_removeKept _ _ _ hOverride, hRoverride]
    · -- agent_budget (active-guarded)
      intro G L hactive'
      obtain ⟨hGactive, hGne⟩ := hactive'
      show (a.agent_budget G L ∧ G ≠ target) ↔
        ((G, budgetC L) ∈ st'.agent_budget.entries.val) ∨
        ((∀ bl, (G, bl) ∉ st'.agent_budget.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5)
      rw [hBudget]
      have hL : (a.agent_budget G L ∧ G ≠ target) ↔ a.agent_budget G L :=
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
      show (a.agent_parent C P ∧ C ≠ target) ↔
        vmLastEntry st'.agent_parent.entries.val C = some (C, P)
      rw [hParent, vmLastEntry_filter_removeKept]
      by_cases hC : C = target
      · simp [hC]
      · rw [if_neg hC, ← hRparent C P]; simp [hC]
    · -- agent_parent keys stay unique (filtering preserves key-Nodup)
      show vmNodupKeys st'.agent_parent
      unfold vmNodupKeys
      rw [hParent]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hRnodup

end ArgusLean.Refinement

-- Trust-base audit. Identical residual set to `cascade_revoke` (shared bridging): the three standard
-- axioms, the extracted-model `sorryAx`/`AgentId.root` baseline (root-checking action), the
-- `register_tool` `String`/id residuals, and `optionAgentId_ne_spec` (the `Option AgentId` gate
-- disequality). No new axioms; no solver.
#print axioms ArgusLean.Refinement.revoke_ok_inv
#print axioms ArgusLean.Refinement.revoke_refines
