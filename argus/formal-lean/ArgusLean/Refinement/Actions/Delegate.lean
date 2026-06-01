import ArgusLean.Refinement.StateRelation

/-! # Refinement — `delegate` (9/10 fields)

`delegate grantor grantee` is the largest structural action: three gates (grantor active,
grantee inactive, grantee ≠ root) followed by an `agent_active` insert, an `agent_parent`
rewrite (`agent_parent_drop_endpoint` + insert), an empty-cap insert, and a
`clear_agent_state` wipe of the grantee from seven per-agent maps.

This proves the simulation against `Rdel`, the slice over the **nine** fields whose abstract
post-image is recoverable without a key-uniqueness invariant. The tenth, `agent_parent`, is
genuinely *not* provable here: `agent_parent_drop_endpoint` re-inserts entries under
`VecMap` last-match semantics, which disagrees with the abstract `agent_parent` clause unless
`st.agent_parent` has unique keys. That field is deferred to the unified `R` (where the
well-formedness invariant lives); here the witness simply sets it to the abstract clause to
satisfy `next`, and `Rdel` does not constrain it. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- Inversion lemma for a successful `delegate` step. Peels the three gates and decodes the
    post-state's nine `Rdel` fields: the `agent_active` insert (`hActive`), the empty-cap
    insert under last-match get-semantics (`hCap` + the inserted set is empty), and the seven
    `clear_agent_state` removes as key-filtered entry lists. The `agent_parent` rewrite is only
    stepped over (success forces `.ok`), never characterised. -/
theorem delegate_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (grantor grantee : types.AgentId)
    (hcapA : st.agent_active.items.val.length < Usize.max)
    (hcapC : st.agent_cap.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.delegate st bg grantor grantee = .ok (.Ok (st', ev))) :
    ∃ (vs1 : collections.VecSet capability.CapKind) (rootVal : types.AgentId),
      vsMem st.agent_active grantor ∧
      ¬ vsMem st.agent_active grantee ∧
      types.AgentId.root = .ok rootVal ∧ grantee ≠ rootVal ∧
      vs1.items.val = [] ∧
      (∀ y, vsMem st'.agent_active y ↔ vsMem st.agent_active y ∨ y = grantee) ∧
      (∀ j, vmLastEntry st'.agent_cap.entries.val j =
        if j = grantee then some (grantee, vs1) else vmLastEntry st.agent_cap.entries.val j) ∧
      st'.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept grantee) ∧
      st'.in_flight.entries.val = st.in_flight.entries.val.filter (removeKept grantee) ∧
      st'.gh_taint_invoked.entries.val =
        st.gh_taint_invoked.entries.val.filter (removeKept grantee) ∧
      st'.gh_taint_received.entries.val =
        st.gh_taint_received.entries.val.filter (removeKept grantee) ∧
      st'.agent_instruction.entries.val =
        st.agent_instruction.entries.val.filter (removeKept grantee) ∧
      st'.override_used.entries.val = st.override_used.entries.val.filter (removeKept grantee) ∧
      st'.agent_budget.entries.val = st.agent_budget.entries.val.filter (removeKept grantee) := by
  simp only [transitions.delegate] at hok
  -- Gate 1: grantor active.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantor)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- Gate 2: grantee inactive.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = false := by cases b1 with | false => rfl | true => simp at hok
  simp only [hb1, reduceIte, Bool.false_eq_true] at hok
  -- Gate 3: grantee ≠ root.
  obtain ⟨rootVal, hrootEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hrootEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :
      ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq grantee rootVal = .ok bb ∧
        (bb = true ↔ grantee = rootVal) :=
    ⟨_, agentId_eq_spec grantee rootVal, by simp⟩
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = false := by cases b2 with | false => rfl | true => simp at hok
  simp only [hb2, reduceIte, Bool.false_eq_true] at hok
  -- Inserts: clones collapse to identity.
  simp only [agentId_clone_spec, bind_tc_ok] at hok
  -- active insert
  obtain ⟨vs, hvsEq, hvsMem⟩ :=
    spec_imp_exists (vecSetInsert_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee hcapA)
  rw [hvsEq] at hok
  simp only [bind_tc_ok] at hok
  -- agent_parent rewrite (deferred): just force `.ok`.
  obtain ⟨vm, hvmEq⟩ : ∃ m, transitions.agent_parent_drop_endpoint st.agent_parent grantee = .ok m := by
    cases h : transitions.agent_parent_drop_endpoint st.agent_parent grantee with
    | ok m => exact ⟨m, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq⟩ : ∃ m,
      collections.VecMap.insert types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone
        vm grantee grantor = .ok m := by
    cases h : collections.VecMap.insert types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone
        vm grantee grantor with
    | ok m => exact ⟨m, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hvm1Eq] at hok
  simp only [collections.VecSet.new, bind_tc_ok] at hok
  -- empty-cap insert
  obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ :=
    spec_imp_exists (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec _ st.agent_cap grantee
      { items := alloc.vec.Vec.new capability.CapKind } hcapC)
  rw [hvm2Eq] at hok
  simp only [bind_tc_ok] at hok
  -- clear_agent_state
  obtain ⟨st1, hclearEq, hActiveF, hParentF, hCapF, hInvocF, hToolF, hTaint, hInflight,
    hGhInv, hGhRec, hInstr, hOverride, hBudget⟩ :=
    spec_imp_exists (clearAgentState_spec
      { st with agent_active := vs, agent_parent := vm1, agent_cap := vm2 } grantee)
  rw [hclearEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _hev⟩ := hok
  subst hst
  refine ⟨{ items := alloc.vec.Vec.new capability.CapKind }, rootVal, hbIff.mp hb,
    (by rw [← hb1Iff, hb1]; simp), hrootEq, (fun h => by simp [hb2Iff.mpr h] at hb2), rfl,
    (fun y => by rw [hActiveF]; exact hvsMem y), (fun j => by rw [hCapF]; exact hvm2Mem j),
    hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hBudget⟩

/-- Forward simulation: a successful `delegate` step is matched by the abstract action,
    preserving `Rdel` (the nine non-`agent_parent` fields). The witness sets `agent_parent` to
    the abstract clause purely to satisfy `next`; `Rdel` does not relate it. -/
theorem delegate_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (grantor grantee : types.AgentId)
    (hR : Rdel st a)
    (hcapA : st.agent_active.items.val.length < Usize.max)
    (hcapC : st.agent_cap.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.delegate st bg grantor grantee = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.delegate grantor grantee).guard a ∧
          (Tzimtzum.delegate grantor grantee).next a a' ∧ Rdel st' a' := by
  obtain ⟨hRroot, hRactive, hRcap, hRinstr, hRinflight, hRtaint, hRghinv, hRghrec,
    hRoverride, hRbudget⟩ := hR
  obtain ⟨vs1, rootVal, hgrantor, hgrantee, hrootEq, hgrne, hvs1empty, hActive, hCap,
    hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hBudget⟩ :=
    delegate_ok_inv st bg grantor grantee hcapA hcapC st' ev hok
  have hrootId : a.root_agent = rootVal := by rw [hRroot] at hrootEq; exact Result.ok.inj hrootEq
  refine ⟨{ a with
      agent_active := fun A => a.agent_active A ∨ A = grantee
      agent_parent := fun C P =>
        (C = grantee ∧ P = grantor) ∨ (a.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)
      agent_cap := fun N C => a.agent_cap N C ∧ N ≠ grantee
      agent_instruction := fun A I => a.agent_instruction A I ∧ A ≠ grantee
      taint_levels := fun A L => a.taint_levels A L ∧ A ≠ grantee
      agent_budget := fun G L =>
        (G = grantee ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (a.agent_budget G L ∧ G ≠ grantee)
      in_flight := fun A I => a.in_flight A I ∧ A ≠ grantee
      gh_taint_invoked := fun A L => a.gh_taint_invoked A L ∧ A ≠ grantee
      gh_taint_received := fun A L => a.gh_taint_received A L ∧ A ≠ grantee
      override_used := fun A T L => a.override_used A T L ∧ A ≠ grantee }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.delegate]
    refine ⟨?_, ?_, ?_⟩
    · rw [hRactive]; exact hgrantor
    · rw [hRactive]; exact hgrantee
    · rw [hrootId]; exact hgrne
  · -- next
    simp [Tzimtzum.delegate]
  · -- Rdel st' a'
    refine ⟨hRroot, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- agent_active
      intro x
      show (a.agent_active x ∨ x = grantee) ↔ vsMem st'.agent_active x
      rw [hActive x, hRactive x]
    · -- agent_cap (get-based)
      intro N C
      show (a.agent_cap N C ∧ N ≠ grantee) ↔ capMem st'.agent_cap N C
      by_cases hN : N = grantee
      · have hc : capMem st'.agent_cap N C ↔ False := by
          simp only [capMem, hCap N, if_pos hN]
          simp [hvs1empty]
        rw [hc]; simp [hN]
      · have hc : capMem st'.agent_cap N C ↔ capMem st.agent_cap N C := by
          simp only [capMem, hCap N, if_neg hN]
        rw [hc, ← hRcap N]; simp [hN]
    · -- agent_instruction
      intro ag ins
      show (a.agent_instruction ag ins ∧ ag ≠ grantee) ↔ vmsMem st'.agent_instruction ag ins
      rw [vmsMem_filter_removeKept _ _ _ hInstr, hRinstr]
    · -- in_flight
      intro ag inv
      show (a.in_flight ag inv ∧ ag ≠ grantee) ↔ vmsMem st'.in_flight ag inv
      rw [vmsMem_filter_removeKept _ _ _ hInflight, hRinflight]
    · -- taint_levels
      intro ag L
      show (a.taint_levels ag L ∧ ag ≠ grantee) ↔ vmsMem st'.taint_levels ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hTaint, hRtaint]
    · -- gh_taint_invoked
      intro ag L
      show (a.gh_taint_invoked ag L ∧ ag ≠ grantee) ↔ vmsMem st'.gh_taint_invoked ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hGhInv, hRghinv]
    · -- gh_taint_received
      intro ag L
      show (a.gh_taint_received ag L ∧ ag ≠ grantee) ↔ vmsMem st'.gh_taint_received ag (confC L)
      rw [vmsMem_filter_removeKept _ _ _ hGhRec, hRghrec]
    · -- override_used
      intro ag t L
      show (a.override_used ag t L ∧ ag ≠ grantee) ↔
        vmsMem st'.override_used ag { tool := t, level := confC L }
      rw [vmsMem_filter_removeKept _ _ _ hOverride, hRoverride]
    · -- agent_budget
      intro G L
      show ((G = grantee ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (a.agent_budget G L ∧ G ≠ grantee)) ↔
        ((G, budgetC L) ∈ st'.agent_budget.entries.val) ∨
        ((∀ bl, (G, bl) ∉ st'.agent_budget.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5)
      rw [hBudget]
      by_cases hG : G = grantee
      · constructor
        · intro h
          refine Or.inr ⟨fun bl => by rw [mem_filter_removeKept]; simp [hG], ?_⟩
          rcases h with ⟨_, hL5⟩ | ⟨_, hne⟩
          · exact hL5
          · exact absurd hG hne
        · rintro (hmem | ⟨_, hL5⟩)
          · rw [mem_filter_removeKept] at hmem; simp [hG] at hmem
          · exact Or.inl ⟨hG, hL5⟩
      · have hL : ((G = grantee ∧ L = Tzimtzum.BudgetLevel.bl5) ∨
            (a.agent_budget G L ∧ G ≠ grantee)) ↔ a.agent_budget G L := by
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩)
            · exact absurd h hG
            · exact h
          · intro h; exact Or.inr ⟨h, hG⟩
        have hR : (((G, budgetC L) ∈ st.agent_budget.entries.val.filter (removeKept grantee)) ∨
            ((∀ bl, (G, bl) ∉ st.agent_budget.entries.val.filter (removeKept grantee)) ∧
              L = Tzimtzum.BudgetLevel.bl5)) ↔ a.agent_budget G L := by
          rw [hRbudget]
          constructor
          · rintro (hmem | ⟨hab, h5⟩)
            · exact Or.inl ((mem_filter_removeKept _ _ _ _).mp hmem).1
            · exact Or.inr ⟨fun bl hc => hab bl ((mem_filter_removeKept _ _ _ _).mpr ⟨hc, hG⟩), h5⟩
          · rintro (hmem | ⟨hab, h5⟩)
            · exact Or.inl ((mem_filter_removeKept _ _ _ _).mpr ⟨hmem, hG⟩)
            · exact Or.inr ⟨fun bl hc => hab bl ((mem_filter_removeKept _ _ _ _).mp hc).1, h5⟩
        rw [hL, hR]

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms, the residuals split in two:
--   * From the refinement (same class as the `register_tool` exemplar): the documented
--     `String`/id extractor pins `string_eq_spec` / `string_clone_spec` / `agentId_ne_spec`
--     (+ the opaque `String.eq` / `String.clone` / `AgentId.ne` / `CapKind.ne` they pin). No
--     solver.
--   * From the EXTRACTED MODEL itself, not this proof: `sorryAx`,
--     `AgentId.root._native.decide.ax_1` and `…String.to_owned` are carried by the extracted
--     `types.AgentId.root` constant (Aeneas' String-literal model has a `sorry` placeholder),
--     so `transitions.delegate` — which gates on the root — depends on them a priori. Every
--     root-checking action (`delegate` / `revoke` / `cascade_revoke`) inherits this baseline;
--     `register_tool` is clean only because it never names the root. Verify with
--     `#print axioms argus_kernel.types.AgentId.root`.
#print axioms ArgusLean.Refinement.delegate_ok_inv
#print axioms ArgusLean.Refinement.delegate_refines
