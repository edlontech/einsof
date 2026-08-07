import ArgusLean.Refinement.Unified.Preservation.ClearAgent

/-! # Layer 1 — `delegate` preserves the unified `R` (V4)

`delegate grantor grantee` spawns `grantee` as an active child of `grantor` with empty labels,
pending, challenges, and grants. It inserts `grantee` into `agent_active`, rebuilds `agent_parent`
by dropping every edge touching `grantee` (`delegate_loop1`, filter `parentKept`) and appending
`(grantee, grantor)`, removes `grantee`'s key from `agent_cap` / `taint_levels` / `integ_levels`,
and drops `grantee`'s pending / challenges / grants (reusing the `drop_*_of` specs). The reused-id
guard `∀ C, ¬ agent_parent C grantee` is computed by `delegate_loop0`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-- `delegate_loop0` decides whether some `agent_parent` edge has `grantee` as its parent value. -/
theorem delegateLoop0_spec (vm : collections.VecMap types.AgentId types.AgentId)
    (grantee : types.AgentId) (hnd : (vm.entries.val.map Prod.fst).Nodup)
    (start : Bool) (i0 : Usize) (hi0 : i0.val ≤ vm.entries.val.length)
    (hstart : start = true ↔ ∃ p ∈ vm.entries.val.take i0.val, p.2 = grantee) :
    transitions.delegate_loop0 vm grantee start i0 ⦃ b =>
      b = true ↔ ∃ p ∈ vm.entries.val, p.2 = grantee ⦄ := by
  unfold transitions.delegate_loop0
  apply loop.spec_decr_nat
    (measure := fun p => vm.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ vm.entries.val.length ∧
      (p.1 = true ↔ ∃ q ∈ vm.entries.val.take p.2.val, q.2 = grantee))
  · rintro ⟨found, i⟩ ⟨hile, hinv⟩
    simp only [transitions.delegate_loop0.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < vm.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone vm i hlt)
      rw [hkEq]; simp only [agentId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.AgentId.Insts.CoreCloneClone agentId_clone_spec vm k)
      have hlast : vmLastEntry vm.entries.val k =
          some ((vm.entries.val[i.val]'hlt).1, (vm.entries.val[i.val]'hlt).2) := by
        rw [hk]; exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, bind_tc_ok]
      have htk : (∃ q ∈ vm.entries.val.take (i.val + 1), q.2 = grantee) ↔
          (∃ q ∈ vm.entries.val.take i.val, q.2 = grantee)
            ∨ (vm.entries.val[i.val]'hlt).2 = grantee := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨q, hq | hq, hpe⟩
          · exact Or.inl ⟨q, hq, hpe⟩
          · exact Or.inr (by rw [← hq]; exact hpe)
        · rintro (⟨q, hq, hpe⟩ | hpe)
          · exact ⟨q, Or.inl hq, hpe⟩
          · exact ⟨_, Or.inr rfl, hpe⟩
      by_cases hpg : (vm.entries.val[i.val]'hlt).2 = grantee
      · simp only [hpg, decide_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk]
        exact iff_of_true trivial (Or.inr hpg)
      · simp only [hpg, decide_false, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        constructor
        · exact fun hh => Or.inl hh
        · rintro (hh | hh)
          · exact hh
          · exact absurd hh hpg
    case isFalse h =>
      have heq' : i.val = vm.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

/-- `delegate_loop1` rebuilds `agent_parent` keeping only edges whose child and parent both differ
    from `grantee` (`parentKept`). -/
theorem delegateLoop1_spec (vm : collections.VecMap types.AgentId types.AgentId)
    (grantee : types.AgentId) (hnd : (vm.entries.val.map Prod.fst).Nodup)
    (kept : collections.VecMap types.AgentId types.AgentId) (i0 : Usize)
    (hi0 : i0.val ≤ vm.entries.val.length)
    (hkept0 : kept.entries.val = (vm.entries.val.take i0.val).filter (parentKept grantee)) :
    transitions.delegate_loop1 vm grantee kept i0 ⦃ out =>
      out.entries.val = vm.entries.val.filter (parentKept grantee) ⦄ := by
  unfold transitions.delegate_loop1
  apply loop.spec_decr_nat
    (measure := fun p => vm.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ vm.entries.val.length ∧
      p.1.entries.val = (vm.entries.val.take p.2.val).filter (parentKept grantee))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [transitions.delegate_loop1.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < vm.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone vm i hlt)
      rw [hkEq]; simp only [agentId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.AgentId.Insts.CoreCloneClone agentId_clone_spec vm k)
      have hlast : vmLastEntry vm.entries.val k =
          some ((vm.entries.val[i.val]'hlt).1, (vm.entries.val[i.val]'hlt).2) := by
        rw [hk]; exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, bind_tc_ok]
      have hcapk : kept.entries.val.length < Usize.max := by
        have hle : kept.entries.val.length ≤ i.val := by
          rw [hkept]
          exact le_trans (List.length_filter_le _ _)
            (by rw [List.length_take]; exact Nat.min_le_left _ _)
        scalar_tac
      have hfresh : ∀ p ∈ kept.entries.val, p.1 ≠ k := by
        have hni := fst_getElem_not_mem_map_take vm.entries.val i.val hlt hnd
        rw [hkept]
        intro p hp hpc
        have hmem : p.1 ∈ (vm.entries.val.take i.val).map Prod.fst :=
          List.mem_map.mpr ⟨p, List.mem_of_mem_filter hp, rfl⟩
        rw [hpc, hk] at hmem
        exact hni hmem
      have hget : vm.entries.val[i.val]? =
          some ((vm.entries.val[i.val]'hlt).1, (vm.entries.val[i.val]'hlt).2) := by
        rw [List.getElem?_eq_getElem hlt]
      simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        agentId_eq_spec, bind_tc_ok]
      split
      · rename_i hbc
        have hcg : (vm.entries.val[i.val]'hlt).1 ≠ grantee := by rw [hk] at hbc; simpa using hbc
        split
        · rename_i hbp
          have hpg : (vm.entries.val[i.val]'hlt).2 ≠ grantee := by simpa using hbp
          obtain ⟨kept1, hkept1Eq, hkept1⟩ := spec_imp_exists
            (vecMapInsert_append_spec types.AgentId.Insts.CoreCloneClone
              types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
              types.AgentId.Insts.CoreCloneClone kept k (vm.entries.val[i.val]'hlt).2 hcapk hfresh)
          rw [hkept1Eq]; simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget,
            Option.toList_some, List.filter_append, ← hkept, hkept1, hk]
          simp [parentKept, hcg, hpg]
        · rename_i hbp
          have hpg : (vm.entries.val[i.val]'hlt).2 = grantee := by simpa using hbp
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget,
            Option.toList_some, List.filter_append, hkept]
          simp [parentKept, hpg]
      · rename_i hbc
        have hcg : (vm.entries.val[i.val]'hlt).1 = grantee := by rw [hk] at hbc; simpa using hbc
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget,
          Option.toList_some, List.filter_append, hkept]
        simp [parentKept, hcg]
    case isFalse h =>
      have heq' : i.val = vm.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hkept ⊢
      exact hkept
  · exact ⟨hi0, by simpa using hkept0⟩

/-- `delegate` preserves the unified `R`. -/
theorem delegate_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (grantor grantee : types.AgentId)
    (hR : R st bg a)
    (hcapActive : st.agent_active.items.val.length < Usize.max)
    (hcapParent : st.agent_parent.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.delegate st bg grantor grantee = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.delegate grantor grantee).guard a ∧
          (Tzimtzum.delegate grantor grantee).next a a' ∧ R st' bg a' := by
  simp only [transitions.delegate] at hok
  -- active grantor
  obtain ⟨bg0, hbg0Eq, hbg0Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantor)
  rw [hbg0Eq] at hok; simp only [bind_tc_ok] at hok
  have hbg0 : bg0 = true := by cases bg0 with | true => rfl | false => simp at hok
  simp only [hbg0, reduceIte] at hok
  -- ¬ active grantee
  obtain ⟨bg1, hbg1Eq, hbg1Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee)
  rw [hbg1Eq] at hok; simp only [bind_tc_ok] at hok
  have hbg1 : bg1 = false := by cases bg1 with | false => rfl | true => simp at hok
  simp only [hbg1, Bool.false_eq_true, reduceIte] at hok
  -- grantee ≠ root
  simp only [background.BackgroundTheory.impl.root_agent, agentId_eq_spec, bind_tc_ok] at hok
  split at hok
  · rename_i hroot; simp at hok
  · rename_i hroot
    have hgne : grantee ≠ bg.root_agent := by simpa using hroot
    -- ¬ grantee-is-parent
    obtain ⟨ip, hipEq, hipIff⟩ := spec_imp_exists
      (delegateLoop0_spec st.agent_parent grantee hR.ndParent false 0#usize (by simp) (by simp))
    rw [hipEq] at hok; simp only [bind_tc_ok] at hok
    have hip : ip = false := by cases ip with | false => rfl | true => simp at hok
    simp only [hip, Bool.false_eq_true, reduceIte] at hok
    -- insert grantee into active
    simp only [agentId_clone_spec, bind_tc_ok] at hok
    obtain ⟨vs, hvsEq, hvs⟩ := spec_imp_exists
      (vecSetInsert_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee
        hcapActive)
    rw [hvsEq] at hok; simp only [collections.VecMap.new, bind_tc_ok] at hok
    -- rebuild agent_parent: filter parentKept, then append (grantee, grantor)
    obtain ⟨kept1, hkept1Eq, hkept1⟩ := spec_imp_exists
      (delegateLoop1_spec st.agent_parent grantee hR.ndParent { entries := alloc.vec.Vec.new _ }
        0#usize (by scalar_tac) (by simp [List.take_zero]))
    rw [hkept1Eq] at hok; simp only [agentId_clone_spec, bind_tc_ok] at hok
    have hkept1nd : (kept1.entries.val.map Prod.fst).Nodup := by
      rw [hkept1]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndParent
    have hkept1cap : kept1.entries.val.length < Usize.max := by
      rw [hkept1]
      exact lt_of_le_of_lt (List.length_filter_le _ _) hcapParent
    have hkept1fresh : ∀ p ∈ kept1.entries.val, p.1 ≠ grantee := by
      rw [hkept1]; intro p hp
      have := List.of_mem_filter hp
      simp only [parentKept, decide_eq_true_eq] at this
      exact this.1
    obtain ⟨kept2, hkept2Eq, hkept2⟩ := spec_imp_exists
      (vecMapInsert_append_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.AgentId.Insts.CoreCloneClone kept1 grantee grantor hkept1cap hkept1fresh)
    rw [hkept2Eq] at hok; simp only [bind_tc_ok] at hok
    -- remove grantee from agent_cap / taint / integ
    obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
      (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
        (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
        st.agent_cap grantee)
    rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm1, hvm1Eq, hvm1⟩ := spec_imp_exists
      (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
        (collections.VecSet.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCloneClone)
        st.taint_levels grantee)
    rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm2, hvm2Eq, hvm2⟩ := spec_imp_exists
      (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
        (collections.VecSet.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCloneClone)
        st.integ_levels grantee)
    rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
    -- drop grantee's pending / challenges / grants
    set s0 : state.KernelState := { st with agent_active := vs, agent_parent := kept2, agent_cap := vm, taint_levels := vm1, integ_levels := vm2 } with hs0def
    obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1ch, hs1ci, hs1ca, hs1cc, hs1g, hs1tr,
        hs1pend⟩ := spec_imp_exists (dropPendingOf_spec s0 grantee hR.ndPending)
    rw [hs1Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨s2, hs2Eq, hs2a, hs2p, hs2c, hs2t, hs2i, hs2pend, hs2ci, hs2ca, hs2cc, hs2g, hs2tr,
        hs2ch⟩ := spec_imp_exists (dropChallengesOf_spec s1 grantee (by rw [hs1ch]; exact hR.ndChallenges))
    rw [hs2Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨s3, hs3Eq, hs3a, hs3p, hs3c, hs3t, hs3i, hs3pend, hs3ch, hs3ci, hs3ca, hs3cc, hs3tr,
        hs3g⟩ := spec_imp_exists (dropGrantsOf_spec s2 grantee (by rw [hs2g, hs1g]; exact hR.ndGrants))
    rw [hs3Eq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _hEv⟩ := hok
    subst hStateEq
    -- assemble s3 field characterizations (s3 = s3)
    have hs3active : ∀ y, vsMem s3.agent_active y ↔ vsMem st.agent_active y ∨ y = grantee := by
      intro y; rw [hs3a, hs2a, hs1a]; exact hvs y
    have hs3parent : s3.agent_parent.entries.val =
        st.agent_parent.entries.val.filter (parentKept grantee) ++ [(grantee, grantor)] := by
      rw [hs3p, hs2p, hs1p]; show s0.agent_parent.entries.val = _; rw [hs0def]; show kept2.entries.val = _
      rw [hkept2, hkept1]
    have hs3cap : s3.agent_cap.entries.val = st.agent_cap.entries.val.filter (removeKept grantee) := by
      rw [hs3c, hs2c, hs1c]; show s0.agent_cap.entries.val = _; rw [hs0def]; show vm.entries.val = _; exact hvm
    have hs3taint : s3.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept grantee) := by
      rw [hs3t, hs2t, hs1t]; show s0.taint_levels.entries.val = _; rw [hs0def]; show vm1.entries.val = _; exact hvm1
    have hs3integ : s3.integ_levels.entries.val = st.integ_levels.entries.val.filter (removeKept grantee) := by
      rw [hs3i, hs2i, hs1i]; show s0.integ_levels.entries.val = _; rw [hs0def]; show vm2.entries.val = _; exact hvm2
    have hs3pend : s3.pending.entries.val = st.pending.entries.val.filter (keepAgentP (·.agent) grantee) := by
      rw [hs3pend, hs2pend]; exact hs1pend
    have hs3chal : s3.challenges.entries.val = st.challenges.entries.val.filter (keepAgentP (·.agent) grantee) := by
      rw [hs3ch, hs2ch, hs1ch]
    have hs3grant : s3.crossing_grants.entries.val = st.crossing_grants.entries.val.filter (keepGrantP grantee) := by
      rw [hs3g, hs2g, hs1g]
    have hs3ci : s3.consumed_ids = st.consumed_ids := by rw [hs3ci, hs2ci, hs1ci]
    have hs3ca : s3.consumed_attestations = st.consumed_attestations := by rw [hs3ca, hs2ca, hs1ca]
    have hs3cc : s3.consumed_crossings = st.consumed_crossings := by rw [hs3cc, hs2cc, hs1cc]
    have hs3tr : s3.tool_registered = st.tool_registered := by rw [hs3tr, hs2tr, hs1tr]
    -- nodup invariants
    have hndActive := hR.ndParent
    have hs3ndParent : vmNodupKeys s3.agent_parent := by
      unfold vmNodupKeys; rw [hs3parent]; exact parentPost_nodupKeys _ grantee grantor hR.ndParent
    have hs3ndCap : vmNodupKeys s3.agent_cap := by
      unfold vmNodupKeys; rw [hs3cap]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndCap
    have hs3ndTaint : vmNodupKeys s3.taint_levels := by
      unfold vmNodupKeys; rw [hs3taint]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndTaint
    have hs3ndInteg : vmNodupKeys s3.integ_levels := by
      unfold vmNodupKeys; rw [hs3integ]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndInteg
    have hs3ndPend : vmNodupKeys s3.pending := by
      unfold vmNodupKeys; rw [hs3pend]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndPending
    have hs3ndChal : vmNodupKeys s3.challenges := by
      unfold vmNodupKeys; rw [hs3chal]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndChallenges
    have hs3ndGrant : vmNodupKeys s3.crossing_grants := by
      unfold vmNodupKeys; rw [hs3grant]
      exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndGrants
    refine ⟨{ a with
        agent_active := fun A => a.agent_active A ∨ A = grantee,
        agent_parent := fun C P => (C = grantee ∧ P = grantor) ∨
          (a.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee),
        agent_cap := fun A C => a.agent_cap A C ∧ A ≠ grantee,
        taint_levels := fun A L => a.taint_levels A L ∧ A ≠ grantee,
        integ_levels := fun A L => a.integ_levels A L ∧ A ≠ grantee,
        pending := Tzimtzum.dropPendingOf a.pending grantee,
        challenges := Tzimtzum.dropChallengesOf a.challenges grantee,
        crossing_grants := Tzimtzum.dropGrantsOf a.crossing_grants grantee }, ?_, ?_, ?_⟩
    · -- guard
      simp only [Tzimtzum.delegate]
      refine ⟨(hR.active grantor).mpr (hbg0Iff.mp hbg0), ?_, ?_, ?_⟩
      · rw [hR.active grantee]; intro hc
        have := hbg1Iff.mpr hc; rw [hbg1] at this; exact Bool.false_ne_true this
      · rw [hR.root]; exact hgne
      · intro C hc
        have hex : ∃ p ∈ st.agent_parent.entries.val, p.2 = grantee := by
          have hpe : vmLastEntry st.agent_parent.entries.val C = some (C, grantee) :=
            (hR.parent C grantee).mp hc
          exact ⟨(C, grantee), vmLastEntry_mem _ _ _ hpe, rfl⟩
        have := hipIff.mpr hex; rw [hip] at this; exact Bool.false_ne_true this
    · -- next
      simp [Tzimtzum.delegate]
    · -- R s3 bg a'
      refine
        { root := hR.root, mode := hR.mode
          active := ?_, tool_reg := ?_, parent := ?_, cap := ?_, taint := ?_, integ := ?_
          pending := pending_clause_filtered st s3 a grantee hR.pending hR.ndPending hs3pend
          challenges := challenges_clause_filtered st s3 a grantee hR.challenges hR.ndChallenges hs3chal
          grants := grants_clause_filtered st s3 a grantee hR.grants hR.ndGrants hs3grant
          consumedIds := ?_, consumedAtt := ?_, consumedCross := ?_
          flowAllows := hR.flowAllows, flowInspects := hR.flowInspects
          ndParent := hs3ndParent, ndCap := hs3ndCap, ndTaint := hs3ndTaint, ndInteg := hs3ndInteg
          ndPending := hs3ndPend, ndChallenges := hs3ndChal, ndGrants := hs3ndGrant }
      · intro y; show (a.agent_active y ∨ y = grantee) ↔ vsMem s3.agent_active y
        rw [hs3active y, hR.active y]
      · intro t; show a.tool_registered t ↔ vsMem s3.tool_registered t
        rw [show s3.tool_registered = st.tool_registered from hs3tr, hR.tool_reg t]
      · intro C P
        show ((C = grantee ∧ P = grantor) ∨ (a.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)) ↔
          vmLastEntry s3.agent_parent.entries.val C = some (C, P)
        rw [hs3parent, parentPost_vmLast _ grantee grantor C P hR.ndParent, hR.parent C P]
      · intro N C
        show (a.agent_cap N C ∧ N ≠ grantee) ↔ vmsMemLast s3.agent_cap N C
        rw [vmsMemLast_filter_removeKept s3.agent_cap st.agent_cap grantee hs3cap, ← hR.cap N C]
      · intro ag L
        show (a.taint_levels ag L ∧ ag ≠ grantee) ↔ vmsMemLast s3.taint_levels ag (confC L)
        rw [vmsMemLast_filter_removeKept s3.taint_levels st.taint_levels grantee hs3taint,
          ← hR.taint ag L]
      · intro ag L
        show (a.integ_levels ag L ∧ ag ≠ grantee) ↔ vmsMemLast s3.integ_levels ag (integC L)
        rw [vmsMemLast_filter_removeKept s3.integ_levels st.integ_levels grantee hs3integ,
          ← hR.integ ag L]
      · intro I; rw [show s3.consumed_ids = st.consumed_ids from hs3ci]; exact hR.consumedIds I
      · intro Att; rw [show s3.consumed_attestations = st.consumed_attestations from hs3ca]
        exact hR.consumedAtt Att
      · intro X; rw [show s3.consumed_crossings = st.consumed_crossings from hs3cc]
        exact hR.consumedCross X

end ArgusLean.Refinement
