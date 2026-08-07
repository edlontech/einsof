import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `clear_agent` and the `drop_*_of` filter rebuilds (V4)

`revoke` / `cascade_revoke` destroy an agent via `transitions.clear_agent`, and `delegate` reuses the
`drop_*_of` filters to clear a reused-id grantee. `clear_agent agent` removes `agent` from
`agent_active`, `VecMap.remove`s its key from `agent_parent` / `agent_cap` / `taint_levels` /
`integ_levels`, then rebuilds `pending` / `challenges` / `crossing_grants` keeping only the records
whose agent (value's `agent` for pending/challenges, key's `agent` for grants) differs from the
removed one. Each `drop_*_of` loop scans the original map (`key_at` + last-match `get_cloned`) and
re-inserts kept entries; under `vmNodupKeys` each key is fresh in the accumulator, so the rebuild is
exactly a `List.filter` and the last-match view collapses to the abstract `drop*Of`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-- Keep predicate for `drop_pending_of` / `drop_challenges_of`: the record's `agent` field differs
    from the removed agent (works for any struct with an `agent : AgentId` field). -/
abbrev keepAgentP {V : Type} (proj : V → types.AgentId) (agent : types.AgentId) :
    types.InvocationId × V → Bool := fun p => decide (proj p.2 ≠ agent)

/-! ## `drop_pending_of` -/

theorem dropPendingLoop_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.pending.entries.val.map Prod.fst).Nodup)
    (kept : collections.VecMap types.InvocationId types.PendingInvocation) (i0 : Usize)
    (hi0 : i0.val ≤ self.pending.entries.val.length)
    (hkept0 : kept.entries.val =
      (self.pending.entries.val.take i0.val).filter (keepAgentP (·.agent) agent)) :
    state.KernelState.drop_pending_of_loop self agent kept i0 ⦃ out =>
      ∃ kept1, out = (self.agent_active, self.agent_parent, self.agent_cap, self.taint_levels,
        self.integ_levels, self.challenges, self.consumed_ids, self.consumed_attestations,
        self.consumed_crossings, self.crossing_grants, self.tool_registered, kept1) ∧
        kept1.entries.val = self.pending.entries.val.filter (keepAgentP (·.agent) agent) ⦄ := by
  unfold state.KernelState.drop_pending_of_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.pending.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.pending.entries.val.length ∧
      p.1.entries.val = (self.pending.entries.val.take p.2.val).filter (keepAgentP (·.agent) agent))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [state.KernelState.drop_pending_of_loop.body, collections.VecMap.len,
      alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < self.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone self.pending i hlt)
      rw [hkEq]; simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec self.pending k)
      have hlast : vmLastEntry self.pending.entries.val k =
          some ((self.pending.entries.val[i.val]'hlt).1, (self.pending.entries.val[i.val]'hlt).2) := by
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
        have hni := fst_getElem_not_mem_map_take self.pending.entries.val i.val hlt hnd
        rw [hkept]
        intro p hp hpc
        have hmem : p.1 ∈ (self.pending.entries.val.take i.val).map Prod.fst :=
          List.mem_map.mpr ⟨p, List.mem_of_mem_filter hp, rfl⟩
        rw [hpc, hk] at hmem
        exact hni hmem
      have hget : self.pending.entries.val[i.val]? =
          some ((self.pending.entries.val[i.val]'hlt).1, (self.pending.entries.val[i.val]'hlt).2) := by
        rw [List.getElem?_eq_getElem hlt]
      simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        agentId_eq_spec, bind_tc_ok]
      split
      · rename_i hb
        have hag : (self.pending.entries.val[i.val]'hlt).2.agent ≠ agent := by simpa using hb
        obtain ⟨kept1, hkept1Eq, hkept1⟩ := spec_imp_exists
          (vecMapInsert_append_spec types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
            types.PendingInvocation.Insts.CoreCloneClone kept k
            (self.pending.entries.val[i.val]'hlt).2 hcapk hfresh)
        rw [hkept1Eq]; simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget, Option.toList_some,
          List.filter_append, ← hkept, hkept1, hk]
        simp [keepAgentP, hag]
      · rename_i hb
        have hag : (self.pending.entries.val[i.val]'hlt).2.agent = agent := by simpa using hb
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget, Option.toList_some,
          List.filter_append, hkept]
        simp [keepAgentP, hag]
    case isFalse h =>
      have heq' : i.val = self.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hkept ⊢
      exact ⟨kept, rfl, hkept⟩
  · exact ⟨hi0, by simpa using hkept0⟩

theorem dropPendingOf_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.pending.entries.val.map Prod.fst).Nodup) :
    state.KernelState.drop_pending_of self agent ⦃ st' =>
      st'.agent_active = self.agent_active ∧ st'.agent_parent = self.agent_parent ∧
      st'.agent_cap = self.agent_cap ∧ st'.taint_levels = self.taint_levels ∧
      st'.integ_levels = self.integ_levels ∧ st'.challenges = self.challenges ∧
      st'.consumed_ids = self.consumed_ids ∧
      st'.consumed_attestations = self.consumed_attestations ∧
      st'.consumed_crossings = self.consumed_crossings ∧
      st'.crossing_grants = self.crossing_grants ∧ st'.tool_registered = self.tool_registered ∧
      st'.pending.entries.val = self.pending.entries.val.filter (keepAgentP (·.agent) agent) ⦄ := by
  unfold state.KernelState.drop_pending_of
  simp only [collections.VecMap.new, bind_tc_ok]
  obtain ⟨out, houtEq, kept1, houtVal, hkeptVal⟩ := spec_imp_exists
    (dropPendingLoop_spec self agent hnd { entries := alloc.vec.Vec.new _ } 0#usize (by scalar_tac)
      (by simp [alloc.vec.Vec.new, List.take_zero]))
  rw [houtEq]; simp only [bind_tc_ok, houtVal, spec_ok]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact hkeptVal

/-! ## `drop_challenges_of` (same shape as pending, on the challenge map) -/

theorem dropChallengesLoop_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.challenges.entries.val.map Prod.fst).Nodup)
    (kept : collections.VecMap types.InvocationId types.ChallengeScope) (i0 : Usize)
    (hi0 : i0.val ≤ self.challenges.entries.val.length)
    (hkept0 : kept.entries.val =
      (self.challenges.entries.val.take i0.val).filter (keepAgentP (·.agent) agent)) :
    state.KernelState.drop_challenges_of_loop self agent kept i0 ⦃ out =>
      ∃ kept1, out = (self.agent_active, self.agent_parent, self.agent_cap, self.taint_levels,
        self.integ_levels, self.pending, self.consumed_ids, self.consumed_attestations,
        self.consumed_crossings, self.crossing_grants, self.tool_registered, kept1) ∧
        kept1.entries.val = self.challenges.entries.val.filter (keepAgentP (·.agent) agent) ⦄ := by
  unfold state.KernelState.drop_challenges_of_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.challenges.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.challenges.entries.val.length ∧
      p.1.entries.val = (self.challenges.entries.val.take p.2.val).filter (keepAgentP (·.agent) agent))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [state.KernelState.drop_challenges_of_loop.body, collections.VecMap.len,
      alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < self.challenges.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.ChallengeScope.Insts.CoreCloneClone self.challenges i hlt)
      rw [hkEq]; simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ChallengeScope.Insts.CoreCloneClone challengeScope_clone_spec self.challenges k)
      have hlast : vmLastEntry self.challenges.entries.val k =
          some ((self.challenges.entries.val[i.val]'hlt).1,
            (self.challenges.entries.val[i.val]'hlt).2) := by
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
        have hni := fst_getElem_not_mem_map_take self.challenges.entries.val i.val hlt hnd
        rw [hkept]
        intro p hp hpc
        have hmem : p.1 ∈ (self.challenges.entries.val.take i.val).map Prod.fst :=
          List.mem_map.mpr ⟨p, List.mem_of_mem_filter hp, rfl⟩
        rw [hpc, hk] at hmem
        exact hni hmem
      have hget : self.challenges.entries.val[i.val]? =
          some ((self.challenges.entries.val[i.val]'hlt).1,
            (self.challenges.entries.val[i.val]'hlt).2) := by
        rw [List.getElem?_eq_getElem hlt]
      simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        agentId_eq_spec, bind_tc_ok]
      split
      · rename_i hb
        have hag : (self.challenges.entries.val[i.val]'hlt).2.agent ≠ agent := by simpa using hb
        obtain ⟨kept1, hkept1Eq, hkept1⟩ := spec_imp_exists
          (vecMapInsert_append_spec types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
            types.ChallengeScope.Insts.CoreCloneClone kept k
            (self.challenges.entries.val[i.val]'hlt).2 hcapk hfresh)
        rw [hkept1Eq]; simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget, Option.toList_some,
          List.filter_append, ← hkept, hkept1, hk]
        simp [keepAgentP, hag]
      · rename_i hb
        have hag : (self.challenges.entries.val[i.val]'hlt).2.agent = agent := by simpa using hb
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget, Option.toList_some,
          List.filter_append, hkept]
        simp [keepAgentP, hag]
    case isFalse h =>
      have heq' : i.val = self.challenges.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hkept ⊢
      exact ⟨kept, rfl, hkept⟩
  · exact ⟨hi0, by simpa using hkept0⟩

theorem dropChallengesOf_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.challenges.entries.val.map Prod.fst).Nodup) :
    state.KernelState.drop_challenges_of self agent ⦃ st' =>
      st'.agent_active = self.agent_active ∧ st'.agent_parent = self.agent_parent ∧
      st'.agent_cap = self.agent_cap ∧ st'.taint_levels = self.taint_levels ∧
      st'.integ_levels = self.integ_levels ∧ st'.pending = self.pending ∧
      st'.consumed_ids = self.consumed_ids ∧
      st'.consumed_attestations = self.consumed_attestations ∧
      st'.consumed_crossings = self.consumed_crossings ∧
      st'.crossing_grants = self.crossing_grants ∧ st'.tool_registered = self.tool_registered ∧
      st'.challenges.entries.val = self.challenges.entries.val.filter (keepAgentP (·.agent) agent) ⦄ := by
  unfold state.KernelState.drop_challenges_of
  simp only [collections.VecMap.new, bind_tc_ok]
  obtain ⟨out, houtEq, kept1, houtVal, hkeptVal⟩ := spec_imp_exists
    (dropChallengesLoop_spec self agent hnd { entries := alloc.vec.Vec.new _ } 0#usize
      (by scalar_tac) (by simp [alloc.vec.Vec.new, List.take_zero]))
  rw [houtEq]; simp only [bind_tc_ok, houtVal, spec_ok]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact hkeptVal

/-! ## `drop_grants_of` (filters on the key's `agent`) -/

/-- Keep predicate for `drop_grants_of`: the crossing KEY's `agent` differs from the removed one. -/
abbrev keepGrantP (agent : types.AgentId) : types.CrossingKey × types.CrossingGrant → Bool :=
  fun p => decide (p.1.agent ≠ agent)

theorem dropGrantsLoop_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.crossing_grants.entries.val.map Prod.fst).Nodup)
    (kept : collections.VecMap types.CrossingKey types.CrossingGrant) (i0 : Usize)
    (hi0 : i0.val ≤ self.crossing_grants.entries.val.length)
    (hkept0 : kept.entries.val =
      (self.crossing_grants.entries.val.take i0.val).filter (keepGrantP agent)) :
    state.KernelState.drop_grants_of_loop self agent kept i0 ⦃ out =>
      ∃ kept1, out = (self.agent_active, self.agent_parent, self.agent_cap, self.taint_levels,
        self.integ_levels, self.pending, self.challenges, self.consumed_ids,
        self.consumed_attestations, self.consumed_crossings, self.tool_registered, kept1) ∧
        kept1.entries.val = self.crossing_grants.entries.val.filter (keepGrantP agent) ⦄ := by
  unfold state.KernelState.drop_grants_of_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.crossing_grants.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.crossing_grants.entries.val.length ∧
      p.1.entries.val = (self.crossing_grants.entries.val.take p.2.val).filter (keepGrantP agent))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [state.KernelState.drop_grants_of_loop.body, collections.VecMap.len,
      alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < self.crossing_grants.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.CrossingKey.Insts.CoreCloneClone
          types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey
          types.CrossingGrant.Insts.CoreCloneClone self.crossing_grants i hlt)
      rw [hkEq]; simp only [crossingKey_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.CrossingKey.Insts.CoreCloneClone
          types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
          types.CrossingGrant.Insts.CoreCloneClone crossingGrant_clone_spec self.crossing_grants k)
      have hlast : vmLastEntry self.crossing_grants.entries.val k =
          some ((self.crossing_grants.entries.val[i.val]'hlt).1,
            (self.crossing_grants.entries.val[i.val]'hlt).2) := by
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
        have hni := fst_getElem_not_mem_map_take self.crossing_grants.entries.val i.val hlt hnd
        rw [hkept]
        intro p hp hpc
        have hmem : p.1 ∈ (self.crossing_grants.entries.val.take i.val).map Prod.fst :=
          List.mem_map.mpr ⟨p, List.mem_of_mem_filter hp, rfl⟩
        rw [hpc, hk] at hmem
        exact hni hmem
      have hget : self.crossing_grants.entries.val[i.val]? =
          some ((self.crossing_grants.entries.val[i.val]'hlt).1,
            (self.crossing_grants.entries.val[i.val]'hlt).2) := by
        rw [List.getElem?_eq_getElem hlt]
      simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
        agentId_eq_spec, bind_tc_ok]
      split
      · rename_i hb
        have hag : (self.crossing_grants.entries.val[i.val]'hlt).1.agent ≠ agent := by
          rw [hk] at hb; simpa using hb
        obtain ⟨kept1, hkept1Eq, hkept1⟩ := spec_imp_exists
          (vecMapInsert_append_spec types.CrossingKey.Insts.CoreCloneClone
            types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
            types.CrossingGrant.Insts.CoreCloneClone kept k
            (self.crossing_grants.entries.val[i.val]'hlt).2 hcapk hfresh)
        rw [hkept1Eq]; simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget, Option.toList_some,
          List.filter_append, ← hkept, hkept1, hk]
        simp [keepGrantP, hag]
      · rename_i hb
        have hag : (self.crossing_grants.entries.val[i.val]'hlt).1.agent = agent := by
          rw [hk] at hb; simpa using hb
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget, Option.toList_some,
          List.filter_append, hkept]
        simp [keepGrantP, hag]
    case isFalse h =>
      have heq' : i.val = self.crossing_grants.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hkept ⊢
      exact ⟨kept, rfl, hkept⟩
  · exact ⟨hi0, by simpa using hkept0⟩

theorem dropGrantsOf_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.crossing_grants.entries.val.map Prod.fst).Nodup) :
    state.KernelState.drop_grants_of self agent ⦃ st' =>
      st'.agent_active = self.agent_active ∧ st'.agent_parent = self.agent_parent ∧
      st'.agent_cap = self.agent_cap ∧ st'.taint_levels = self.taint_levels ∧
      st'.integ_levels = self.integ_levels ∧ st'.pending = self.pending ∧
      st'.challenges = self.challenges ∧ st'.consumed_ids = self.consumed_ids ∧
      st'.consumed_attestations = self.consumed_attestations ∧
      st'.consumed_crossings = self.consumed_crossings ∧
      st'.tool_registered = self.tool_registered ∧
      st'.crossing_grants.entries.val =
        self.crossing_grants.entries.val.filter (keepGrantP agent) ⦄ := by
  unfold state.KernelState.drop_grants_of
  simp only [collections.VecMap.new, bind_tc_ok]
  obtain ⟨out, houtEq, kept1, houtVal, hkeptVal⟩ := spec_imp_exists
    (dropGrantsLoop_spec self agent hnd { entries := alloc.vec.Vec.new _ } 0#usize
      (by scalar_tac) (by simp [alloc.vec.Vec.new, List.take_zero]))
  rw [houtEq]; simp only [bind_tc_ok, houtVal, spec_ok]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact hkeptVal

/-! ## `clear_agent` (5 key-removes + the 3 drops, composed) -/

theorem clearAgent_spec (self : state.KernelState) (agent : types.AgentId)
    (hndPending : (self.pending.entries.val.map Prod.fst).Nodup)
    (hndChallenges : (self.challenges.entries.val.map Prod.fst).Nodup)
    (hndGrants : (self.crossing_grants.entries.val.map Prod.fst).Nodup) :
    transitions.clear_agent self agent ⦃ st' =>
      (∀ y, vsMem st'.agent_active y ↔ vsMem self.agent_active y ∧ y ≠ agent) ∧
      st'.agent_parent.entries.val = self.agent_parent.entries.val.filter (removeKept agent) ∧
      st'.agent_cap.entries.val = self.agent_cap.entries.val.filter (removeKept agent) ∧
      st'.taint_levels.entries.val = self.taint_levels.entries.val.filter (removeKept agent) ∧
      st'.integ_levels.entries.val = self.integ_levels.entries.val.filter (removeKept agent) ∧
      st'.pending.entries.val = self.pending.entries.val.filter (keepAgentP (·.agent) agent) ∧
      st'.challenges.entries.val = self.challenges.entries.val.filter (keepAgentP (·.agent) agent) ∧
      st'.crossing_grants.entries.val = self.crossing_grants.entries.val.filter (keepGrantP agent) ∧
      st'.consumed_ids = self.consumed_ids ∧
      st'.consumed_attestations = self.consumed_attestations ∧
      st'.consumed_crossings = self.consumed_crossings ∧
      st'.tool_registered = self.tool_registered ⦄ := by
  unfold transitions.clear_agent
  obtain ⟨vs, hvsEq, hvs⟩ := spec_imp_exists
    (vecSetRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec agentId_clone_spec
      self.agent_active agent)
  rw [hvsEq]; simp only [bind_tc_ok]
  obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
    (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      types.AgentId.Insts.CoreCloneClone self.agent_parent agent)
  rw [hvmEq]; simp only [bind_tc_ok]
  obtain ⟨vm1, hvm1Eq, hvm1⟩ := spec_imp_exists
    (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      self.agent_cap agent)
  rw [hvm1Eq]; simp only [bind_tc_ok]
  obtain ⟨vm2, hvm2Eq, hvm2⟩ := spec_imp_exists
    (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      (collections.VecSet.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCloneClone)
      self.taint_levels agent)
  rw [hvm2Eq]; simp only [bind_tc_ok]
  obtain ⟨vm3, hvm3Eq, hvm3⟩ := spec_imp_exists
    (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      (collections.VecSet.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCloneClone)
      self.integ_levels agent)
  rw [hvm3Eq]; simp only [bind_tc_ok]
  -- drop_pending_of on the 5-field-modified state (its pending = self.pending)
  set s0 : state.KernelState := { self with agent_active := vs, agent_parent := vm, agent_cap := vm1, taint_levels := vm2, integ_levels := vm3 } with hs0def
  obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1ch, hs1ci, hs1ca, hs1cc, hs1g, hs1tr,
      hs1pend⟩ := spec_imp_exists (dropPendingOf_spec s0 agent hndPending)
  rw [hs1Eq]; simp only [bind_tc_ok]
  -- drop_challenges_of on s1 (s1.challenges = self.challenges)
  obtain ⟨s2, hs2Eq, hs2a, hs2p, hs2c, hs2t, hs2i, hs2pend, hs2ci, hs2ca, hs2cc, hs2g, hs2tr,
      hs2ch⟩ := spec_imp_exists (dropChallengesOf_spec s1 agent (by rw [hs1ch]; exact hndChallenges))
  rw [hs2Eq]; simp only [bind_tc_ok]
  -- drop_grants_of on s2 (s2.crossing_grants = s1.crossing_grants = self.crossing_grants)
  obtain ⟨s3, hs3Eq, hs3a, hs3p, hs3c, hs3t, hs3i, hs3pend, hs3ch, hs3ci, hs3ca, hs3cc, hs3tr,
      hs3g⟩ := spec_imp_exists
    (dropGrantsOf_spec s2 agent (by rw [hs2g, hs1g]; exact hndGrants))
  rw [hs3Eq]; simp only [spec_ok]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- agent_active
    rw [hs3a, hs2a, hs1a]; exact hvs
  · -- agent_parent
    rw [hs3p, hs2p, hs1p]; exact hvm
  · -- agent_cap
    rw [hs3c, hs2c, hs1c]; exact hvm1
  · -- taint_levels
    rw [hs3t, hs2t, hs1t]; exact hvm2
  · -- integ_levels
    rw [hs3i, hs2i, hs1i]; exact hvm3
  · -- pending
    rw [hs3pend, hs2pend]; exact hs1pend
  · -- challenges
    rw [hs3ch, hs2ch, hs1ch]
  · -- crossing_grants
    rw [hs3g, hs2g, hs1g]
  · -- consumed_ids
    rw [hs3ci, hs2ci, hs1ci]
  · -- consumed_attestations
    rw [hs3ca, hs2ca, hs1ca]
  · -- consumed_crossings
    rw [hs3cc, hs2cc, hs1cc]
  · -- tool_registered
    rw [hs3tr, hs2tr, hs1tr]

end ArgusLean.Refinement
