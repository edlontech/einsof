import ArgusLean.Refinement.Unified.Relation

/-! # Layer 2 — V4 init refinement

The extracted initial `KernelState` relates under the unified V4 relation `R` to a
`Tzimtzum.initial` state. The concrete constructor hard-codes `AgentId.root`; the deployed
background separately carries the governed root identifier, so the theorem states their equality
explicitly. `CapacityOK` supplies that initialization-coherence premise in `Soundness.lean`.
-/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- `CapKind.ALL` enumerates every capability. -/
theorem capKindAll_complete (C : capability.CapKind) : C ∈ capability.CapKind.ALL.val := by
  cases C <;> simp [capability.CapKind.ALL, Array.make]

/-- `CapKind.ALL` lists each capability once. -/
theorem capKindAll_nodup : capability.CapKind.ALL.val.Nodup := by
  simp only [capability.CapKind.ALL, Array.make]
  decide

/-- The extracted capability-build loop contains exactly the processed prefix. -/
theorem initialCaps_loop_spec (all_caps : collections.VecSet capability.CapKind) (i0 : Usize)
    (hi0 : i0.val ≤ capability.CapKind.ALL.val.length)
    (hacc : all_caps.items.val = capability.CapKind.ALL.val.take i0.val) :
    state.KernelState.initial_loop all_caps i0 ⦃ vs => ∀ C : capability.CapKind, C ∈ vs.items.val ⦄ := by
  unfold state.KernelState.initial_loop
  apply loop.spec_decr_nat
    (measure := fun p => capability.CapKind.ALL.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ capability.CapKind.ALL.val.length ∧
        p.1.items.val = capability.CapKind.ALL.val.take p.2.val)
  · rintro ⟨ac, i⟩ ⟨hile, hacc'⟩
    simp only [state.KernelState.initial_loop.body]
    dsimp only at hile hacc' ⊢
    step*
    · have hilt : i.val < capability.CapKind.ALL.val.length := by
        have h := ‹i < s.len›
        simp only [s_post, Slice.len, Array.to_slice] at h
        scalar_tac
      have hck_notin : ck ∉ ac.items.val := by
        rw [hacc', ck_post]
        exact getElem_not_mem_take capKindAll_nodup hilt
      obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
        (vecSetContains_spec capability.CapKind.Insts.CoreCloneClone
          capability.CapKind.Insts.CoreCmpPartialEqCapKind capKind_eq_spec ac ck)
      have hbfalse : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd (hbIff.mp rfl) hck_notin
      have hcap : ac.items.val.length < Usize.max := by
        rw [hacc', List.length_take]
        scalar_tac
      unfold collections.VecSet.insert
      rw [hbEq]
      simp only [hbfalse, Bool.false_eq_true, if_false, bind_tc_ok]
      obtain ⟨v, hvEq, hvval⟩ := spec_imp_exists (alloc.vec.Vec.push_spec ac.items ck hcap)
      rw [hvEq]
      simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      show v.val = capability.CapKind.ALL.val.take _
      rw [hvval, hacc', ck_post, i2_post,
        List.take_add_one, List.getElem?_eq_getElem hilt, Option.toList_some]
    · rename_i hlt
      have hlen : i.val = capability.CapKind.ALL.val.length := by
        simp only [s_post, Slice.len, Array.to_slice] at hlt
        scalar_tac
      intro C
      rw [hacc', hlen, List.take_length]
      exact capKindAll_complete C
  · exact ⟨hi0, hacc⟩

/-- The complete extracted capability build contains every `CapKind`. -/
theorem initialCaps_spec :
    state.KernelState.initial_loop
      { items := alloc.vec.Vec.new capability.CapKind } 0#usize ⦃ vs =>
      ∀ C : capability.CapKind, C ∈ vs.items.val ⦄ :=
  initialCaps_loop_spec _ 0#usize (by simp) (by simp)

/-- Field characterization of the extracted V4 initial state. -/
theorem init_chars (bg : background.BackgroundTheory)
    (hroot : types.AgentId.root = .ok bg.root_agent)
    (c0 : state.KernelState) (hc0 : state.KernelState.initial = .ok c0) :
    (∀ y, vsMem c0.agent_active y ↔ y = bg.root_agent) ∧
    (∀ N C, vmsMemLast c0.agent_cap N C ↔ N = bg.root_agent) ∧
    vmNodupKeys c0.agent_cap ∧
    c0.agent_parent.entries.val = [] ∧
    c0.taint_levels.entries.val = [] ∧
    c0.integ_levels.entries.val = [] ∧
    c0.pending.entries.val = [] ∧
    c0.challenges.entries.val = [] ∧
    c0.consumed_ids.items.val = [] ∧
    c0.consumed_attestations.items.val = [] ∧
    c0.consumed_crossings.items.val = [] ∧
    c0.crossing_grants.entries.val = [] ∧
    c0.tool_registered.items.val = [] := by
  simp only [state.KernelState.initial, collections.VecSet.new, collections.VecMap.new,
    bind_tc_ok] at hc0
  rw [hroot] at hc0
  simp only [bind_tc_ok] at hc0
  obtain ⟨acs, hacsEq, hacsMem⟩ := spec_imp_exists initialCaps_spec
  rw [hacsEq] at hc0
  simp only [agentId_clone_spec, bind_tc_ok] at hc0
  obtain ⟨aa, haaEq, haaMem⟩ := spec_imp_exists
    (vecSetInsert_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      { items := alloc.vec.Vec.new types.AgentId } bg.root_agent (by simp; scalar_tac))
  rw [haaEq] at hc0
  simp only [bind_tc_ok] at hc0
  obtain ⟨acap, hacapEq, hacapLast⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      { entries := alloc.vec.Vec.new (types.AgentId × collections.VecSet capability.CapKind) }
      bg.root_agent acs (by simp; scalar_tac))
  obtain ⟨acapN, hacapNEq, hacapNd⟩ := spec_imp_exists
    (vecMapInsert_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      { entries := alloc.vec.Vec.new (types.AgentId × collections.VecSet capability.CapKind) }
      bg.root_agent acs (by simp; scalar_tac))
  have hsame : acapN = acap := Result.ok.inj (hacapNEq.symm.trans hacapEq)
  rw [hacapEq] at hc0
  simp only [bind_tc_ok, Result.ok.injEq] at hc0
  subst c0
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro y
    rw [haaMem y]
    simp [vsMem]
  · intro N C
    unfold vmsMemLast
    rw [hacapLast N]
    by_cases hN : N = bg.root_agent
    · simp [hN, hacsMem C]
    · simp [hN, vmLastEntry]
  · rw [← hsame]
    exact hacapNd (by simp [vmNodupKeys])

/-- The abstract V4 initial state, with immutable root/mode/ceiling fields read from `bg`. -/
noncomputable def absInitial (bg : background.BackgroundTheory) : AbsState where
  agent_active := fun A => A = bg.root_agent
  agent_parent := fun _ _ => False
  agent_cap := fun A _ => A = bg.root_agent
  taint_levels := fun _ _ => False
  integ_levels := fun _ _ => False
  pending := fun _ => none
  challenges := fun _ => none
  consumed_ids := fun _ => False
  consumed_attestations := fun _ => False
  consumed_crossings := fun _ => False
  crossing_grants := fun _ _ => none
  tool_registered := fun _ => False
  egress_allow_ceiling := fun E => (ceilC bg.allow_ceiling E).map confA
  egress_inspect_ceiling := fun E => (ceilC bg.inspect_ceiling E).map confA
  mode := modeA bg.mode
  root_agent := bg.root_agent

/-- The extracted initial state refines `Tzimtzum.initial` under explicit root coherence. -/
theorem init_refines (bg : background.BackgroundTheory)
    (hroot : types.AgentId.root = .ok bg.root_agent)
    (c0 : state.KernelState) (hc0 : state.KernelState.initial = .ok c0) :
    ∃ a0 : AbsState, Tzimtzum.initial a0 ∧ R c0 bg a0 := by
  obtain ⟨hactive, hcap, hcapNd, hpar, htaint, hinteg, hpend, hchal, hids, hatt, hcross,
    hgrant, htool⟩ := init_chars bg hroot c0 hc0
  refine ⟨absInitial bg, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [absInitial]
  · refine
      { root := rfl
        mode := rfl
        active := ?_
        tool_reg := ?_
        parent := ?_
        cap := ?_
        taint := ?_
        integ := ?_
        pending := ?_
        challenges := ?_
        grants := ?_
        consumedIds := ?_
        consumedAtt := ?_
        consumedCross := ?_
        flowAllows := ?_
        flowInspects := ?_
        ndParent := ?_
        ndCap := hcapNd
        ndTaint := ?_
        ndInteg := ?_
        ndPending := ?_
        ndChallenges := ?_
        ndGrants := ?_ }
    · intro x
      exact (hactive x).symm
    · intro t
      simp [absInitial, vsMem, htool]
    · intro C P
      simp [absInitial, hpar, vmLastEntry]
    · intro N C
      exact (hcap N C).symm
    · intro ag L
      simp [absInitial, vmsMemLast, htaint, vmLastEntry]
    · intro ag L
      simp [absInitial, vmsMemLast, hinteg, vmLastEntry]
    · intro I
      simp [absInitial, pendingC, hpend, vmLastEntry, optRel]
    · intro I
      simp [absInitial, challengeC, hchal, vmLastEntry, optRel]
    · intro A D
      simp [absInitial, crossingGrantC, hgrant, vmLastEntry, optRel]
    · intro I
      simp [absInitial, vsMem, hids]
    · intro Att
      simp [absInitial, vsMem, hatt]
    · intro X
      simp [absInitial, vsMem, hcross]
    · intro L E
      show Tzimtzum.ceilingAdmits _ L E ↔ _
      simp only [absInitial]
      exact ceilingAdmits_mapA_iff bg.allow_ceiling L E
    · intro L E
      show Tzimtzum.ceilingAdmits _ L E ↔ _
      simp only [absInitial]
      exact ceilingAdmits_mapA_iff bg.inspect_ceiling L E
    · simp [vmNodupKeys, hpar]
    · simp [vmNodupKeys, htaint]
    · simp [vmNodupKeys, hinteg]
    · simp [vmNodupKeys, hpend]
    · simp [vmNodupKeys, hchal]
    · simp [vmNodupKeys, hgrant]

end ArgusLean.Refinement
