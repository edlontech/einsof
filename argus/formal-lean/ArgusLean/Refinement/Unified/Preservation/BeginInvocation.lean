import ArgusLean.Refinement.Unified.Preservation.Ingest

/-! # Layer 1 — `begin_invocation` preserves the unified `R` (V4)

The V4 admission gate re-evaluates capability, clearance, confidentiality flow, and integrity over
held labels plus every pending output. This module gives each extracted fold a membership-level
specification, bridges the resulting nine checks to the abstract predicates, and transports the
three successful concrete branches through `R`.
-/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

-- The extracted gate contains several nested linear scans. These bounds keep elaboration stable.
/- The extracted gate contains nested vector scans followed by a seven-boolean dispatch. Keeping the
   atom, loop, and post-state proofs staged avoids the simplifier saturation seen when that tree is
   unfolded as one term; the remaining branch normalization still needs a larger elaboration budget. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-! ## Speculative labels -/

/-- Concrete speculative confidentiality membership. -/
def speculativeTaintC (s : state.KernelState) (agent : types.AgentId)
    (l : types.ConfLevel) : Prop :=
  vmsMemLast s.taint_levels agent l ∨
    ∃ p ∈ s.pending.entries.val, p.2.agent = agent ∧ p.2.policy.output_conf = l

/-- Concrete speculative integrity membership. -/
def speculativeIntegC (s : state.KernelState) (agent : types.AgentId)
    (l : types.IntegLevel) : Prop :=
  vmsMemLast s.integ_levels agent l ∨
    ∃ p ∈ s.pending.entries.val, p.2.agent = agent ∧ p.2.policy.output_integ = l

theorem speculativeTaintLoop_spec (s : state.KernelState) (agent : types.AgentId)
    (hnd : vmNodupKeys s.pending) (base : collections.VecSet types.ConfLevel)
    (hbase : ∀ l, vsMem base l ↔ vmsMemLast s.taint_levels agent l)
    (hcap : base.items.val.length + s.pending.entries.val.length ≤ Usize.max)
    (acc : collections.VecSet types.ConfLevel) (i0 : Usize)
    (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hlen : acc.items.val.length ≤ base.items.val.length + i0.val)
    (hmem : ∀ l, vsMem acc l ↔ vsMem base l ∨
      ∃ p ∈ s.pending.entries.val.take i0.val,
        p.2.agent = agent ∧ p.2.policy.output_conf = l) :
    state.KernelState.speculative_taint_loop s.pending agent acc i0 ⦃ out =>
      (∀ l, vsMem out l ↔ speculativeTaintC s agent l) ∧
      out.items.val.length ≤ base.items.val.length + s.pending.entries.val.length ⦄ := by
  unfold state.KernelState.speculative_taint_loop
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ s.pending.entries.val.length ∧
      p.1.items.val.length ≤ base.items.val.length + p.2.val ∧
      ∀ l, vsMem p.1 l ↔ vsMem base l ∨
        ∃ q ∈ s.pending.entries.val.take p.2.val,
          q.2.agent = agent ∧ q.2.policy.output_conf = l)
  · rintro ⟨cur, i⟩ ⟨hile, hlenL, hmemL⟩
    simp only [state.KernelState.speculative_taint_loop.body, collections.VecMap.len,
      alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]
      simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]
        exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, bind_tc_ok]
      set q := s.pending.entries.val[i.val]'hlt with hq
      have hget : s.pending.entries.val[i.val]? = some q := by
        rw [List.getElem?_eq_getElem hlt, hq]
      have htake : ∀ l,
          (∃ p ∈ s.pending.entries.val.take (i.val + 1),
              p.2.agent = agent ∧ p.2.policy.output_conf = l) ↔
            (∃ p ∈ s.pending.entries.val.take i.val,
              p.2.agent = agent ∧ p.2.policy.output_conf = l) ∨
              (q.2.agent = agent ∧ q.2.policy.output_conf = l) := by
        intro l
        rw [List.take_add_one, hget]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨p, hp | rfl, hp1, hp2⟩
          · exact Or.inl ⟨p, hp, hp1, hp2⟩
          · exact Or.inr ⟨hp1, hp2⟩
        · rintro (⟨p, hp, hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · exact ⟨p, Or.inl hp, hp1, hp2⟩
          · exact ⟨q, Or.inr rfl, hp1, hp2⟩
      have hlenL' : cur.items.val.length ≤ base.items.val.length + i.val := by
        simpa using hlenL
      have hmemL' : ∀ l, vsMem cur l ↔ vsMem base l ∨
          ∃ p ∈ s.pending.entries.val.take i.val,
            p.2.agent = agent ∧ p.2.policy.output_conf = l := by
        simpa using hmemL
      split
      case isTrue hb =>
        have hag0 : (s.pending.entries.val[i.val]'hlt).2.agent = agent := by simpa using hb
        have hag : q.2.agent = agent := by simpa [q] using hag0
        have hcapCur : cur.items.val.length < Usize.max := by
          have := hcap
          have := hlenL
          scalar_tac
        obtain ⟨cur', hcurEq, hcurMem, hcurLen⟩ := spec_imp_exists
          (vecSetInsertLen_spec types.ConfLevel.Insts.CoreCloneClone
            types.ConfLevel.Insts.CoreCmpPartialEqConfLevel confLevel_eq_spec cur
            q.2.policy.output_conf hcapCur)
        rw [hcurEq]
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · calc
            cur'.items.val.length ≤ cur.items.val.length + 1 := hcurLen
            _ ≤ (base.items.val.length + i.val) + 1 := Nat.add_le_add_right hlenL' 1
            _ = base.items.val.length + i2.val := by omega
        · intro l
          rw [show i2.val = i.val + 1 from by scalar_tac, htake l, hcurMem l, hmemL' l]
          simp [hag, eq_comm, or_assoc]
      case isFalse hb =>
        have hag0 : ¬(s.pending.entries.val[i.val]'hlt).2.agent = agent := by simpa using hb
        have hag : ¬q.2.agent = agent := by simpa [q] using hag0
        step*
        refine ⟨by scalar_tac, by omega, ?_, by scalar_tac⟩
        intro l
        rw [show i2.val = i.val + 1 from by scalar_tac, htake l, hmemL' l]
        simp [hag]
    case isFalse h =>
      have hi : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hmemL ⊢
      refine ⟨?_, by rwa [hi] at hlenL⟩
      intro l
      rw [hmemL l, hbase l]
      rfl
  · exact ⟨hi0, hlen, hmem⟩

theorem speculativeTaint_spec (s : state.KernelState) (agent : types.AgentId)
    (hnd : vmNodupKeys s.pending)
    (hcap : vmSetLen s.taint_levels agent + s.pending.entries.val.length ≤ Usize.max) :
    state.KernelState.speculative_taint s agent ⦃ out =>
      ∀ l, vsMem out l ↔ speculativeTaintC s agent l ⦄ := by
  unfold state.KernelState.speculative_taint
  obtain ⟨base, hbaseEq, hbaseMem, hbaseLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec s.taint_levels agent)
  rw [hbaseEq]
  simp only [bind_tc_ok]
  obtain ⟨out, houtEq, houtMem, _⟩ := spec_imp_exists
    (speculativeTaintLoop_spec s agent hnd base hbaseMem
      (by rw [hbaseLen]; exact hcap) base 0#usize (by simp) (by simp) (by simp))
  rw [houtEq]
  exact houtMem


theorem speculativeIntegLoop_spec (s : state.KernelState) (agent : types.AgentId)
    (hnd : vmNodupKeys s.pending) (base : collections.VecSet types.IntegLevel)
    (hbase : ∀ l, vsMem base l ↔ vmsMemLast s.integ_levels agent l)
    (hcap : base.items.val.length + s.pending.entries.val.length ≤ Usize.max)
    (acc : collections.VecSet types.IntegLevel) (i0 : Usize)
    (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hlen : acc.items.val.length ≤ base.items.val.length + i0.val)
    (hmem : ∀ l, vsMem acc l ↔ vsMem base l ∨
      ∃ p ∈ s.pending.entries.val.take i0.val,
        p.2.agent = agent ∧ p.2.policy.output_integ = l) :
    state.KernelState.speculative_integ_loop s.pending agent acc i0 ⦃ out =>
      (∀ l, vsMem out l ↔ speculativeIntegC s agent l) ∧
      out.items.val.length ≤ base.items.val.length + s.pending.entries.val.length ⦄ := by
  unfold state.KernelState.speculative_integ_loop
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ s.pending.entries.val.length ∧
      p.1.items.val.length ≤ base.items.val.length + p.2.val ∧
      ∀ l, vsMem p.1 l ↔ vsMem base l ∨
        ∃ q ∈ s.pending.entries.val.take p.2.val,
          q.2.agent = agent ∧ q.2.policy.output_integ = l)
  · rintro ⟨cur, i⟩ ⟨hile, hlenL, hmemL⟩
    simp only [state.KernelState.speculative_integ_loop.body, collections.VecMap.len,
      alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]
      simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]
        exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, bind_tc_ok]
      set q := s.pending.entries.val[i.val]'hlt with hq
      have hget : s.pending.entries.val[i.val]? = some q := by
        rw [List.getElem?_eq_getElem hlt, hq]
      have htake : ∀ l,
          (∃ p ∈ s.pending.entries.val.take (i.val + 1),
              p.2.agent = agent ∧ p.2.policy.output_integ = l) ↔
            (∃ p ∈ s.pending.entries.val.take i.val,
              p.2.agent = agent ∧ p.2.policy.output_integ = l) ∨
              (q.2.agent = agent ∧ q.2.policy.output_integ = l) := by
        intro l
        rw [List.take_add_one, hget]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨p, hp | rfl, hp1, hp2⟩
          · exact Or.inl ⟨p, hp, hp1, hp2⟩
          · exact Or.inr ⟨hp1, hp2⟩
        · rintro (⟨p, hp, hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · exact ⟨p, Or.inl hp, hp1, hp2⟩
          · exact ⟨q, Or.inr rfl, hp1, hp2⟩
      have hlenL' : cur.items.val.length ≤ base.items.val.length + i.val := by
        simpa using hlenL
      have hmemL' : ∀ l, vsMem cur l ↔ vsMem base l ∨
          ∃ p ∈ s.pending.entries.val.take i.val,
            p.2.agent = agent ∧ p.2.policy.output_integ = l := by
        simpa using hmemL
      split
      case isTrue hb =>
        have hag0 : (s.pending.entries.val[i.val]'hlt).2.agent = agent := by simpa using hb
        have hag : q.2.agent = agent := by simpa [q] using hag0
        have hcapCur : cur.items.val.length < Usize.max := by
          have := hcap
          have := hlenL
          scalar_tac
        obtain ⟨cur', hcurEq, hcurMem, hcurLen⟩ := spec_imp_exists
          (vecSetInsertLen_spec types.IntegLevel.Insts.CoreCloneClone
            types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel integLevel_eq_spec cur
            q.2.policy.output_integ hcapCur)
        rw [hcurEq]
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · calc
            cur'.items.val.length ≤ cur.items.val.length + 1 := hcurLen
            _ ≤ (base.items.val.length + i.val) + 1 := Nat.add_le_add_right hlenL' 1
            _ = base.items.val.length + i2.val := by omega
        · intro l
          rw [show i2.val = i.val + 1 from by scalar_tac, htake l, hcurMem l, hmemL' l]
          simp [hag, eq_comm, or_assoc]
      case isFalse hb =>
        have hag0 : ¬(s.pending.entries.val[i.val]'hlt).2.agent = agent := by simpa using hb
        have hag : ¬q.2.agent = agent := by simpa [q] using hag0
        step*
        refine ⟨by scalar_tac, by omega, ?_, by scalar_tac⟩
        intro l
        rw [show i2.val = i.val + 1 from by scalar_tac, htake l, hmemL' l]
        simp [hag]
    case isFalse h =>
      have hi : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hmemL ⊢
      refine ⟨?_, by rwa [hi] at hlenL⟩
      intro l
      rw [hmemL l, hbase l]
      rfl
  · exact ⟨hi0, hlen, hmem⟩

theorem speculativeInteg_spec (s : state.KernelState) (agent : types.AgentId)
    (hnd : vmNodupKeys s.pending)
    (hcap : vmSetLen s.integ_levels agent + s.pending.entries.val.length ≤ Usize.max) :
    state.KernelState.speculative_integ s agent ⦃ out =>
      ∀ l, vsMem out l ↔ speculativeIntegC s agent l ⦄ := by
  unfold state.KernelState.speculative_integ
  obtain ⟨base, hbaseEq, hbaseMem, hbaseLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_clone_spec s.integ_levels agent)
  rw [hbaseEq]
  simp only [bind_tc_ok]
  obtain ⟨out, houtEq, houtMem, _⟩ := spec_imp_exists
    (speculativeIntegLoop_spec s agent hnd base hbaseMem
      (by rw [hbaseLen]; exact hcap) base 0#usize (by simp) (by simp) (by simp))
  rw [houtEq]
  exact houtMem

/-- Concrete speculative taint coincides with the abstract derived predicate. -/
theorem speculativeTaint_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId) (L : Tzimtzum.ConfLevel) :
    speculativeTaintC st agent (confC L) ↔ Tzimtzum.speculative_taint a agent L := by
  constructor
  · rintro (hh | ⟨p, hp, hpa, hpL⟩)
    · exact Or.inl ((hR.taint agent L).mpr hh)
    · obtain ⟨J, hJ, hrel⟩ := entry_to_abs_pending st bg a hR p hp
      obtain ⟨hjag, hsnap, _⟩ := hrel
      obtain ⟨_, _, _, _, _, hout, _⟩ := hsnap
      refine Or.inr ⟨p.1, J, hJ, ?_, ?_⟩
      · rw [hjag]
        exact hpa
      · change J.policy.output_conf = L
        rw [hout, hpL, confA_confC]
  · rintro (hh | ⟨I, J, hJ, hJa, hJL⟩)
    · exact Or.inl ((hR.taint agent L).mp hh)
    · obtain ⟨cj, hcj, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
      obtain ⟨hjag, hsnap, _⟩ := hrel
      obtain ⟨_, _, _, _, _, hout, _⟩ := hsnap
      refine Or.inr ⟨(I, cj), hcj, ?_, ?_⟩
      · rw [← hjag]
        exact hJa
      · change cj.policy.output_conf = confC L
        have hc := congrArg confC (hout.symm.trans hJL)
        simpa using hc

/-- Concrete speculative integrity coincides with the abstract derived predicate. -/
theorem speculativeInteg_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId) (L : Tzimtzum.IntegLevel) :
    speculativeIntegC st agent (integC L) ↔ Tzimtzum.speculative_integ a agent L := by
  constructor
  · rintro (hh | ⟨p, hp, hpa, hpL⟩)
    · exact Or.inl ((hR.integ agent L).mpr hh)
    · obtain ⟨J, hJ, hrel⟩ := entry_to_abs_pending st bg a hR p hp
      obtain ⟨hjag, hsnap, _⟩ := hrel
      obtain ⟨_, _, _, _, _, _, hout, _⟩ := hsnap
      refine Or.inr ⟨p.1, J, hJ, ?_, ?_⟩
      · rw [hjag]
        exact hpa
      · change J.policy.output_integ = L
        rw [hout, hpL, integA_integC]
  · rintro (hh | ⟨I, J, hJ, hJa, hJL⟩)
    · exact Or.inl ((hR.integ agent L).mp hh)
    · obtain ⟨cj, hcj, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
      obtain ⟨hjag, hsnap, _⟩ := hrel
      obtain ⟨_, _, _, _, _, _, hout, _⟩ := hsnap
      refine Or.inr ⟨(I, cj), hcj, ?_, ?_⟩
      · rw [← hjag]
        exact hJa
      · change cj.policy.output_integ = integC L
        have hc := congrArg integC (hout.symm.trans hJL)
        simpa using hc

/-! ## Capability check -/

theorem checkCapabilityLoop_spec (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) (ok0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ snap.required_caps.items.val.length)
    (hstart : ok0 = true ↔ ∀ c ∈ snap.required_caps.items.val.take i0.val,
      vmsMemLast s.agent_cap agent c) :
    transitions.check_capability_loop s agent snap ok0 i0 ⦃ b =>
      b = true ↔ ∀ c ∈ snap.required_caps.items.val, vmsMemLast s.agent_cap agent c ⦄ := by
  unfold transitions.check_capability_loop
  apply loop.spec_decr_nat
    (measure := fun p => snap.required_caps.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ snap.required_caps.items.val.length ∧
      (p.1 = true ↔ ∀ c ∈ snap.required_caps.items.val.take p.2.val,
        vmsMemLast s.agent_cap agent c))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.check_capability_loop.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < snap.required_caps.items.val.length := by scalar_tac
      step as ⟨c, hc⟩
      obtain ⟨b, hbEq, hb⟩ := spec_imp_exists
        (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          capability.CapKind.Insts.CoreCloneClone
          capability.CapKind.Insts.CoreCmpPartialEqCapKind capKind_eq_spec capKind_clone_spec
          s.agent_cap agent c)
      rw [hbEq]
      simp only [bind_tc_ok]
      have htake : (∀ x ∈ snap.required_caps.items.val.take (i.val + 1),
            vmsMemLast s.agent_cap agent x) ↔
          (∀ x ∈ snap.required_caps.items.val.take i.val,
            vmsMemLast s.agent_cap agent x) ∧ vmsMemLast s.agent_cap agent c := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hc]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh c (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      by_cases hbc : b = true
      · simp only [hbc, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        have hc' := hb.mp hbc
        exact ⟨fun h => ⟨h, hc'⟩, fun h => h.1⟩
      · rw [Bool.not_eq_true] at hbc
        simp only [hbc, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake]
        constructor
        · intro hfalse
          exact absurd hfalse (by decide)
        · rintro ⟨_, hc'⟩
          exact absurd (hb.mpr hc') (by simpa using hbc)
    case isFalse h =>
      have hi : i.val = snap.required_caps.items.val.length := by scalar_tac
      simpa [hi] using hinv
  · exact ⟨hi0, hstart⟩

theorem checkCapability_spec (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) :
    transitions.check_capability s agent snap ⦃ b =>
      b = true ↔ ∀ c ∈ snap.required_caps.items.val, vmsMemLast s.agent_cap agent c ⦄ := by
  unfold transitions.check_capability
  exact checkCapabilityLoop_spec s agent snap true 0#usize (by simp) (by simp)

theorem checkCapability_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap) :
    (∀ c ∈ snap.required_caps.items.val, vmsMemLast st.agent_cap agent c) ↔
      Tzimtzum.checkCapability a agent snapA := by
  obtain ⟨_, hcaps, _⟩ := hsnap
  constructor
  · intro hc C hC
    exact (hR.cap agent C).mpr (hc C ((hcaps C).mp hC))
  · intro hc C hC
    exact (hR.cap agent C).mp (hc C ((hcaps C).mpr hC))

/-! ## Clearance check -/

/-- Concrete image of the three clearance conjuncts. -/
def checkClearanceC (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) : Prop :=
  (∀ l, speculativeTaintC s agent l → confLeC l snap.conf_clearance = true) ∧
  (∀ p ∈ s.pending.entries.val, p.2.agent = agent →
    confLeC snap.output_conf p.2.policy.conf_clearance = true) ∧
  confLeC snap.output_conf snap.conf_clearance = true

theorem checkClearanceLoop0_spec (snap : types.ActionPolicySnapshot)
    (levels : collections.VecSet types.ConfLevel) (ok0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ levels.items.val.length)
    (hstart : ok0 = true ↔ ∀ l ∈ levels.items.val.take i0.val,
      confLeC l snap.conf_clearance = true) :
    transitions.check_clearance_loop0 snap ok0 levels i0 ⦃ out =>
      out.1 = snap ∧
      (out.2 = true ↔ ∀ l ∈ levels.items.val, confLeC l snap.conf_clearance = true) ⦄ := by
  unfold transitions.check_clearance_loop0
  apply loop.spec_decr_nat
    (measure := fun p => levels.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ levels.items.val.length ∧
      (p.1 = true ↔ ∀ l ∈ levels.items.val.take p.2.val,
        confLeC l snap.conf_clearance = true))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.check_clearance_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < levels.items.val.length := by scalar_tac
      step as ⟨l, hl⟩
      simp only [confLevel_le_spec, bind_tc_ok]
      have htake : (∀ x ∈ levels.items.val.take (i.val + 1),
            confLeC x snap.conf_clearance = true) ↔
          (∀ x ∈ levels.items.val.take i.val, confLeC x snap.conf_clearance = true) ∧
            confLeC l snap.conf_clearance = true := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hl]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh l (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      by_cases hle : confLeC l snap.conf_clearance = true
      · simp only [hle, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        exact ⟨fun h => ⟨h, hle⟩, fun h => h.1⟩
      · rw [Bool.not_eq_true] at hle
        simp only [hle, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake]
        constructor
        · intro hfalse
          exact absurd hfalse (by decide)
        · rintro ⟨_, hh⟩
          rw [hle] at hh
          contradiction
    case isFalse h =>
      have hi : i.val = levels.items.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hinv ⊢
      exact ⟨True.intro, hinv⟩
  · exact ⟨hi0, hstart⟩

theorem checkClearanceLoop1_spec (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) (hnd : vmNodupKeys s.pending)
    (start ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hstart : ok0 = true ↔ start = true ∧ ∀ p ∈ s.pending.entries.val.take i0.val,
      p.2.agent = agent → confLeC snap.output_conf p.2.policy.conf_clearance = true) :
    transitions.check_clearance_loop1 s agent snap ok0 i0 ⦃ out =>
      out.1 = snap ∧ (out.2 = true ↔ start = true ∧ ∀ p ∈ s.pending.entries.val,
        p.2.agent = agent → confLeC snap.output_conf p.2.policy.conf_clearance = true) ⦄ := by
  unfold transitions.check_clearance_loop1
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.2.val)
    (inv := fun p => p.1 = snap ∧ p.2.2.val ≤ s.pending.entries.val.length ∧
      (p.2.1 = true ↔ start = true ∧ ∀ q ∈ s.pending.entries.val.take p.2.2.val,
        q.2.agent = agent → confLeC snap.output_conf q.2.policy.conf_clearance = true))
  · rintro ⟨snapc, okc, i⟩ ⟨hsnap, hile, hinv⟩
    simp only at hsnap hile hinv
    rw [hsnap]
    simp only [transitions.check_clearance_loop1.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]
      simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]
        exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, bind_tc_ok]
      set q := s.pending.entries.val[i.val]'hlt with hq
      have hget : s.pending.entries.val[i.val]? = some q := by
        rw [List.getElem?_eq_getElem hlt, hq]
      have htake : (∀ p ∈ s.pending.entries.val.take (i.val + 1),
            p.2.agent = agent → confLeC snap.output_conf p.2.policy.conf_clearance = true) ↔
          (∀ p ∈ s.pending.entries.val.take i.val,
            p.2.agent = agent → confLeC snap.output_conf p.2.policy.conf_clearance = true) ∧
          (q.2.agent = agent → confLeC snap.output_conf q.2.policy.conf_clearance = true) := by
        rw [List.take_add_one, hget]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · intro hh
          exact ⟨fun p hp => hh p (Or.inl hp), hh q (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ p (hp | rfl)
          · exact h1 p hp
          · exact h2
      by_cases hag : q.2.agent = agent
      · have hag' : decide (q.2.agent = agent) = true := by simp [hag]
        simp only [hag', reduceIte, confLevel_le_spec, bind_tc_ok]
        by_cases hle : confLeC snap.output_conf q.2.policy.conf_clearance = true
        · simp only [hle, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
          exact ⟨fun h => ⟨h.1, h.2, fun _ => hle⟩, fun h => ⟨h.1, h.2.1⟩⟩
        · rw [Bool.not_eq_true] at hle
          simp only [hle, Bool.false_eq_true, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, htake]
          constructor
          · intro hfalse
            exact absurd hfalse (by decide)
          · rintro ⟨_, hh⟩
            have hh' := hh.2 hag
            rw [hle] at hh'
            contradiction
      · have hag' : decide (q.2.agent = agent) = false := by simp [hag]
        simp only [hag', Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        exact ⟨fun h => ⟨h.1, h.2, fun ha => absurd ha hag⟩,
          fun h => ⟨h.1, h.2.1⟩⟩
    case isFalse h =>
      have hi : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hinv ⊢
      exact ⟨True.intro, hinv⟩
  · exact ⟨rfl, hi0, hstart⟩

theorem checkClearance_spec (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) (hnd : vmNodupKeys s.pending)
    (hcap : vmSetLen s.taint_levels agent + s.pending.entries.val.length ≤ Usize.max) :
    transitions.check_clearance s agent snap ⦃ b => b = true ↔ checkClearanceC s agent snap ⦄ := by
  unfold transitions.check_clearance checkClearanceC
  obtain ⟨levels, hlevelsEq, hlevels⟩ := spec_imp_exists
    (speculativeTaint_spec s agent hnd hcap)
  rw [hlevelsEq]
  simp only [bind_tc_ok]
  obtain ⟨out0, hout0Eq, hsnap0, hout0⟩ := spec_imp_exists
    (checkClearanceLoop0_spec snap levels true 0#usize (by simp) (by simp))
  obtain ⟨snap0, ok0⟩ := out0
  simp only at hsnap0 hout0
  subst snap0
  rw [hout0Eq]
  simp only [bind_tc_ok]
  simp
  obtain ⟨out1, hout1Eq, hsnap1, hout1⟩ := spec_imp_exists
    (checkClearanceLoop1_spec s agent snap hnd ok0 ok0 0#usize (by simp) (by simp))
  obtain ⟨snap1, ok1⟩ := out1
  simp only at hsnap1 hout1
  subst snap1
  rw [hout1Eq]
  simp only [confLevel_le_spec, bind_tc_ok]
  by_cases hself : confLeC snap.output_conf snap.conf_clearance = true
  · simp [hself, hout1, hout0]
    intro _
    constructor
    · intro hall l hl
      exact hall l ((hlevels l).mpr hl)
    · intro hall l hl
      exact hall l ((hlevels l).mp hl)
  · rw [Bool.not_eq_true] at hself
    simp [hself]

theorem checkClearance_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap) :
    checkClearanceC st agent snap ↔ Tzimtzum.checkClearance a agent snapA := by
  obtain ⟨_, _, hclear, _, _, hout, _⟩ := hsnap
  constructor
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro L hL
      unfold Tzimtzum.clearance_admits
      rw [hclear, le_conf_confLeC]
      exact hlevels (confC L) ((speculativeTaint_bridge st bg a hR agent L).mpr hL)
    · intro I J hJ hJa
      obtain ⟨cj, hcj, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
      obtain ⟨hjag, hjsnap, _⟩ := hrel
      obtain ⟨_, _, hjclear, _⟩ := hjsnap
      have hcjA : cj.agent = agent := by rw [← hjag]; exact hJa
      have hh := hpending (I, cj) hcj hcjA
      show Tzimtzum.le_conf snapA.output_conf J.policy.conf_clearance
      rw [hout, hjclear, le_conf_confLeC_both]
      exact hh
    · show Tzimtzum.le_conf snapA.output_conf snapA.conf_clearance
      rw [hout, hclear, le_conf_confLeC_both]
      exact hself
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro l hl
      have ha : Tzimtzum.speculative_taint a agent (confA l) :=
        (speculativeTaint_bridge st bg a hR agent (confA l)).mp (by simpa using hl)
      have hh := hlevels (confA l) ha
      unfold Tzimtzum.clearance_admits at hh
      rw [hclear, le_conf_confLeC] at hh
      simpa using hh
    · intro p hp hpa
      obtain ⟨J, hJ, hrel⟩ := entry_to_abs_pending st bg a hR p hp
      obtain ⟨hjag, hjsnap, _⟩ := hrel
      obtain ⟨_, _, hjclear, _⟩ := hjsnap
      have hJa : J.agent = agent := by rw [hjag]; exact hpa
      have hh := hpending p.1 J hJ hJa
      unfold Tzimtzum.clearance_admits at hh
      rw [hout, hjclear, le_conf_confLeC_both] at hh
      exact hh
    · unfold Tzimtzum.clearance_admits at hself
      rw [← le_conf_confLeC_both, ← hout, ← hclear]
      exact hself

/-! ## Flow check -/

/-- One concrete flow atom. `vouched` matters only on the admissible inspect arm. -/
def flowPassC (bg : background.BackgroundTheory) (strict vouched : Bool)
    (l : types.ConfLevel) (e : types.EgressKind) : Prop :=
  ceilAdmitsC bg.allow_ceiling l e = true ∨
    (strict = false ∧ ceilAdmitsC bg.inspect_ceiling l e = true ∧ vouched = true)

theorem flowPass_spec (bg : background.BackgroundTheory) (strict vouched : Bool)
    (l : types.ConfLevel) (e : types.EgressKind) :
    (if strict then background.BackgroundTheory.flow_allows bg l e else do
      let ba ← background.BackgroundTheory.flow_allows bg l e
      if ba then ok true else do
        let bi ← background.BackgroundTheory.flow_inspects bg l e
        if bi then ok vouched else ok false) ⦃ b => b = true ↔ flowPassC bg strict vouched l e ⦄ := by
  by_cases hs : strict = true
  · have hs' : strict = true := hs
    subst strict
    simp only [reduceIte]
    obtain ⟨b, hbEq, hb⟩ := spec_imp_exists (flowAllows_spec bg l e)
    rw [hbEq]
    simp [flowPassC, hb]
  · have hs' : strict = false := by simpa using hs
    subst strict
    simp only [Bool.false_eq_true, reduceIte]
    obtain ⟨ba, hbaEq, hba⟩ := spec_imp_exists (flowAllows_spec bg l e)
    rw [hbaEq]
    simp only [bind_tc_ok]
    by_cases ha : ceilAdmitsC bg.allow_ceiling l e = true
    · have hbat : ba = true := hba.trans ha
      simp [hbat, flowPassC, ha]
    · have hbaf : ba = false := by rw [hba]; simpa using ha
      simp only [hbaf, Bool.false_eq_true, reduceIte]
      obtain ⟨bi, hbiEq, hbi⟩ := spec_imp_exists (flowInspects_spec bg l e)
      rw [hbiEq]
      by_cases hi : ceilAdmitsC bg.inspect_ceiling l e = true
      · have hbit : bi = true := hbi.trans hi
        simp [hbit, flowPassC, ha, hi]
      · have hbif : bi = false := by rw [hbi]; simpa using hi
        simp [hbif, flowPassC, ha, hi]

/-- CHECK 3a inner egress fold. -/
theorem checkFlowInner0_spec (bg : background.BackgroundTheory)
    (egr : collections.VecSet types.EgressKind) (strict : Bool) (l : types.ConfLevel)
    (ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ egr.items.val.length)
    (hstart : ok0 = true ↔ start = true ∧
      ∀ e ∈ egr.items.val.take i0.val, flowPassC bg strict true l e) :
    transitions.check_flow_loop0_loop0 bg egr strict ok0 l i0 ⦃ b =>
      b = true ↔ start = true ∧ ∀ e ∈ egr.items.val, flowPassC bg strict true l e ⦄ := by
  unfold transitions.check_flow_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => egr.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ egr.items.val.length ∧
      (p.1 = true ↔ start = true ∧
        ∀ e ∈ egr.items.val.take p.2.val, flowPassC bg strict true l e))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.check_flow_loop0_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < egr.items.val.length := by scalar_tac
      step as ⟨e, he⟩
      obtain ⟨pass, hpassEq, hpass⟩ := spec_imp_exists (flowPass_spec bg strict true l e)
      have hkernel :
          (if strict then background.BackgroundTheory.flow_allows bg l e else do
            let ba ← background.BackgroundTheory.flow_allows bg l e
            if ba then ok true else background.BackgroundTheory.flow_inspects bg l e) =
          (if strict then background.BackgroundTheory.flow_allows bg l e else do
            let ba ← background.BackgroundTheory.flow_allows bg l e
            if ba then ok true else do
              let bi ← background.BackgroundTheory.flow_inspects bg l e
              if bi then ok true else ok false) := by
        cases strict <;> simp only [Bool.false_eq_true, reduceIte]
        obtain ⟨ba, hbaEq, _⟩ := spec_imp_exists (flowAllows_spec bg l e)
        rw [hbaEq]
        cases ba <;> simp only [bind_tc_ok, Bool.false_eq_true, reduceIte]
        obtain ⟨bi, hbiEq, _⟩ := spec_imp_exists (flowInspects_spec bg l e)
        rw [hbiEq]
        cases bi <;> rfl
      rw [hkernel, hpassEq]
      simp only [bind_tc_ok]
      have htake : (∀ x ∈ egr.items.val.take (i.val + 1), flowPassC bg strict true l x) ↔
          (∀ x ∈ egr.items.val.take i.val, flowPassC bg strict true l x) ∧
            flowPassC bg strict true l e := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← he]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh e (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      by_cases hp : pass = true
      · simp only [hp, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        have hp' := hpass.mp hp
        exact ⟨fun h => ⟨h.1, h.2, hp'⟩, fun h => ⟨h.1, h.2.1⟩⟩
      · rw [Bool.not_eq_true] at hp
        simp only [hp, Bool.false_eq_true, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake]
        constructor
        · intro hfalse
          exact absurd hfalse (by decide)
        · rintro ⟨_, _, hh⟩
          exact absurd (hpass.mpr hh) (by simpa using hp)
    case isFalse h =>
      have hi : i.val = egr.items.val.length := by scalar_tac
      simpa [hi] using hinv
  · exact ⟨hi0, hstart⟩

/-- CHECK 3a outer speculative-taint fold. -/
theorem checkFlowLoop0_spec (bg : background.BackgroundTheory)
    (egr : collections.VecSet types.EgressKind) (strict : Bool)
    (levels : collections.VecSet types.ConfLevel) (ok0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ levels.items.val.length)
    (hstart : ok0 = true ↔ start = true ∧ ∀ l ∈ levels.items.val.take i0.val,
      ∀ e ∈ egr.items.val, flowPassC bg strict true l e) :
    transitions.check_flow_loop0 bg egr strict ok0 levels i0 ⦃ b =>
      b = true ↔ start = true ∧ ∀ l ∈ levels.items.val,
        ∀ e ∈ egr.items.val, flowPassC bg strict true l e ⦄ := by
  unfold transitions.check_flow_loop0
  apply loop.spec_decr_nat
    (measure := fun p => levels.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ levels.items.val.length ∧
      (p.1 = true ↔ start = true ∧ ∀ l ∈ levels.items.val.take p.2.val,
        ∀ e ∈ egr.items.val, flowPassC bg strict true l e))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.check_flow_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < levels.items.val.length := by scalar_tac
      step as ⟨l, hl⟩
      obtain ⟨ok2, hok2Eq, hok2⟩ := spec_imp_exists
        (checkFlowInner0_spec (start := okc) bg egr strict l okc 0#usize (by simp) (by simp))
      rw [hok2Eq]
      simp only [bind_tc_ok]
      have htake : (∀ x ∈ levels.items.val.take (i.val + 1),
            ∀ e ∈ egr.items.val, flowPassC bg strict true x e) ↔
          (∀ x ∈ levels.items.val.take i.val,
            ∀ e ∈ egr.items.val, flowPassC bg strict true x e) ∧
          (∀ e ∈ egr.items.val, flowPassC bg strict true l e) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hl]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh l (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [show i2.val = i.val + 1 from by scalar_tac, htake, hok2, hinv]
      tauto
    case isFalse h =>
      have hi : i.val = levels.items.val.length := by scalar_tac
      simpa [hi] using hinv
  · exact ⟨hi0, hstart⟩

/-- CHECK 3b inner egress fold for one pending record. -/
theorem checkFlowPendingInner_spec (bg : background.BackgroundTheory)
    (snap : types.ActionPolicySnapshot) (strict : Bool)
    (egr : collections.VecSet types.EgressKind) (vouched : Bool)
    (ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ egr.items.val.length)
    (hstart : ok0 = true ↔ start = true ∧ ∀ e ∈ egr.items.val.take i0.val,
      flowPassC bg strict vouched snap.output_conf e) :
    transitions.check_flow_loop1_loop0 bg snap strict ok0 egr vouched i0 ⦃ out =>
      out.1 = snap ∧ (out.2 = true ↔ start = true ∧ ∀ e ∈ egr.items.val,
        flowPassC bg strict vouched snap.output_conf e) ⦄ := by
  unfold transitions.check_flow_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun p => egr.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ egr.items.val.length ∧
      (p.1 = true ↔ start = true ∧ ∀ e ∈ egr.items.val.take p.2.val,
        flowPassC bg strict vouched snap.output_conf e))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.check_flow_loop1_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < egr.items.val.length := by scalar_tac
      step as ⟨e, he⟩
      obtain ⟨pass, hpassEq, hpass⟩ := spec_imp_exists
        (flowPass_spec bg strict vouched snap.output_conf e)
      rw [hpassEq]
      simp only [bind_tc_ok]
      have htake : (∀ x ∈ egr.items.val.take (i.val + 1),
            flowPassC bg strict vouched snap.output_conf x) ↔
          (∀ x ∈ egr.items.val.take i.val,
            flowPassC bg strict vouched snap.output_conf x) ∧
          flowPassC bg strict vouched snap.output_conf e := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← he]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh e (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      by_cases hp : pass = true
      · simp only [hp, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        have hp' := hpass.mp hp
        exact ⟨fun h => ⟨h.1, h.2, hp'⟩, fun h => ⟨h.1, h.2.1⟩⟩
      · rw [Bool.not_eq_true] at hp
        simp only [hp, Bool.false_eq_true, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake]
        constructor
        · intro hfalse
          exact absurd hfalse (by decide)
        · rintro ⟨_, _, hh⟩
          exact absurd (hpass.mpr hh) (by simpa using hp)
    case isFalse h =>
      have hi : i.val = egr.items.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hinv ⊢
      exact ⟨True.intro, hinv⟩
  · exact ⟨hi0, hstart⟩

/-- CHECK 3b fold over pending records. -/
theorem checkFlowPending_spec (s : state.KernelState) (bg : background.BackgroundTheory)
    (agent : types.AgentId) (snap : types.ActionPolicySnapshot) (strict : Bool)
    (hnd : vmNodupKeys s.pending) (start ok0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hstart : ok0 = true ↔ start = true ∧ ∀ p ∈ s.pending.entries.val.take i0.val,
      p.2.agent = agent → ∀ e ∈ p.2.egress.items.val,
        flowPassC bg strict (vouchedC p.2) snap.output_conf e) :
    transitions.check_flow_loop1 s bg agent snap strict ok0 i0 ⦃ out =>
      out.1 = snap ∧ (out.2 = true ↔ start = true ∧ ∀ p ∈ s.pending.entries.val,
        p.2.agent = agent → ∀ e ∈ p.2.egress.items.val,
          flowPassC bg strict (vouchedC p.2) snap.output_conf e) ⦄ := by
  unfold transitions.check_flow_loop1
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.2.val)
    (inv := fun p => p.1 = snap ∧ p.2.2.val ≤ s.pending.entries.val.length ∧
      (p.2.1 = true ↔ start = true ∧ ∀ q ∈ s.pending.entries.val.take p.2.2.val,
        q.2.agent = agent → ∀ e ∈ q.2.egress.items.val,
          flowPassC bg strict (vouchedC q.2) snap.output_conf e))
  · rintro ⟨snapc, okc, i⟩ ⟨hsnap, hile, hinv⟩
    simp only at hsnap hile hinv
    rw [hsnap]
    simp only [transitions.check_flow_loop1.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]
      simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]
        exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, vouched_eq, bind_tc_ok]
      set q := s.pending.entries.val[i.val]'hlt with hq
      have hget : s.pending.entries.val[i.val]? = some q := by
        rw [List.getElem?_eq_getElem hlt, hq]
      have htake : (∀ p ∈ s.pending.entries.val.take (i.val + 1),
            p.2.agent = agent → ∀ e ∈ p.2.egress.items.val,
              flowPassC bg strict (vouchedC p.2) snap.output_conf e) ↔
          (∀ p ∈ s.pending.entries.val.take i.val,
            p.2.agent = agent → ∀ e ∈ p.2.egress.items.val,
              flowPassC bg strict (vouchedC p.2) snap.output_conf e) ∧
          (q.2.agent = agent → ∀ e ∈ q.2.egress.items.val,
            flowPassC bg strict (vouchedC q.2) snap.output_conf e) := by
        rw [List.take_add_one, hget]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · intro hh
          exact ⟨fun p hp => hh p (Or.inl hp), hh q (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ p (hp | rfl)
          · exact h1 p hp
          · exact h2
      by_cases hag : q.2.agent = agent
      · have hag' : decide (q.2.agent = agent) = true := by simp [hag]
        simp only [hag', reduceIte]
        obtain ⟨out, houtEq, hsnapOut, hout⟩ := spec_imp_exists
          (checkFlowPendingInner_spec (start := okc) bg snap strict q.2.egress (vouchedC q.2)
            okc 0#usize (by simp) (by simp))
        obtain ⟨snapOut, okOut⟩ := out
        simp only at hsnapOut hout
        subst snapOut
        rw [houtEq]
        simp only [bind_tc_ok]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hout, hinv]
        constructor
        · rintro ⟨⟨hs, hpre⟩, hcur⟩
          exact ⟨hs, hpre, fun _ => hcur⟩
        · rintro ⟨hs, hpre, hcur⟩
          exact ⟨⟨hs, hpre⟩, hcur hag⟩
      · have hag' : decide (q.2.agent = agent) = false := by simp [hag]
        simp only [hag', Bool.false_eq_true, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        tauto
    case isFalse h =>
      have hi : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hinv ⊢
      exact ⟨True.intro, hinv⟩
  · exact ⟨rfl, hi0, hstart⟩


/-- CHECK 3c fold over the new invocation's egress set. -/
theorem checkFlowSelf_spec (bg : background.BackgroundTheory)
    (snap : types.ActionPolicySnapshot) (egr : collections.VecSet types.EgressKind)
    (strict start ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ egr.items.val.length)
    (hstart : ok0 = true ↔ start = true ∧ ∀ e ∈ egr.items.val.take i0.val,
      flowPassC bg strict true snap.output_conf e) :
    transitions.check_flow_loop2 bg snap egr strict ok0 i0 ⦃ b =>
      b = true ↔ start = true ∧ ∀ e ∈ egr.items.val,
        flowPassC bg strict true snap.output_conf e ⦄ := by
  unfold transitions.check_flow_loop2
  apply loop.spec_decr_nat
    (measure := fun p => egr.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ egr.items.val.length ∧
      (p.1 = true ↔ start = true ∧ ∀ e ∈ egr.items.val.take p.2.val,
        flowPassC bg strict true snap.output_conf e))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.check_flow_loop2.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < egr.items.val.length := by scalar_tac
      step as ⟨e, he⟩
      obtain ⟨pass, hpassEq, hpass⟩ := spec_imp_exists
        (flowPass_spec bg strict true snap.output_conf e)
      have hkernel :
          (if strict then background.BackgroundTheory.flow_allows bg snap.output_conf e else do
            let ba ← background.BackgroundTheory.flow_allows bg snap.output_conf e
            if ba then ok true else background.BackgroundTheory.flow_inspects bg snap.output_conf e) =
          (if strict then background.BackgroundTheory.flow_allows bg snap.output_conf e else do
            let ba ← background.BackgroundTheory.flow_allows bg snap.output_conf e
            if ba then ok true else do
              let bi ← background.BackgroundTheory.flow_inspects bg snap.output_conf e
              if bi then ok true else ok false) := by
        cases strict <;> simp only [Bool.false_eq_true, reduceIte]
        obtain ⟨ba, hbaEq, _⟩ := spec_imp_exists (flowAllows_spec bg snap.output_conf e)
        rw [hbaEq]
        cases ba <;> simp only [bind_tc_ok, Bool.false_eq_true, reduceIte]
        obtain ⟨bi, hbiEq, _⟩ := spec_imp_exists (flowInspects_spec bg snap.output_conf e)
        rw [hbiEq]
        cases bi <;> rfl
      rw [hkernel, hpassEq]
      simp only [bind_tc_ok]
      have htake : (∀ x ∈ egr.items.val.take (i.val + 1),
            flowPassC bg strict true snap.output_conf x) ↔
          (∀ x ∈ egr.items.val.take i.val,
            flowPassC bg strict true snap.output_conf x) ∧
          flowPassC bg strict true snap.output_conf e := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← he]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh e (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      by_cases hp : pass = true
      · simp only [hp, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        have hp' := hpass.mp hp
        exact ⟨fun h => ⟨h.1, h.2, hp'⟩, fun h => ⟨h.1, h.2.1⟩⟩
      · rw [Bool.not_eq_true] at hp
        simp only [hp, Bool.false_eq_true, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake]
        constructor
        · intro hfalse
          exact absurd hfalse (by decide)
        · rintro ⟨_, _, hh⟩
          exact absurd (hpass.mpr hh) (by simpa using hp)
    case isFalse h =>
      have hi : i.val = egr.items.val.length := by scalar_tac
      simpa [hi] using hinv
  · exact ⟨hi0, hstart⟩

/-- Concrete image of CHECK 3a/3b/3c. -/
def checkFlowC (s : state.KernelState) (bg : background.BackgroundTheory)
    (agent : types.AgentId) (snap : types.ActionPolicySnapshot)
    (egr : collections.VecSet types.EgressKind) (strict : Bool) : Prop :=
  (∀ l, speculativeTaintC s agent l → ∀ e ∈ egr.items.val,
    flowPassC bg strict true l e) ∧
  (∀ p ∈ s.pending.entries.val, p.2.agent = agent → ∀ e ∈ p.2.egress.items.val,
    flowPassC bg strict (vouchedC p.2) snap.output_conf e) ∧
  (∀ e ∈ egr.items.val, flowPassC bg strict true snap.output_conf e)

theorem checkFlow_spec (s : state.KernelState) (bg : background.BackgroundTheory)
    (agent : types.AgentId) (snap : types.ActionPolicySnapshot)
    (egr : collections.VecSet types.EgressKind) (strict : Bool)
    (hnd : vmNodupKeys s.pending)
    (hcap : vmSetLen s.taint_levels agent + s.pending.entries.val.length ≤ Usize.max) :
    transitions.check_flow s bg agent snap egr strict ⦃ b =>
      b = true ↔ checkFlowC s bg agent snap egr strict ⦄ := by
  unfold transitions.check_flow checkFlowC
  obtain ⟨levels, hlevelsEq, hlevels⟩ := spec_imp_exists
    (speculativeTaint_spec s agent hnd hcap)
  rw [hlevelsEq]
  simp only [bind_tc_ok]
  obtain ⟨ok0, hok0Eq, hok0⟩ := spec_imp_exists
    (checkFlowLoop0_spec (start := true) bg egr strict levels true 0#usize (by simp) (by simp))
  rw [hok0Eq]
  simp only [bind_tc_ok]
  obtain ⟨out1, hout1Eq, hsnap1, hout1⟩ := spec_imp_exists
    (checkFlowPending_spec s bg agent snap strict hnd ok0 ok0 0#usize (by simp) (by simp))
  obtain ⟨snap1, ok1⟩ := out1
  simp only at hsnap1 hout1
  subst snap1
  rw [hout1Eq]
  simp
  obtain ⟨ok2, hok2Eq, hok2⟩ := spec_imp_exists
    (checkFlowSelf_spec bg snap egr strict ok1 ok1 0#usize (by simp) (by simp))
  rw [hok2Eq]
  simp only [spec_ok]
  constructor
  · intro hall
    obtain ⟨h1, hself⟩ := hok2.mp hall
    obtain ⟨h0, hp⟩ := hout1.mp h1
    refine ⟨?_, ?_, hself⟩
    · intro l hl
      exact (hok0.mp h0).2 l ((hlevels l).mpr hl)
    · intro k v hkv
      exact hp (k, v) hkv
  · rintro ⟨hlev, hp, hself⟩
    apply hok2.mpr
    refine ⟨hout1.mpr ⟨hok0.mpr ?_, ?_⟩, hself⟩
    · refine ⟨rfl, ?_⟩
      intro l hl
      exact hlev l ((hlevels l).mp hl)
    · rintro ⟨k, v⟩ hkv
      exact hp k v hkv

/-- A strict concrete flow atom is exactly abstract ALLOW. -/
theorem flowPassStrict_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (L : Tzimtzum.ConfLevel) (E : types.EgressKind)
    (vouched : Bool) :
    flowPassC bg true vouched (confC L) E ↔ a.flow_allows L E := by
  simp only [flowPassC, reduceCtorEq, false_and, or_false]
  exact (hR.flowAllows L E).symm

/-- An admissible concrete flow atom with a vouch is abstract ALLOW-or-INSPECT. -/
theorem flowPassAdmissible_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (L : Tzimtzum.ConfLevel) (E : types.EgressKind) :
    flowPassC bg false true (confC L) E ↔ a.flow_allows L E ∨ a.flow_inspects L E := by
  simp only [flowPassC, reduceCtorEq, true_and, and_true]
  rw [hR.flowAllows L E, hR.flowInspects L E]

/-- Strict CHECK 3a/3b/3c bridge. -/
theorem checkFlowStrict_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap)
    (egr : collections.VecSet types.EgressKind) (egrA : types.EgressKind → Prop)
    (hEg : EgressAgree egr egrA) :
    checkFlowC st bg agent snap egr true ↔ Tzimtzum.checkFlowStrict a agent snapA egrA := by
  obtain ⟨_, _, _, _, _, hout, _⟩ := hsnap
  constructor
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro L E hL hE
      have hh := hlevels (confC L) ((speculativeTaint_bridge st bg a hR agent L).mpr hL)
        E ((hEg E).mpr hE)
      exact (flowPassStrict_bridge st bg a hR L E true).mp hh
    · intro I J E hJ hJa hJE
      obtain ⟨cj, hcj, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
      obtain ⟨hjag, _, hegr, _, _⟩ := hrel
      have hcjA : cj.agent = agent := by rw [← hjag]; exact hJa
      have hh := hpending (I, cj) hcj hcjA E ((hegr E).mp hJE)
      have hL : snapA.output_conf = confA snap.output_conf := hout
      rw [hL]
      exact (flowPassStrict_bridge st bg a hR (confA snap.output_conf) E (vouchedC cj)).mp
        (by simpa using hh)
    · intro E hE
      have hh := hself E ((hEg E).mpr hE)
      rw [hout]
      exact (flowPassStrict_bridge st bg a hR (confA snap.output_conf) E true).mp
        (by simpa using hh)
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro l hl E hE
      have ha := (speculativeTaint_bridge st bg a hR agent (confA l)).mp (by simpa using hl)
      have hh := hlevels (confA l) E ha ((hEg E).mp hE)
      have hc := (flowPassStrict_bridge st bg a hR (confA l) E true).mpr hh
      simpa using hc
    · intro p hp hpa E hpE
      obtain ⟨J, hJ, hrel⟩ := entry_to_abs_pending st bg a hR p hp
      obtain ⟨hjag, _, hegr, _, _⟩ := hrel
      have hJa : J.agent = agent := by rw [hjag]; exact hpa
      have hh := hpending p.1 J E hJ hJa ((hegr E).mpr hpE)
      rw [hout] at hh
      have hc :=
        (flowPassStrict_bridge st bg a hR (confA snap.output_conf) E (vouchedC p.2)).mpr hh
      simpa using hc
    · intro E hE
      have hh := hself E ((hEg E).mp hE)
      rw [hout] at hh
      have hc := (flowPassStrict_bridge st bg a hR (confA snap.output_conf) E true).mpr hh
      simpa using hc

/-- Admissible CHECK 3a/3b/3c bridge, including the pending-record vouch rule. -/
theorem checkFlowAdmissible_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap)
    (egr : collections.VecSet types.EgressKind) (egrA : types.EgressKind → Prop)
    (hEg : EgressAgree egr egrA) :
    checkFlowC st bg agent snap egr false ↔
      Tzimtzum.checkFlowAdmissible a agent snapA egrA := by
  obtain ⟨_, _, _, _, _, hout, _⟩ := hsnap
  constructor
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro L E hL hE
      have hh := hlevels (confC L) ((speculativeTaint_bridge st bg a hR agent L).mpr hL)
        E ((hEg E).mpr hE)
      exact (flowPassAdmissible_bridge st bg a hR L E).mp hh
    · intro I J E hJ hJa hJE
      obtain ⟨cj, hcj, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
      obtain ⟨hjag, _, hegr, hadm, _⟩ := hrel
      have hcjA : cj.agent = agent := by rw [← hjag]; exact hJa
      have hh := hpending (I, cj) hcj hcjA E ((hegr E).mp hJE)
      simp [flowPassC] at hh
      rw [hout]
      rcases hh with ha | ⟨hi, hv⟩
      · exact Or.inl ((hR.flowAllows (confA snap.output_conf) E).mpr (by simpa using ha))
      · exact Or.inr ⟨(hR.flowInspects (confA snap.output_conf) E).mpr (by simpa using hi),
          (vouchedC_bridge J cj hadm).mpr hv⟩
    · intro E hE
      have hh := hself E ((hEg E).mpr hE)
      rw [hout]
      exact (flowPassAdmissible_bridge st bg a hR (confA snap.output_conf) E).mp
        (by simpa using hh)
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro l hl E hE
      have ha := (speculativeTaint_bridge st bg a hR agent (confA l)).mp (by simpa using hl)
      have hh := hlevels (confA l) E ha ((hEg E).mp hE)
      have hc := (flowPassAdmissible_bridge st bg a hR (confA l) E).mpr hh
      simpa using hc
    · intro p hp hpa E hpE
      obtain ⟨J, hJ, hrel⟩ := entry_to_abs_pending st bg a hR p hp
      obtain ⟨hjag, _, hegr, hadm, _⟩ := hrel
      have hJa : J.agent = agent := by rw [hjag]; exact hpa
      have hh := hpending p.1 J E hJ hJa ((hegr E).mpr hpE)
      simp [flowPassC]
      rw [hout] at hh
      rcases hh with ha | ⟨hi, hv⟩
      · exact Or.inl (by simpa using (hR.flowAllows (confA snap.output_conf) E).mp ha)
      · exact Or.inr ⟨by simpa using (hR.flowInspects (confA snap.output_conf) E).mp hi,
          (vouchedC_bridge J p.2 hadm).mp hv⟩
    · intro E hE
      have hh := hself E ((hEg E).mp hE)
      rw [hout] at hh
      have hc := (flowPassAdmissible_bridge st bg a hR (confA snap.output_conf) E).mpr hh
      simpa using hc

/-! ## Integrity check -/

/-- One concrete integrity atom; pending inspect arms additionally require `vouched`. -/
def integPassC (strict vouched : Bool) (floor inspect l : types.IntegLevel) : Prop :=
  integLeC floor l = true ∨
    (strict = false ∧ integLeC inspect l = true ∧ vouched = true)

theorem integPass_spec (strict vouched : Bool) (floor inspect l : types.IntegLevel) :
    (if strict then types.IntegLevel.le floor l else do
      let ba ← types.IntegLevel.le floor l
      if ba then ok true else do
        let bi ← types.IntegLevel.le inspect l
        if bi then ok vouched else ok false) ⦃ b =>
      b = true ↔ integPassC strict vouched floor inspect l ⦄ := by
  by_cases hs : strict = true
  · simp only [hs, reduceIte, integLevel_le_spec]
    simp [integPassC, hs]
  · have hs' : strict = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, reduceIte, integLevel_le_spec, bind_tc_ok]
    by_cases ha : integLeC floor l = true
    · simp [ha, integPassC]
    · rw [Bool.not_eq_true] at ha
      simp only [ha, Bool.false_eq_true, reduceIte]
      by_cases hi : integLeC inspect l = true
      · simp [hi, integPassC, ha]
      · rw [Bool.not_eq_true] at hi
        simp [hi, integPassC, ha]

/-- CHECK 5a fold over speculative integrity. -/
theorem checkIntegLoop0_spec (snap : types.ActionPolicySnapshot) (strict : Bool)
    (levels : collections.VecSet types.IntegLevel) (start ok0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ levels.items.val.length)
    (hstart : ok0 = true ↔ start = true ∧ ∀ l ∈ levels.items.val.take i0.val,
      integPassC strict true snap.integ_floor snap.integ_inspect l) :
    transitions.check_integ_loop0 snap strict ok0 levels i0 ⦃ out =>
      out.1 = snap ∧ (out.2 = true ↔ start = true ∧ ∀ l ∈ levels.items.val,
        integPassC strict true snap.integ_floor snap.integ_inspect l) ⦄ := by
  unfold transitions.check_integ_loop0
  apply loop.spec_decr_nat
    (measure := fun p => levels.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ levels.items.val.length ∧
      (p.1 = true ↔ start = true ∧ ∀ l ∈ levels.items.val.take p.2.val,
        integPassC strict true snap.integ_floor snap.integ_inspect l))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.check_integ_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < levels.items.val.length := by scalar_tac
      step as ⟨l, hl⟩
      obtain ⟨pass, hpassEq, hpass⟩ := spec_imp_exists
        (integPass_spec strict true snap.integ_floor snap.integ_inspect l)
      have hkernel :
          (if strict then types.IntegLevel.le snap.integ_floor l else do
            let ba ← types.IntegLevel.le snap.integ_floor l
            if ba then ok true else types.IntegLevel.le snap.integ_inspect l) =
          (if strict then types.IntegLevel.le snap.integ_floor l else do
            let ba ← types.IntegLevel.le snap.integ_floor l
            if ba then ok true else do
              let bi ← types.IntegLevel.le snap.integ_inspect l
              if bi then ok true else ok false) := by
        cases strict <;> simp only [Bool.false_eq_true, reduceIte, integLevel_le_spec, bind_tc_ok]
        cases integLeC snap.integ_floor l <;> cases integLeC snap.integ_inspect l <;> rfl
      rw [hkernel, hpassEq]
      simp only [bind_tc_ok]
      have htake : (∀ x ∈ levels.items.val.take (i.val + 1),
            integPassC strict true snap.integ_floor snap.integ_inspect x) ↔
          (∀ x ∈ levels.items.val.take i.val,
            integPassC strict true snap.integ_floor snap.integ_inspect x) ∧
          integPassC strict true snap.integ_floor snap.integ_inspect l := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hl]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh l (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      by_cases hp : pass = true
      · simp only [hp, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        have hp' := hpass.mp hp
        exact ⟨fun h => ⟨h.1, h.2, hp'⟩, fun h => ⟨h.1, h.2.1⟩⟩
      · rw [Bool.not_eq_true] at hp
        simp only [hp, Bool.false_eq_true, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake]
        constructor
        · intro hfalse
          exact absurd hfalse (by decide)
        · rintro ⟨_, _, hh⟩
          exact absurd (hpass.mpr hh) (by simpa using hp)
    case isFalse h =>
      have hi : i.val = levels.items.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hinv ⊢
      exact ⟨True.intro, hinv⟩
  · exact ⟨hi0, hstart⟩

/-- CHECK 5b fold over pending outputs. -/
theorem checkIntegPending_spec (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) (strict : Bool) (hnd : vmNodupKeys s.pending)
    (start ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hstart : ok0 = true ↔ start = true ∧ ∀ p ∈ s.pending.entries.val.take i0.val,
      p.2.agent = agent → integPassC strict (vouchedC p.2)
        p.2.policy.integ_floor p.2.policy.integ_inspect snap.output_integ) :
    transitions.check_integ_loop1 s agent snap strict ok0 i0 ⦃ out =>
      out.1 = snap ∧ out.2.1 = strict ∧ (out.2.2 = true ↔ start = true ∧
        ∀ p ∈ s.pending.entries.val, p.2.agent = agent →
          integPassC strict (vouchedC p.2) p.2.policy.integ_floor
            p.2.policy.integ_inspect snap.output_integ) ⦄ := by
  unfold transitions.check_integ_loop1
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.2.2.val)
    (inv := fun p => p.1 = snap ∧ p.2.1 = strict ∧
      p.2.2.2.val ≤ s.pending.entries.val.length ∧
      (p.2.2.1 = true ↔ start = true ∧ ∀ q ∈ s.pending.entries.val.take p.2.2.2.val,
        q.2.agent = agent → integPassC strict (vouchedC q.2)
          q.2.policy.integ_floor q.2.policy.integ_inspect snap.output_integ))
  · rintro ⟨snapc, strictc, okc, i⟩ ⟨hsnap, hstrict, hile, hinv⟩
    simp only at hsnap hstrict hile hinv
    rw [hsnap, hstrict]
    simp only [transitions.check_integ_loop1.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]
      simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]
        exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, bind_tc_ok]
      set q := s.pending.entries.val[i.val]'hlt with hq
      have hget : s.pending.entries.val[i.val]? = some q := by
        rw [List.getElem?_eq_getElem hlt, hq]
      have htake : (∀ p ∈ s.pending.entries.val.take (i.val + 1), p.2.agent = agent →
            integPassC strict (vouchedC p.2) p.2.policy.integ_floor
              p.2.policy.integ_inspect snap.output_integ) ↔
          (∀ p ∈ s.pending.entries.val.take i.val, p.2.agent = agent →
            integPassC strict (vouchedC p.2) p.2.policy.integ_floor
              p.2.policy.integ_inspect snap.output_integ) ∧
          (q.2.agent = agent → integPassC strict (vouchedC q.2)
            q.2.policy.integ_floor q.2.policy.integ_inspect snap.output_integ) := by
        rw [List.take_add_one, hget]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · intro hh
          exact ⟨fun p hp => hh p (Or.inl hp), hh q (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ p (hp | rfl)
          · exact h1 p hp
          · exact h2
      by_cases hag : q.2.agent = agent
      · have hag' : decide (q.2.agent = agent) = true := by simp [hag]
        simp only [hag', reduceIte]
        obtain ⟨pass, hpassEq, hpass⟩ := spec_imp_exists
          (integPass_spec strict (vouchedC q.2) q.2.policy.integ_floor
            q.2.policy.integ_inspect snap.output_integ)
        rw [vouched_eq q.2]
        rw [hpassEq]
        simp only [bind_tc_ok]
        by_cases hp : pass = true
        · simp only [hp, reduceIte]
          step as ⟨i2, hi2⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
          have hp' := hpass.mp hp
          exact ⟨fun h => ⟨h.1, h.2, fun _ => hp'⟩, fun h => ⟨h.1, h.2.1⟩⟩
        · rw [Bool.not_eq_true] at hp
          simp only [hp, Bool.false_eq_true, reduceIte]
          step as ⟨i2, hi2⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, htake]
          constructor
          · intro hfalse
            exact absurd hfalse (by decide)
          · rintro ⟨_, hh⟩
            exact absurd (hpass.mpr (hh.2 hag)) (by simpa using hp)
      · have hag' : decide (q.2.agent = agent) = false := by simp [hag]
        simp only [hag', Bool.false_eq_true, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        tauto
    case isFalse h =>
      have hi : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hinv ⊢
      exact ⟨True.intro, True.intro, hinv⟩
  · exact ⟨rfl, rfl, hi0, hstart⟩

/-- CHECK 5c's non-looping self atom. -/
theorem integSelfPass_spec (strict : Bool) (snap : types.ActionPolicySnapshot) :
    (if strict then types.IntegLevel.le snap.integ_floor snap.output_integ else do
      let ba ← types.IntegLevel.le snap.integ_floor snap.output_integ
      if ba then ok true else types.IntegLevel.le snap.integ_inspect snap.output_integ) ⦃ b =>
      b = true ↔ integPassC strict true snap.integ_floor snap.integ_inspect snap.output_integ ⦄ := by
  have hkernel :
      (if strict then types.IntegLevel.le snap.integ_floor snap.output_integ else do
        let ba ← types.IntegLevel.le snap.integ_floor snap.output_integ
        if ba then ok true else types.IntegLevel.le snap.integ_inspect snap.output_integ) =
      (if strict then types.IntegLevel.le snap.integ_floor snap.output_integ else do
        let ba ← types.IntegLevel.le snap.integ_floor snap.output_integ
        if ba then ok true else do
          let bi ← types.IntegLevel.le snap.integ_inspect snap.output_integ
          if bi then ok true else ok false) := by
    cases strict <;> simp only [Bool.false_eq_true, reduceIte, integLevel_le_spec, bind_tc_ok]
    cases integLeC snap.integ_floor snap.output_integ <;>
      cases integLeC snap.integ_inspect snap.output_integ <;> rfl
  rw [hkernel]
  exact integPass_spec strict true snap.integ_floor snap.integ_inspect snap.output_integ

/-- Concrete image of CHECK 5a/5b/5c. -/
def checkIntegC (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) (strict : Bool) : Prop :=
  (∀ l, speculativeIntegC s agent l →
    integPassC strict true snap.integ_floor snap.integ_inspect l) ∧
  (∀ p ∈ s.pending.entries.val, p.2.agent = agent →
    integPassC strict (vouchedC p.2) p.2.policy.integ_floor
      p.2.policy.integ_inspect snap.output_integ) ∧
  integPassC strict true snap.integ_floor snap.integ_inspect snap.output_integ

theorem checkInteg_spec (s : state.KernelState) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot) (strict : Bool) (hnd : vmNodupKeys s.pending)
    (hcap : vmSetLen s.integ_levels agent + s.pending.entries.val.length ≤ Usize.max) :
    transitions.check_integ s agent snap strict ⦃ b =>
      b = true ↔ checkIntegC s agent snap strict ⦄ := by
  unfold transitions.check_integ checkIntegC
  obtain ⟨levels, hlevelsEq, hlevels⟩ := spec_imp_exists
    (speculativeInteg_spec s agent hnd hcap)
  rw [hlevelsEq]
  simp only [bind_tc_ok]
  obtain ⟨out0, hout0Eq, hsnap0, hout0⟩ := spec_imp_exists
    (checkIntegLoop0_spec snap strict levels true true 0#usize (by simp) (by simp))
  obtain ⟨snap0, ok0⟩ := out0
  simp only at hsnap0 hout0
  subst snap0
  rw [hout0Eq]
  simp
  obtain ⟨out1, hout1Eq, hsnap1, hstrict1, hout1⟩ := spec_imp_exists
    (checkIntegPending_spec s agent snap strict hnd ok0 ok0 0#usize (by simp) (by simp))
  obtain ⟨snap1, strict1, ok1⟩ := out1
  simp only at hsnap1 hstrict1 hout1
  subst snap1
  subst strict1
  rw [hout1Eq]
  simp
  obtain ⟨selfPass, hselfEq, hself⟩ := spec_imp_exists (integSelfPass_spec strict snap)
  have hselfEq' := hselfEq
  simp only [integLevel_le_spec, bind_tc_ok] at hselfEq'
  rw [hselfEq']
  simp only [bind_tc_ok]
  by_cases hs : selfPass = true
  · simp only [hs, reduceIte, spec_ok]
    constructor
    · intro hall
      obtain ⟨h0, hp⟩ := hout1.mp hall
      refine ⟨?_, ?_, hself.mp hs⟩
      · intro l hl
        exact (hout0.mp h0).2 l ((hlevels l).mpr hl)
      · intro k v hkv
        exact hp (k, v) hkv
    · rintro ⟨hlev, hp, hselfC⟩
      apply hout1.mpr
      refine ⟨hout0.mpr ⟨True.intro, ?_⟩, ?_⟩
      · intro l hl
        exact hlev l ((hlevels l).mp hl)
      · rintro ⟨k, v⟩ hkv
        exact hp k v hkv
  · rw [Bool.not_eq_true] at hs
    simp only [hs, Bool.false_eq_true, reduceIte, spec_ok]
    constructor
    · intro hfalse
      exact absurd hfalse (by decide)
    · rintro ⟨_, _, hh⟩
      exact absurd (hself.mpr hh) (by simpa using hs)

/-- Strict concrete integrity atom bridge. -/
theorem integPassStrict_bridge (floor inspect : types.IntegLevel)
    (L : Tzimtzum.IntegLevel) (vouched : Bool) :
    integPassC true vouched floor inspect (integC L) ↔
      Tzimtzum.le_integ (integA floor) L := by
  simp only [integPassC, reduceCtorEq, false_and, or_false]
  exact (le_integ_integLeC' floor L).symm

/-- Admissible concrete integrity atom bridge. -/
theorem integPassAdmissible_bridge (floor inspect : types.IntegLevel)
    (L : Tzimtzum.IntegLevel) :
    integPassC false true floor inspect (integC L) ↔
      Tzimtzum.le_integ (integA floor) L ∨ Tzimtzum.le_integ (integA inspect) L := by
  simp only [integPassC, reduceCtorEq, true_and, and_true]
  rw [le_integ_integLeC' floor L, le_integ_integLeC' inspect L]

/-- Strict CHECK 5a/5b/5c bridge. -/
theorem checkIntegStrict_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap) :
    checkIntegC st agent snap true ↔ Tzimtzum.checkIntegStrict a agent snapA := by
  obtain ⟨_, _, _, hfloor, hinspect, _, hout, _⟩ := hsnap
  constructor
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro L hL
      have hh := hlevels (integC L) ((speculativeInteg_bridge st bg a hR agent L).mpr hL)
      unfold Tzimtzum.integ_allows
      rw [hfloor]
      exact (integPassStrict_bridge snap.integ_floor snap.integ_inspect L true).mp hh
    · intro I J hJ hJa
      obtain ⟨cj, hcj, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
      obtain ⟨hjag, hjsnap, _, _, _⟩ := hrel
      obtain ⟨_, _, _, hjfloor, hjinspect, _, hjout, _⟩ := hjsnap
      have hcjA : cj.agent = agent := by rw [← hjag]; exact hJa
      have hh := hpending (I, cj) hcj hcjA
      unfold Tzimtzum.integ_allows
      rw [hout, hjfloor]
      exact (integPassStrict_bridge cj.policy.integ_floor cj.policy.integ_inspect
        (integA snap.output_integ) (vouchedC cj)).mp (by simpa using hh)
    · unfold Tzimtzum.integ_allows
      rw [hout, hfloor]
      exact (integPassStrict_bridge snap.integ_floor snap.integ_inspect
        (integA snap.output_integ) true).mp (by simpa using hself)
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro l hl
      have ha := (speculativeInteg_bridge st bg a hR agent (integA l)).mp (by simpa using hl)
      have hh := hlevels (integA l) ha
      unfold Tzimtzum.integ_allows at hh
      rw [hfloor] at hh
      have hc := (integPassStrict_bridge snap.integ_floor snap.integ_inspect
        (integA l) true).mpr hh
      simpa using hc
    · intro p hp hpa
      obtain ⟨J, hJ, hrel⟩ := entry_to_abs_pending st bg a hR p hp
      obtain ⟨hjag, hjsnap, _, _, _⟩ := hrel
      obtain ⟨_, _, _, hjfloor, hjinspect, _, _, _⟩ := hjsnap
      have hJa : J.agent = agent := by rw [hjag]; exact hpa
      have hh := hpending p.1 J hJ hJa
      unfold Tzimtzum.integ_allows at hh
      rw [hout, hjfloor] at hh
      have hc := (integPassStrict_bridge p.2.policy.integ_floor p.2.policy.integ_inspect
        (integA snap.output_integ) (vouchedC p.2)).mpr hh
      simpa using hc
    · unfold Tzimtzum.integ_allows at hself
      rw [hout, hfloor] at hself
      have hc := (integPassStrict_bridge snap.integ_floor snap.integ_inspect
        (integA snap.output_integ) true).mpr hself
      simpa using hc

/-- Admissible CHECK 5a/5b/5c bridge, including pending vouch evidence. -/
theorem checkIntegAdmissible_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap) :
    checkIntegC st agent snap false ↔ Tzimtzum.checkIntegAdmissible a agent snapA := by
  obtain ⟨_, _, _, hfloor, hinspect, _, hout, _⟩ := hsnap
  constructor
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro L hL
      have hh := hlevels (integC L) ((speculativeInteg_bridge st bg a hR agent L).mpr hL)
      unfold Tzimtzum.integ_allows Tzimtzum.integ_inspects
      rw [hfloor, hinspect]
      exact (integPassAdmissible_bridge snap.integ_floor snap.integ_inspect L).mp hh
    · intro I J hJ hJa
      obtain ⟨cj, hcj, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
      obtain ⟨hjag, hjsnap, _, hadm, _⟩ := hrel
      obtain ⟨_, _, _, hjfloor, hjinspect, _, _, _⟩ := hjsnap
      have hcjA : cj.agent = agent := by rw [← hjag]; exact hJa
      have hh := hpending (I, cj) hcj hcjA
      simp [integPassC] at hh
      unfold Tzimtzum.integ_allows Tzimtzum.integ_inspects
      rw [hout, hjfloor, hjinspect]
      rcases hh with ha | ⟨hi, hv⟩
      · exact Or.inl ((le_integ_integLeC' cj.policy.integ_floor
          (integA snap.output_integ)).mpr (by simpa using ha))
      · exact Or.inr ⟨(le_integ_integLeC' cj.policy.integ_inspect
          (integA snap.output_integ)).mpr (by simpa using hi),
          (vouchedC_bridge J cj hadm).mpr hv⟩
    · unfold Tzimtzum.integ_allows Tzimtzum.integ_inspects
      rw [hout, hfloor, hinspect]
      exact (integPassAdmissible_bridge snap.integ_floor snap.integ_inspect
        (integA snap.output_integ)).mp (by simpa using hself)
  · rintro ⟨hlevels, hpending, hself⟩
    refine ⟨?_, ?_, ?_⟩
    · intro l hl
      have ha := (speculativeInteg_bridge st bg a hR agent (integA l)).mp (by simpa using hl)
      have hh := hlevels (integA l) ha
      unfold Tzimtzum.integ_allows Tzimtzum.integ_inspects at hh
      rw [hfloor, hinspect] at hh
      have hc := (integPassAdmissible_bridge snap.integ_floor snap.integ_inspect
        (integA l)).mpr hh
      simpa using hc
    · intro p hp hpa
      obtain ⟨J, hJ, hrel⟩ := entry_to_abs_pending st bg a hR p hp
      obtain ⟨hjag, hjsnap, _, hadm, _⟩ := hrel
      obtain ⟨_, _, _, hjfloor, hjinspect, _, _, _⟩ := hjsnap
      have hJa : J.agent = agent := by rw [hjag]; exact hpa
      have hh := hpending p.1 J hJ hJa
      simp [integPassC]
      unfold Tzimtzum.integ_allows Tzimtzum.integ_inspects at hh
      rw [hout, hjfloor, hjinspect] at hh
      rcases hh with ha | ⟨hi, hv⟩
      · exact Or.inl (by simpa using (le_integ_integLeC' p.2.policy.integ_floor
          (integA snap.output_integ)).mp ha)
      · exact Or.inr ⟨by simpa using (le_integ_integLeC' p.2.policy.integ_inspect
          (integA snap.output_integ)).mp hi, (vouchedC_bridge J p.2 hadm).mp hv⟩
    · unfold Tzimtzum.integ_allows Tzimtzum.integ_inspects at hself
      rw [hout, hfloor, hinspect] at hself
      have hc := (integPassAdmissible_bridge snap.integ_floor snap.integ_inspect
        (integA snap.output_integ)).mpr hself
      simpa using hc

/-! ## Egress narrowing and composed admissibility -/

theorem egressNarrowsLoop_spec (egr declared : collections.VecSet types.EgressKind)
    (ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ egr.items.val.length)
    (hstart : ok0 = true ↔ ∀ e ∈ egr.items.val.take i0.val, e ∈ declared.items.val) :
    transitions.egress_narrows_loop egr declared ok0 i0 ⦃ b =>
      b = true ↔ ∀ e ∈ egr.items.val, e ∈ declared.items.val ⦄ := by
  unfold transitions.egress_narrows_loop
  apply loop.spec_decr_nat
    (measure := fun p => egr.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ egr.items.val.length ∧
      (p.1 = true ↔ ∀ e ∈ egr.items.val.take p.2.val, e ∈ declared.items.val))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.egress_narrows_loop.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < egr.items.val.length := by scalar_tac
      step as ⟨e, he⟩
      obtain ⟨b, hbEq, hb⟩ := spec_imp_exists
        (vecSetContains_spec types.EgressKind.Insts.CoreCloneClone
          types.EgressKind.Insts.CoreCmpPartialEqEgressKind egressKind_eq_spec declared e)
      rw [hbEq]
      simp only [bind_tc_ok]
      have htake : (∀ x ∈ egr.items.val.take (i.val + 1), x ∈ declared.items.val) ↔
          (∀ x ∈ egr.items.val.take i.val, x ∈ declared.items.val) ∧ e ∈ declared.items.val := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← he]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh e (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | rfl)
          · exact h1 x hx
          · exact h2
      by_cases hbe : b = true
      · simp only [hbe, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake, hinv]
        have he' := hb.mp hbe
        exact ⟨fun h => ⟨h, he'⟩, fun h => h.1⟩
      · rw [Bool.not_eq_true] at hbe
        simp only [hbe, Bool.false_eq_true, reduceIte]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htake]
        constructor
        · intro hfalse
          exact absurd hfalse (by decide)
        · rintro ⟨_, hh⟩
          exact absurd (hb.mpr hh) (by simpa using hbe)
    case isFalse h =>
      have hi : i.val = egr.items.val.length := by scalar_tac
      simpa [hi] using hinv
  · exact ⟨hi0, hstart⟩

theorem egressNarrows_spec (egr declared : collections.VecSet types.EgressKind) :
    transitions.egress_narrows egr declared ⦃ b =>
      b = true ↔ ∀ e ∈ egr.items.val, e ∈ declared.items.val ⦄ := by
  unfold transitions.egress_narrows
  exact egressNarrowsLoop_spec egr declared true 0#usize (by simp) (by simp)

theorem egressCovers_spec (declared egr : collections.VecSet types.EgressKind) :
    transitions.egress_covers declared egr ⦃ b =>
      b = true ↔ declared.items.val ≠ [] → egr.items.val ≠ [] ⦄ := by
  unfold transitions.egress_covers
  obtain ⟨bd, hbdEq, hbd⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.EgressKind.Insts.CoreCloneClone
      types.EgressKind.Insts.CoreCmpPartialEqEgressKind declared)
  rw [hbdEq]
  simp only [bind_tc_ok]
  by_cases hd : declared.items.val = []
  · have hbdt : bd = true := hbd.mpr hd
    simp [hbdt, hd]
  · have hbdf : bd = false := by
      cases hbdv : bd with
      | false => rfl
      | true => exact absurd (hbd.mp hbdv) hd
    simp only [hbdf, Bool.false_eq_true, reduceIte]
    obtain ⟨be, hbeEq, hbe⟩ := spec_imp_exists
      (vecSetIsEmpty_spec types.EgressKind.Insts.CoreCloneClone
        types.EgressKind.Insts.CoreCmpPartialEqEgressKind egr)
    rw [hbeEq]
    cases hbev : be with
    | false =>
      have he : egr.items.val ≠ [] := by
        intro hempty
        have hh := hbe.mpr hempty
        rw [hbev] at hh
        contradiction
      simp [he, hd]
    | true =>
      have he : egr.items.val = [] := hbe.mp hbev
      simp [he, hd]

theorem beginAdmissible_spec (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap)
    (egr : collections.VecSet types.EgressKind) (egrA : types.EgressKind → Prop)
    (hEg : EgressAgree egr egrA) (authorized : Bool) (authorizedA : Prop)
    (hAu : AuAgree authorized authorizedA)
    (hcapT : vmSetLen st.taint_levels agent + st.pending.entries.val.length ≤ Usize.max)
    (hcapI : vmSetLen st.integ_levels agent + st.pending.entries.val.length ≤ Usize.max) :
    transitions.begin_admissible st bg agent snap egr authorized ⦃ b =>
      b = true ↔ Tzimtzum.beginAdmissible a agent snapA egrA authorizedA ⦄ := by
  unfold transitions.begin_admissible
  simp only [Tzimtzum.beginAdmissible_iff]
  obtain ⟨bc, hbcEq, hbc⟩ := spec_imp_exists (checkCapability_spec st agent snap)
  rw [hbcEq]
  simp only [bind_tc_ok]
  by_cases hc : bc = true
  · simp only [hc, reduceIte]
    by_cases hau : authorized = true
    · simp only [hau, reduceIte]
      obtain ⟨bcl, hbclEq, hbcl⟩ := spec_imp_exists
        (checkClearance_spec st agent snap hR.ndPending hcapT)
      rw [hbclEq]
      simp only [bind_tc_ok]
      by_cases hcl : bcl = true
      · simp only [hcl, reduceIte]
        obtain ⟨bf, hbfEq, hbf⟩ := spec_imp_exists
          (checkFlow_spec st bg agent snap egr false hR.ndPending hcapT)
        rw [hbfEq]
        simp only [bind_tc_ok]
        by_cases hf : bf = true
        · simp only [hf, reduceIte]
          obtain ⟨bi, hbiEq, hbi⟩ := spec_imp_exists
            (checkInteg_spec st agent snap false hR.ndPending hcapI)
          rw [hbiEq]
          simp only [spec_ok]
          constructor
          · intro hi
            exact ⟨(checkCapability_bridge st bg a hR agent snap snapA hsnap).mp (hbc.mp hc),
              hAu.mp hau,
              (checkClearance_bridge st bg a hR agent snap snapA hsnap).mp (hbcl.mp hcl),
              (checkFlowAdmissible_bridge st bg a hR agent snap snapA hsnap egr egrA hEg).mp
                (hbf.mp hf),
              (checkIntegAdmissible_bridge st bg a hR agent snap snapA hsnap).mp (hbi.mp hi)⟩
          · rintro ⟨_, _, _, _, hi⟩
            exact hbi.mpr
              ((checkIntegAdmissible_bridge st bg a hR agent snap snapA hsnap).mpr hi)
        · have hf0 : bf = false := by simpa using hf
          simp only [hf0, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
          rintro ⟨_, _, _, hflow, _⟩
          have := hbf.mpr
            ((checkFlowAdmissible_bridge st bg a hR agent snap snapA hsnap egr egrA hEg).mpr
              hflow)
          rw [hf0] at this
          contradiction
      · have hcl0 : bcl = false := by simpa using hcl
        simp only [hcl0, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
        rintro ⟨_, _, hclear, _, _⟩
        have := hbcl.mpr
          ((checkClearance_bridge st bg a hR agent snap snapA hsnap).mpr hclear)
        rw [hcl0] at this
        contradiction
    · have hau0 : authorized = false := by simpa using hau
      simp only [hau0, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
      rintro ⟨_, hauth, _, _, _⟩
      have := hAu.mpr hauth
      rw [hau0] at this
      contradiction
  · have hc0 : bc = false := by simpa using hc
    simp only [hc0, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
    rintro ⟨hcap, _, _, _, _⟩
    have := hbc.mpr ((checkCapability_bridge st bg a hR agent snap snapA hsnap).mpr hcap)
    rw [hc0] at this
    contradiction

/-! ## Invocation post-state transport -/

open Classical in
noncomputable def beginAbs (a : AbsState) (agent : types.AgentId) (inv : types.InvocationId)
    (chal : types.ChallengeId)
    (snap : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest)
    (egr : types.EgressKind → Prop) (ah : types.ContentHash) (authorized : Prop)
    (v : Tzimtzum.Verdict) : AbsState :=
  { a with
    pending := fun I => if I = inv then
      match v, a.mode with
      | .allow, _ => some (Tzimtzum.PendingInvocation.mk agent snap egr
          .plain .permitted authorized False)
      | .inspection_required, .enforce => none
      | .inspection_required, .monitor => some (Tzimtzum.PendingInvocation.mk agent snap egr
          .bypassed .monitor_bypassed authorized False)
      | .deny, _ => some (Tzimtzum.PendingInvocation.mk agent snap egr
          .bypassed .monitor_bypassed authorized False)
      else a.pending I
    challenges := fun I => if I = inv then
      match v, a.mode with
      | .inspection_required, .enforce =>
        some (Tzimtzum.ChallengeScope.mk chal agent snap egr ah authorized)
      | _, _ => a.challenges I
      else a.challenges I
    consumed_ids := fun I => a.consumed_ids I ∨ I = inv }

theorem pendingRel_new (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap)
    (egr : collections.VecSet types.EgressKind) (egrA : types.EgressKind → Prop)
    (hEg : EgressAgree egr egrA) (authorized : Bool) (authorizedA : Prop)
    (hAu : AuAgree authorized authorizedA) (adm : types.Admission)
    (admA : Tzimtzum.Admission types.AttestationId) (hadm : admissionRel admA adm)
    (disp : types.Disposition) (dispA' : Tzimtzum.Disposition)
    (hdisp : dispA' = dispA disp) :
    pendingRel
      { agent := agent, policy := snapA, egress := egrA, admission := admA,
        disposition := dispA', authorized := authorizedA, quarantined := False }
      { agent := agent, policy := snap, egress := egr, admission := adm,
        disposition := disp, authorized := authorized, quarantined := false } := by
  exact ⟨rfl, hsnap, fun E => (hEg E).symm, hadm, hdisp, hAu.symm, by simp⟩

theorem challengeRel_new (chal : types.ChallengeId) (agent : types.AgentId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap)
    (egr : collections.VecSet types.EgressKind) (egrA : types.EgressKind → Prop)
    (hEg : EgressAgree egr egrA) (ah : types.ContentHash)
    (authorized : Bool) (authorizedA : Prop) (hAu : AuAgree authorized authorizedA) :
    challengeRel
      { challenge := chal, agent := agent, policy := snapA, egress := egrA,
        args_hash := ah, authorized := authorizedA }
      { challenge := chal, agent := agent, policy := snap, egress := egr,
        args_hash := ah, authorized := authorized } := by
  exact ⟨rfl, rfl, hsnap, fun E => (hEg E).symm, rfl, hAu.symm⟩

theorem pending_clause_insert (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (inv : types.InvocationId)
    (aj : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.AttestationId types.PolicyDigest)
    (cj : types.PendingInvocation)
    (hrel : pendingRel aj cj)
    (vm : collections.VecMap types.InvocationId types.PendingInvocation)
    (hvm : ∀ I, vmLastEntry vm.entries.val I =
      if I = inv then some (inv, cj) else vmLastEntry st.pending.entries.val I) :
    ∀ I, optRel pendingRel (if I = inv then some aj else a.pending I)
      ((vmLastEntry vm.entries.val I).map Prod.snd) := by
  intro I
  rw [hvm I]
  by_cases hI : I = inv
  · subst I
    simp [hrel, optRel]
  · rw [if_neg hI, if_neg hI]
    exact hR.pending I

theorem challenge_clause_insert (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (inv : types.InvocationId)
    (ac : Tzimtzum.ChallengeScope types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.ChallengeId types.PolicyDigest types.ContentHash)
    (cc : types.ChallengeScope) (hrel : challengeRel ac cc)
    (vm : collections.VecMap types.InvocationId types.ChallengeScope)
    (hvm : ∀ I, vmLastEntry vm.entries.val I =
      if I = inv then some (inv, cc) else vmLastEntry st.challenges.entries.val I) :
    ∀ I, optRel challengeRel (if I = inv then some ac else a.challenges I)
      ((vmLastEntry vm.entries.val I).map Prod.snd) := by
  intro I
  rw [hvm I]
  by_cases hI : I = inv
  · subst I
    simp [hrel, optRel]
  · rw [if_neg hI, if_neg hI]
    exact hR.challenges I

/-- Rebuild `R` after a begin branch, given the three changed clauses. -/
theorem begin_post_R (st st' : state.KernelState) (bg : background.BackgroundTheory)
    (a a' : AbsState) (hR : R st bg a)
    (hpending : ∀ I, optRel pendingRel (a'.pending I) (pendingC st' I))
    (hchallenges : ∀ I, optRel challengeRel (a'.challenges I) (challengeC st' I))
    (hconsumed : ∀ I, a'.consumed_ids I ↔ vsMem st'.consumed_ids I)
    (hndPending : vmNodupKeys st'.pending) (hndChallenges : vmNodupKeys st'.challenges)
    (hactive : st'.agent_active = st.agent_active) (hparent : st'.agent_parent = st.agent_parent)
    (hcap : st'.agent_cap = st.agent_cap) (htaint : st'.taint_levels = st.taint_levels)
    (hinteg : st'.integ_levels = st.integ_levels) (htool : st'.tool_registered = st.tool_registered)
    (hatt : st'.consumed_attestations = st.consumed_attestations)
    (hcross : st'.consumed_crossings = st.consumed_crossings)
    (hgrants : st'.crossing_grants = st.crossing_grants)
    (hroot : a'.root_agent = a.root_agent) (hmode : a'.mode = a.mode)
    (hactiveA : a'.agent_active = a.agent_active) (hparentA : a'.agent_parent = a.agent_parent)
    (hcapA : a'.agent_cap = a.agent_cap) (htaintA : a'.taint_levels = a.taint_levels)
    (hintegA : a'.integ_levels = a.integ_levels) (htoolA : a'.tool_registered = a.tool_registered)
    (hattA : a'.consumed_attestations = a.consumed_attestations)
    (hcrossA : a'.consumed_crossings = a.consumed_crossings)
    (hgrantsA : a'.crossing_grants = a.crossing_grants)
    (hceilA : a'.egress_allow_ceiling = a.egress_allow_ceiling)
    (hceilI : a'.egress_inspect_ceiling = a.egress_inspect_ceiling) :
    R st' bg a' := by
  refine
    { root := hroot.trans hR.root, mode := hmode.trans hR.mode
      active := ?_, tool_reg := ?_, parent := ?_, cap := ?_, taint := ?_, integ := ?_
      pending := hpending, challenges := hchallenges, grants := ?_
      consumedIds := hconsumed, consumedAtt := ?_, consumedCross := ?_
      flowAllows := ?_, flowInspects := ?_
      ndParent := ?_, ndCap := ?_, ndTaint := ?_, ndInteg := ?_
      ndPending := hndPending, ndChallenges := hndChallenges, ndGrants := ?_ }
  · intro x; rw [hactiveA, hactive]; exact hR.active x
  · intro t; rw [htoolA, htool]; exact hR.tool_reg t
  · intro C P; rw [hparentA, hparent]; exact hR.parent C P
  · intro A C; rw [hcapA, hcap]; exact hR.cap A C
  · intro A L; rw [htaintA, htaint]; exact hR.taint A L
  · intro A L; rw [hintegA, hinteg]; exact hR.integ A L
  · intro A D
    rw [hgrantsA]
    unfold crossingGrantC
    rw [hgrants]
    exact hR.grants A D
  · intro X; rw [hattA, hatt]; exact hR.consumedAtt X
  · intro X; rw [hcrossA, hcross]; exact hR.consumedCross X
  · intro L E
    simp only [Tzimtzum.St.flow_allows]
    rw [hceilA]
    exact hR.flowAllows L E
  · intro L E
    simp only [Tzimtzum.St.flow_inspects]
    rw [hceilI]
    exact hR.flowInspects L E
  · rw [hparent]; exact hR.ndParent
  · rw [hcap]; exact hR.ndCap
  · rw [htaint]; exact hR.ndTaint
  · rw [hinteg]; exact hR.ndInteg
  · rw [hgrants]; exact hR.ndGrants

/-- Shared post transport for the three branches that insert a pending record. -/
theorem beginPendingPostR (st st' : state.KernelState) (bg : background.BackgroundTheory)
    (a a' : AbsState) (hR : R st bg a) (inv : types.InvocationId)
    (aj : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.AttestationId types.PolicyDigest)
    (cj : types.PendingInvocation) (hrel : pendingRel aj cj)
    (hpendA : ∀ I, a'.pending I = if I = inv then some aj else a.pending I)
    (hchalA : a'.challenges = a.challenges)
    (hconsA : ∀ I, a'.consumed_ids I ↔ a.consumed_ids I ∨ I = inv)
    (hframes : a'.root_agent = a.root_agent ∧ a'.mode = a.mode ∧
      a'.agent_active = a.agent_active ∧ a'.agent_parent = a.agent_parent ∧
      a'.agent_cap = a.agent_cap ∧ a'.taint_levels = a.taint_levels ∧
      a'.integ_levels = a.integ_levels ∧ a'.tool_registered = a.tool_registered ∧
      a'.consumed_attestations = a.consumed_attestations ∧
      a'.consumed_crossings = a.consumed_crossings ∧
      a'.crossing_grants = a.crossing_grants ∧
      a'.egress_allow_ceiling = a.egress_allow_ceiling ∧
      a'.egress_inspect_ceiling = a.egress_inspect_ceiling)
    (hcapP : st.pending.entries.val.length < Usize.max)
    (hcapIds : st.consumed_ids.items.val.length < Usize.max)
    (ev0 : event.KernelAction) (ev : event.KernelAction)
    (hok : (do
      let vm ← collections.VecMap.insert types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId
        types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj
      let vs ← collections.VecSet.insert types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId st.consumed_ids inv
      ok (.Ok ({ st with pending := vm, consumed_ids := vs }, ev0))) =
      (.ok (.Ok (st', ev)) : Result (core.result.Result
        (state.KernelState × event.KernelAction) error.KernelError))) :
    R st' bg a' := by
  obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj hcapP)
  obtain ⟨vmN, hvmNEq, hvmN⟩ := spec_imp_exists
    (vecMapInsert_nodup types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj hcapP)
  have hvmN' : vmN = vm := Result.ok.inj (hvmNEq.symm.trans hvmEq)
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vs, hvsEq, hvs, _⟩ := spec_imp_exists
    (vecSetInsertNodup_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      st.consumed_ids inv (fun _ => hcapIds))
  rw [hvsEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _⟩ := hok
  subst st'
  obtain ⟨hrootA, hmodeA, hactiveA, hparentA, hcapA, htaintA, hintegA, htoolA,
    hattA, hcrossA, hgrantsA, hceilA, hceilI⟩ := hframes
  apply begin_post_R st { st with pending := vm, consumed_ids := vs } bg a a' hR
  · intro I
    rw [hpendA I]
    unfold pendingC
    exact pending_clause_insert st bg a hR inv aj cj hrel vm hvm I
  · intro I
    rw [hchalA]
    exact hR.challenges I
  · intro I
    rw [hconsA I, hvs I, ← hR.consumedIds I]
  · exact hvmN' ▸ hvmN hR.ndPending
  · exact hR.ndChallenges
  all_goals first | rfl | assumption

/-- Shared post transport for the enforce inspection branch. -/
theorem beginChallengePostR (st st' : state.KernelState) (bg : background.BackgroundTheory)
    (a a' : AbsState) (hR : R st bg a) (inv : types.InvocationId)
    (ac : Tzimtzum.ChallengeScope types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.ChallengeId types.PolicyDigest types.ContentHash)
    (cc : types.ChallengeScope) (hrel : challengeRel ac cc)
    (hpendA : a'.pending = a.pending)
    (hchalA : ∀ I, a'.challenges I = if I = inv then some ac else a.challenges I)
    (hconsA : ∀ I, a'.consumed_ids I ↔ a.consumed_ids I ∨ I = inv)
    (hframes : a'.root_agent = a.root_agent ∧ a'.mode = a.mode ∧
      a'.agent_active = a.agent_active ∧ a'.agent_parent = a.agent_parent ∧
      a'.agent_cap = a.agent_cap ∧ a'.taint_levels = a.taint_levels ∧
      a'.integ_levels = a.integ_levels ∧ a'.tool_registered = a.tool_registered ∧
      a'.consumed_attestations = a.consumed_attestations ∧
      a'.consumed_crossings = a.consumed_crossings ∧
      a'.crossing_grants = a.crossing_grants ∧
      a'.egress_allow_ceiling = a.egress_allow_ceiling ∧
      a'.egress_inspect_ceiling = a.egress_inspect_ceiling)
    (hcapCh : st.challenges.entries.val.length < Usize.max)
    (hcapIds : st.consumed_ids.items.val.length < Usize.max)
    (ev0 ev : event.KernelAction)
    (hok : (do
      let vm ← collections.VecMap.insert types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId
        types.ChallengeScope.Insts.CoreCloneClone st.challenges inv cc
      let vs ← collections.VecSet.insert types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId st.consumed_ids inv
      ok (.Ok ({ st with challenges := vm, consumed_ids := vs }, ev0))) =
      (.ok (.Ok (st', ev)) : Result (core.result.Result
        (state.KernelState × event.KernelAction) error.KernelError))) :
    R st' bg a' := by
  obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ChallengeScope.Insts.CoreCloneClone st.challenges inv cc hcapCh)
  obtain ⟨vmN, hvmNEq, hvmN⟩ := spec_imp_exists
    (vecMapInsert_nodup types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ChallengeScope.Insts.CoreCloneClone st.challenges inv cc hcapCh)
  have hvmN' : vmN = vm := Result.ok.inj (hvmNEq.symm.trans hvmEq)
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vs, hvsEq, hvs, _⟩ := spec_imp_exists
    (vecSetInsertNodup_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      st.consumed_ids inv (fun _ => hcapIds))
  rw [hvsEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _⟩ := hok
  subst st'
  obtain ⟨hrootA, hmodeA, hactiveA, hparentA, hcapA, htaintA, hintegA, htoolA,
    hattA, hcrossA, hgrantsA, hceilA, hceilI⟩ := hframes
  apply begin_post_R st { st with challenges := vm, consumed_ids := vs } bg a a' hR
  · intro I
    rw [hpendA]
    exact hR.pending I
  · intro I
    rw [hchalA I]
    unfold challengeC
    exact challenge_clause_insert st bg a hR inv ac cc hrel vm hvm I
  · intro I
    rw [hconsA I, hvs I, ← hR.consumedIds I]
  · exact hR.ndPending
  · exact hvmN' ▸ hvmN hR.ndChallenges
  all_goals first | rfl | assumption

/-! ## Main preservation -/

theorem begin_invocation_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (agent : types.AgentId) (inv : types.InvocationId) (chal : types.ChallengeId)
    (snap : types.ActionPolicySnapshot)
    (snapA : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
      types.EgressKind types.PolicyDigest) (hsnap : snapshotRel snapA snap)
    (egr : collections.VecSet types.EgressKind) (egrA : types.EgressKind → Prop)
    (hEg : EgressAgree egr egrA) (ah : types.ContentHash)
    (authorized : Bool) (authorizedA : Prop) (hAu : AuAgree authorized authorizedA)
    (hR : R st bg a)
    (hcapT : vmSetLen st.taint_levels agent + st.pending.entries.val.length ≤ Usize.max)
    (hcapI : vmSetLen st.integ_levels agent + st.pending.entries.val.length ≤ Usize.max)
    (hcapP : st.pending.entries.val.length < Usize.max)
    (hcapCh : st.challenges.entries.val.length < Usize.max)
    (hcapIds : st.consumed_ids.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.begin_invocation st bg agent inv chal snap egr ah authorized =
      .ok (.Ok (st', ev))) :
    ∃ (v : Tzimtzum.Verdict) (a' : AbsState),
      (Tzimtzum.begin_invocation agent inv chal snapA egrA ah authorizedA v).guard a ∧
      (Tzimtzum.begin_invocation agent inv chal snapA egrA ah authorizedA v).next a a' ∧
      R st' bg a' := by
  simp only [transitions.begin_invocation] at hok
  obtain ⟨bactive, hactiveEq, hactive⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hactiveEq] at hok
  simp only [bind_tc_ok] at hok
  have hactiveT : bactive = true := by
    cases hb : bactive with
    | true => rfl
    | false => simp only [hb, Bool.false_eq_true, reduceIte] at hok; simp at hok
  simp only [hactiveT, reduceIte, background.BackgroundTheory.impl.root_agent,
    agentId_eq_spec, bind_tc_ok] at hok
  have hrootNe : agent ≠ bg.root_agent := by
    intro heq
    have hb : decide (agent = bg.root_agent) = true := by simp [heq]
    simp only [hb, reduceIte] at hok
    simp at hok
  simp only [hrootNe, decide_false, Bool.false_eq_true, reduceIte] at hok
  obtain ⟨btool, htoolEq, htool⟩ := spec_imp_exists
    (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered snap.tool)
  rw [htoolEq] at hok
  simp only [bind_tc_ok] at hok
  have htoolT : btool = true := by
    cases hb : btool with
    | true => rfl
    | false => simp only [hb, Bool.false_eq_true, reduceIte] at hok; simp at hok
  simp only [htoolT, reduceIte, integLevel_le_spec, bind_tc_ok] at hok
  have hcoh : integLeC snap.integ_inspect snap.integ_floor = true := by
    cases hb : integLeC snap.integ_inspect snap.integ_floor with
    | true => rfl
    | false => simp only [hb, Bool.false_eq_true, reduceIte] at hok; simp at hok
  simp only [hcoh, reduceIte] at hok
  obtain ⟨bp, hbpEq, hbp⟩ := spec_imp_exists
    (containsKey_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.PendingInvocation.Insts.CoreCloneClone st.pending inv)
  rw [hbpEq] at hok
  simp only [bind_tc_ok] at hok
  have hbpF : bp = false := by
    cases hb : bp with
    | false => rfl
    | true => simp only [hb, reduceIte] at hok; simp at hok
  simp only [hbpF, Bool.false_eq_true, reduceIte] at hok
  obtain ⟨bid, hbidEq, hbid⟩ := spec_imp_exists
    (vecSetContains_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec st.consumed_ids inv)
  rw [hbidEq] at hok
  simp only [bind_tc_ok] at hok
  have hbidF : bid = false := by
    cases hb : bid with
    | false => rfl
    | true => simp only [hb, reduceIte] at hok; simp at hok
  simp only [hbidF, Bool.false_eq_true, reduceIte] at hok
  obtain ⟨bch, hbchEq, hbch⟩ := spec_imp_exists
    (containsKey_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ChallengeScope.Insts.CoreCloneClone st.challenges inv)
  rw [hbchEq] at hok
  simp only [bind_tc_ok] at hok
  have hbchF : bch = false := by
    cases hb : bch with
    | false => rfl
    | true => simp only [hb, reduceIte] at hok; simp at hok
  simp only [hbchF, Bool.false_eq_true, reduceIte] at hok
  obtain ⟨bn, hbnEq, hbn⟩ := spec_imp_exists (egressNarrows_spec egr snap.declared_egress)
  rw [hbnEq] at hok
  simp only [bind_tc_ok] at hok
  have hbnT : bn = true := by
    cases hb : bn with
    | true => rfl
    | false => simp only [hb, Bool.false_eq_true, reduceIte] at hok; simp at hok
  simp only [hbnT, reduceIte] at hok
  obtain ⟨bcov, hbcovEq, hbcov⟩ := spec_imp_exists
    (egressCovers_spec snap.declared_egress egr)
  rw [hbcovEq] at hok
  simp only [bind_tc_ok] at hok
  have hbcovT : bcov = true := by
    cases hb : bcov with
    | true => rfl
    | false => simp only [hb, Bool.false_eq_true, reduceIte] at hok; simp at hok
  simp only [hbcovT, reduceIte] at hok
  obtain ⟨bcap, hbcapEq, hbcap⟩ := spec_imp_exists (checkCapability_spec st agent snap)
  rw [hbcapEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨bclear, hbclearEq, hbclear⟩ := spec_imp_exists
    (checkClearance_spec st agent snap hR.ndPending hcapT)
  rw [hbclearEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨bfs, hbfsEq, hbfs⟩ := spec_imp_exists
    (checkFlow_spec st bg agent snap egr true hR.ndPending hcapT)
  rw [hbfsEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨bfa, hbfaEq, hbfa⟩ := spec_imp_exists
    (checkFlow_spec st bg agent snap egr false hR.ndPending hcapT)
  rw [hbfaEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨bis, hbisEq, hbis⟩ := spec_imp_exists
    (checkInteg_spec st agent snap true hR.ndPending hcapI)
  rw [hbisEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨bia, hbiaEq, hbia⟩ := spec_imp_exists
    (checkInteg_spec st agent snap false hR.ndPending hcapI)
  rw [hbiaEq] at hok
  simp only [bind_tc_ok] at hok
  have hCap : bcap = true ↔ Tzimtzum.checkCapability a agent snapA :=
    hbcap.trans (checkCapability_bridge st bg a hR agent snap snapA hsnap)
  have hClear : bclear = true ↔ Tzimtzum.checkClearance a agent snapA :=
    hbclear.trans (checkClearance_bridge st bg a hR agent snap snapA hsnap)
  have hFlowS : bfs = true ↔ Tzimtzum.checkFlowStrict a agent snapA egrA :=
    hbfs.trans (checkFlowStrict_bridge st bg a hR agent snap snapA hsnap egr egrA hEg)
  have hFlowA : bfa = true ↔ Tzimtzum.checkFlowAdmissible a agent snapA egrA :=
    hbfa.trans (checkFlowAdmissible_bridge st bg a hR agent snap snapA hsnap egr egrA hEg)
  have hIntegS : bis = true ↔ Tzimtzum.checkIntegStrict a agent snapA :=
    hbis.trans (checkIntegStrict_bridge st bg a hR agent snap snapA hsnap)
  have hIntegA : bia = true ↔ Tzimtzum.checkIntegAdmissible a agent snapA :=
    hbia.trans (checkIntegAdmissible_bridge st bg a hR agent snap snapA hsnap)
  unfold AuAgree at hAu
  have hAllow : Tzimtzum.beginAllow a agent snapA egrA authorizedA ↔
      bcap = true ∧ authorized = true ∧ bclear = true ∧ bfs = true ∧ bis = true := by
    rw [Tzimtzum.beginAllow_iff, hCap, hAu, hClear, hFlowS, hIntegS]
  have hAdm : Tzimtzum.beginAdmissible a agent snapA egrA authorizedA ↔
      bcap = true ∧ authorized = true ∧ bclear = true ∧ bfa = true ∧ bia = true := by
    rw [Tzimtzum.beginAdmissible_iff, hCap, hAu, hClear, hFlowA, hIntegA]
  have hguardBase :
      a.agent_active agent ∧ agent ≠ a.root_agent ∧ a.tool_registered snapA.tool ∧
      Tzimtzum.le_integ snapA.integ_inspect snapA.integ_floor ∧
      a.pending inv = none ∧ ¬a.consumed_ids inv ∧ a.challenges inv = none ∧
      (∀ E, egrA E → snapA.declared_egress E) ∧
      ((∃ E, snapA.declared_egress E) → ∃ E, egrA E) := by
    refine ⟨(hR.active agent).mpr (hactive.mp hactiveT), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hR.root]
      exact hrootNe
    · obtain ⟨htoolA, _⟩ := hsnap
      rw [htoolA]
      exact (hR.tool_reg snap.tool).mpr (htool.mp htoolT)
    · obtain ⟨_, _, _, hfloor, hinspect, _⟩ := hsnap
      rw [hinspect, hfloor, le_integ_integLeC_both]
      exact hcoh
    · have hnone : pendingC st inv = none := by
        unfold pendingC
        apply Option.map_eq_none_iff.mpr
        apply vmLastEntry_eq_none
        intro p hp hpI
        have : bp = true := hbp.mpr ⟨p, hp, hpI⟩
        rw [hbpF] at this
        contradiction
      have hh := hR.pending inv
      rw [hnone] at hh
      cases ha : a.pending inv <;> simp_all [optRel]
    · intro hc
      have ht := hbid.mpr ((hR.consumedIds inv).mp hc)
      rw [hbidF] at ht
      contradiction
    · have hnone : challengeC st inv = none := by
        unfold challengeC
        apply Option.map_eq_none_iff.mpr
        apply vmLastEntry_eq_none
        intro p hp hpI
        have : bch = true := hbch.mpr ⟨p, hp, hpI⟩
        rw [hbchF] at this
        contradiction
      have hh := hR.challenges inv
      rw [hnone] at hh
      cases ha : a.challenges inv <;> simp_all [optRel]
    · intro E hE
      obtain ⟨_, _, _, _, _, _, _, hdecl, _⟩ := hsnap
      exact (hdecl E).mpr (hbn.mp hbnT E ((hEg E).mpr hE))
    · intro hdeclA
      obtain ⟨E, hE⟩ := hdeclA
      obtain ⟨_, _, _, _, _, _, _, hdecl, _⟩ := hsnap
      have hdeclC : snap.declared_egress.items.val ≠ [] := by
        intro hn
        have : E ∈ snap.declared_egress.items.val := (hdecl E).mp hE
        rw [hn] at this
        contradiction
      have hegrC := hbcov.mp hbcovT hdeclC
      obtain ⟨E', hE'⟩ := List.exists_mem_of_ne_nil egr.items.val hegrC
      exact ⟨E', (hEg E').mp hE'⟩
  -- The remaining proof dispatches the concrete verdict/mode arms and transports their writes.
  clear hactiveEq htoolEq hbpEq hbidEq hbchEq hbnEq hbcovEq hbcapEq hbclearEq hbfsEq hbfaEq
    hbisEq hbiaEq
  obtain ⟨gactive, groot, gtool, gcoh, gpend, gids, gchal, gnarrow, gcover⟩ := hguardBase
  by_cases hallowB : bcap = true ∧ authorized = true ∧ bclear = true ∧ bfs = true ∧ bis = true
  · obtain ⟨hc, hau, hcl, hfs, his⟩ := hallowB
    let cj : types.PendingInvocation :=
      { agent := agent, policy := snap, egress := egr, admission := .Plain,
        disposition := .Permitted, authorized := authorized, quarantined := false }
    let aj : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
        types.EgressKind types.AttestationId types.PolicyDigest :=
      { agent := agent, policy := snapA, egress := egrA, admission := .plain,
        disposition := .permitted, authorized := authorizedA, quarantined := False }
    have hok' : (do
        let vm ← collections.VecMap.insert types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj
        let vs ← collections.VecSet.insert types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId st.consumed_ids inv
        ok (.Ok ({ st with pending := vm, consumed_ids := vs },
          event.KernelAction.BeginInvocation agent inv snap.tool types.Verdict.Allow authorized))) =
        (.ok (.Ok (st', ev)) : Result (core.result.Result
          (state.KernelState × event.KernelAction) error.KernelError)) := by
      cases hfa : bfa <;> cases hia : bia <;>
        simpa [hc, hau, hcl, hfs, his, hfa, hia, cj, toolId_clone_spec,
          invocationId_clone_spec, agentId_clone_spec,
          background.BackgroundTheory.impl.mode] using hok
    refine ⟨.allow, beginAbs a agent inv chal snapA egrA ah authorizedA .allow, ?_, ?_, ?_⟩
    · simp only [Tzimtzum.begin_invocation]
      exact ⟨gactive, groot, gtool, gcoh, gpend, gids, gchal, gnarrow, gcover,
        fun _ => hAllow.mpr ⟨hc, hau, hcl, hfs, his⟩, by simp, by simp, by simp⟩
    · simp [Tzimtzum.begin_invocation, beginAbs]
    · apply beginPendingPostR st st' bg a
        (beginAbs a agent inv chal snapA egrA ah authorizedA .allow) hR inv aj cj
        (ev0 := event.KernelAction.BeginInvocation agent inv snap.tool types.Verdict.Allow authorized)
        (ev := ev)
      · unfold aj cj
        exact pendingRel_new agent snap snapA hsnap egr egrA hEg authorized authorizedA hAu
          .Plain .plain (by simp [admissionRel]) .Permitted .permitted rfl
      · intro I; simp [beginAbs, aj]
      · simp [beginAbs]
      · intro I; simp [beginAbs]
      · simp [beginAbs]
      · exact hcapP
      · exact hcapIds
      · exact hok'
  · by_cases hadmB : bcap = true ∧ authorized = true ∧ bclear = true ∧ bfa = true ∧ bia = true
    · obtain ⟨hc, hau, hcl, hfa, hia⟩ := hadmB
      have hnotAllowA : ¬Tzimtzum.beginAllow a agent snapA egrA authorizedA := by
        rw [hAllow]
        exact hallowB
      have hAdmA : Tzimtzum.beginAdmissible a agent snapA egrA authorizedA := hAdm.mpr
        ⟨hc, hau, hcl, hfa, hia⟩
      have hstrictNot : ¬(bfs = true ∧ bis = true) := by
        rintro ⟨hfs, his⟩
        exact hallowB ⟨hc, hau, hcl, hfs, his⟩
      cases hm : bg.mode with
      | Enforce =>
        have hamode : a.mode = Tzimtzum.Mode.enforce := by rw [hR.mode, hm]; rfl
        let cc : types.ChallengeScope :=
          { challenge := chal, agent := agent, policy := snap, egress := egr,
            args_hash := ah, authorized := authorized }
        let ac : Tzimtzum.ChallengeScope types.AgentId types.ToolId capability.CapKind
            types.EgressKind types.ChallengeId types.PolicyDigest types.ContentHash :=
          { challenge := chal, agent := agent, policy := snapA, egress := egrA,
            args_hash := ah, authorized := authorizedA }
        have hok' : (do
            let vm ← collections.VecMap.insert types.InvocationId.Insts.CoreCloneClone
              types.InvocationId.Insts.CoreCmpPartialEqInvocationId
              types.ChallengeScope.Insts.CoreCloneClone st.challenges inv cc
            let vs ← collections.VecSet.insert types.InvocationId.Insts.CoreCloneClone
              types.InvocationId.Insts.CoreCmpPartialEqInvocationId st.consumed_ids inv
            ok (.Ok ({ st with challenges := vm, consumed_ids := vs },
              event.KernelAction.BeginInvocation agent inv snap.tool
                types.Verdict.InspectionRequired authorized))) =
            (.ok (.Ok (st', ev)) : Result (core.result.Result
              (state.KernelState × event.KernelAction) error.KernelError)) := by
          cases bfs <;> cases bis
          all_goals try exact (hstrictNot ⟨rfl, rfl⟩).elim
          all_goals simpa [hc, hau, hcl, hfa, hia, hm, cc, toolId_clone_spec,
            invocationId_clone_spec, agentId_clone_spec,
            background.BackgroundTheory.impl.mode] using hok
        refine ⟨.inspection_required,
          beginAbs a agent inv chal snapA egrA ah authorizedA .inspection_required, ?_, ?_, ?_⟩
        · simp only [Tzimtzum.begin_invocation]
          exact ⟨gactive, groot, gtool, gcoh, gpend, gids, gchal, gnarrow, gcover,
            by simp, fun _ => ⟨hAdmA, hnotAllowA⟩, by simp, by simp⟩
        · simp [Tzimtzum.begin_invocation, beginAbs, hamode]
        · apply beginChallengePostR st st' bg a
            (beginAbs a agent inv chal snapA egrA ah authorizedA .inspection_required)
            hR inv ac cc
            (ev0 := event.KernelAction.BeginInvocation agent inv snap.tool
              types.Verdict.InspectionRequired authorized) (ev := ev)
          · unfold ac cc
            exact challengeRel_new chal agent snap snapA hsnap egr egrA hEg ah
              authorized authorizedA hAu
          · funext I
            by_cases hI : I = inv
            · subst I; simp [beginAbs, hamode, gpend]
            · simp [beginAbs, hamode, hI]
          · intro I; simp [beginAbs, hamode, ac]
          · intro I; simp [beginAbs]
          · simp [beginAbs]
          · exact hcapCh
          · exact hcapIds
          · exact hok'
      | Monitor =>
        have hamode : a.mode = Tzimtzum.Mode.monitor := by rw [hR.mode, hm]; rfl
        let cj : types.PendingInvocation :=
          { agent := agent, policy := snap, egress := egr, admission := .Bypassed,
            disposition := .MonitorBypassed, authorized := authorized, quarantined := false }
        let aj : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
            types.EgressKind types.AttestationId types.PolicyDigest :=
          { agent := agent, policy := snapA, egress := egrA, admission := .bypassed,
            disposition := .monitor_bypassed, authorized := authorizedA, quarantined := False }
        have hok' : (do
            let vm ← collections.VecMap.insert types.InvocationId.Insts.CoreCloneClone
              types.InvocationId.Insts.CoreCmpPartialEqInvocationId
              types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj
            let vs ← collections.VecSet.insert types.InvocationId.Insts.CoreCloneClone
              types.InvocationId.Insts.CoreCmpPartialEqInvocationId st.consumed_ids inv
            ok (.Ok ({ st with pending := vm, consumed_ids := vs },
              event.KernelAction.BeginInvocation agent inv snap.tool
                types.Verdict.InspectionRequired authorized))) =
            (.ok (.Ok (st', ev)) : Result (core.result.Result
              (state.KernelState × event.KernelAction) error.KernelError)) := by
          cases bfs <;> cases bis
          all_goals try exact (hstrictNot ⟨rfl, rfl⟩).elim
          all_goals simpa [hc, hau, hcl, hfa, hia, hm, cj, toolId_clone_spec,
            invocationId_clone_spec, agentId_clone_spec,
            background.BackgroundTheory.impl.mode] using hok
        refine ⟨.inspection_required,
          beginAbs a agent inv chal snapA egrA ah authorizedA .inspection_required, ?_, ?_, ?_⟩
        · simp only [Tzimtzum.begin_invocation]
          exact ⟨gactive, groot, gtool, gcoh, gpend, gids, gchal, gnarrow, gcover,
            by simp, fun _ => ⟨hAdmA, hnotAllowA⟩, by simp, by simp⟩
        · simp [Tzimtzum.begin_invocation, beginAbs, hamode]
        · apply beginPendingPostR st st' bg a
            (beginAbs a agent inv chal snapA egrA ah authorizedA .inspection_required)
            hR inv aj cj
            (ev0 := event.KernelAction.BeginInvocation agent inv snap.tool
              types.Verdict.InspectionRequired authorized) (ev := ev)
          · unfold aj cj
            exact pendingRel_new agent snap snapA hsnap egr egrA hEg authorized authorizedA hAu
              .Bypassed .bypassed (by simp [admissionRel])
              .MonitorBypassed .monitor_bypassed rfl
          · intro I; simp [beginAbs, hamode, aj]
          · simp [beginAbs, hamode]
          · intro I; simp [beginAbs]
          · simp [beginAbs]
          · exact hcapP
          · exact hcapIds
          · exact hok'
    · have hnotAdmA : ¬Tzimtzum.beginAdmissible a agent snapA egrA authorizedA := by
        rw [hAdm]
        exact hadmB
      have hnotAllowA : ¬Tzimtzum.beginAllow a agent snapA egrA authorizedA :=
        fun ha => hnotAdmA (Tzimtzum.beginAllow_admissible a agent snapA egrA authorizedA ha)
      have hm : bg.mode = types.Mode.Monitor := by
        cases hmode : bg.mode with
        | Monitor => rfl
        | Enforce =>
          cases hbcapv : bcap <;> cases hauv : authorized <;> cases hclearv : bclear <;>
            cases hfsv : bfs <;> cases hisv : bis <;> cases hfav : bfa <;> cases hiav : bia <;>
            simp_all [hmode, toolId_clone_spec, invocationId_clone_spec, agentId_clone_spec,
              background.BackgroundTheory.impl.mode]
      have hamode : a.mode = Tzimtzum.Mode.monitor := by rw [hR.mode, hm]; rfl
      let cj : types.PendingInvocation :=
        { agent := agent, policy := snap, egress := egr, admission := .Bypassed,
          disposition := .MonitorBypassed, authorized := authorized, quarantined := false }
      let aj : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
          types.EgressKind types.AttestationId types.PolicyDigest :=
        { agent := agent, policy := snapA, egress := egrA, admission := .bypassed,
          disposition := .monitor_bypassed, authorized := authorizedA, quarantined := False }
      have hok' : (do
          let vm ← collections.VecMap.insert types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId
            types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj
          let vs ← collections.VecSet.insert types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId st.consumed_ids inv
          ok (.Ok ({ st with pending := vm, consumed_ids := vs },
            event.KernelAction.BeginInvocation agent inv snap.tool types.Verdict.Deny authorized))) =
          (.ok (.Ok (st', ev)) : Result (core.result.Result
            (state.KernelState × event.KernelAction) error.KernelError)) := by
        cases hbcapv : bcap <;> cases hauv : authorized <;> cases hclearv : bclear <;>
          cases hfsv : bfs <;> cases hisv : bis <;> cases hfav : bfa <;> cases hiav : bia <;>
          simp_all [hm, cj, toolId_clone_spec, invocationId_clone_spec, agentId_clone_spec,
            background.BackgroundTheory.impl.mode]
      refine ⟨.deny, beginAbs a agent inv chal snapA egrA ah authorizedA .deny, ?_, ?_, ?_⟩
      · simp only [Tzimtzum.begin_invocation]
        exact ⟨gactive, groot, gtool, gcoh, gpend, gids, gchal, gnarrow, gcover,
          by simp, by simp, fun _ => hnotAdmA, fun _ => hamode⟩
      · simp [Tzimtzum.begin_invocation, beginAbs, hamode]
      · apply beginPendingPostR st st' bg a
          (beginAbs a agent inv chal snapA egrA ah authorizedA .deny) hR inv aj cj
          (ev0 := event.KernelAction.BeginInvocation agent inv snap.tool types.Verdict.Deny authorized)
          (ev := ev)
        · unfold aj cj
          exact pendingRel_new agent snap snapA hsnap egr egrA hEg authorized authorizedA hAu
            .Bypassed .bypassed (by simp [admissionRel])
            .MonitorBypassed .monitor_bypassed rfl
        · intro I; simp [beginAbs, hamode, aj]
        · simp [beginAbs, hamode]
        · intro I; simp [beginAbs]
        · simp [beginAbs]
        · exact hcapP
        · exact hcapIds
        · exact hok'
