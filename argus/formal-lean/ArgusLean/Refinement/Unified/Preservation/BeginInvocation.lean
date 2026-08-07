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
set_option maxHeartbeats 1000000
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
