import ArgusLean.Refinement.Unified.Preservation.ClearAgent

/-! # Layer 1 — `ingest` preserves the unified `R` (V4)

`ingest a src pconf pinteg` admits an incoming `(pconf, pinteg)` label into agent `a`. The kernel
computes the disposition: if the three holds pass it is `permitted` (insert only); otherwise, in
`monitor` mode it is `monitor_bypassed` (insert + demote `a`'s live permits) and in `enforce` mode
it fails closed. The three holds (`ingest_conf_hold` / `ingest_clear_hold` / `ingest_integ_hold`)
are ∀-scans over `a`'s pending records; this module bridges them to the abstract
`ingestConfHold` / `ingestClearHold` / `ingestIntegHold`, threads the `insert_into` taint/integ
updates and the `demote_all_of` demotion, and assembles the transport. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

/-- Abstract-to-abstract confidentiality order: `le_conf` between two abstracted concrete levels is
    the kernel's rank compare. -/
theorem le_conf_confLeC_both (pc cc : types.ConfLevel) :
    Tzimtzum.le_conf (confA pc) (confA cc) ↔ confLeC pc cc = true := by
  rw [le_conf_confLeC]; simp

/-- Abstract-to-abstract integrity order. -/
theorem le_integ_integLeC_both (pi ci : types.IntegLevel) :
    Tzimtzum.le_integ (integA ci) (integA pi) ↔ integLeC ci pi = true := by
  rw [le_integ_integLeC]; simp

/-! ## `ingest_clear_hold` -/

theorem ingestClearHoldLoop_spec (s : state.KernelState) (a : types.AgentId)
    (pconf : types.ConfLevel) (hnd : (s.pending.entries.val.map Prod.fst).Nodup)
    (ok1 : Bool) (i0 : Usize) (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hstart : ok1 = true ↔ ∀ p ∈ s.pending.entries.val.take i0.val,
      p.2.agent = a → confLeC pconf p.2.policy.conf_clearance = true) :
    transitions.ingest_clear_hold_loop s a pconf ok1 i0 ⦃ b =>
      b = true ↔ ∀ p ∈ s.pending.entries.val,
        p.2.agent = a → confLeC pconf p.2.policy.conf_clearance = true ⦄ := by
  unfold transitions.ingest_clear_hold_loop
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ s.pending.entries.val.length ∧
      (p.1 = true ↔ ∀ q ∈ s.pending.entries.val.take p.2.val,
        q.2.agent = a → confLeC pconf q.2.policy.conf_clearance = true))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.ingest_clear_hold_loop.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]; simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]; exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, confLevel_le_spec, bind_tc_ok]
      have hget : s.pending.entries.val[i.val]? =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [List.getElem?_eq_getElem hlt]
      set p := (s.pending.entries.val[i.val]'hlt) with hpdef
      have htk : (∀ q ∈ s.pending.entries.val.take (i.val + 1),
            q.2.agent = a → confLeC pconf q.2.policy.conf_clearance = true) ↔
          ((∀ q ∈ s.pending.entries.val.take i.val,
            q.2.agent = a → confLeC pconf q.2.policy.conf_clearance = true)
            ∧ (p.2.agent = a → confLeC pconf p.2.policy.conf_clearance = true)) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hpdef]
        constructor
        · intro hh; exact ⟨fun q hq => hh q (Or.inl hq), hh p (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ q (hq | hq)
          · exact h1 q hq
          · subst hq; exact h2
      by_cases hag : p.2.agent = a
      · simp only [hag, decide_true, reduceIte]
        by_cases hcl : confLeC pconf p.2.policy.conf_clearance = true
        · simp only [hcl, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
          exact ⟨fun hh => ⟨hh, fun _ => hcl⟩, fun hh => hh.1⟩
        · simp only [hcl, Bool.false_eq_true, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, htk]
          constructor
          · intro hc; exact absurd hc (by simp)
          · rintro ⟨_, h2⟩; exact absurd (h2 hag) hcl
      · simp only [hag, decide_false, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        exact ⟨fun hh => ⟨hh, fun hc => absurd hc hag⟩, fun hh => hh.1⟩
    case isFalse h =>
      have heq' : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

theorem ingestClearHold_spec (s : state.KernelState) (a : types.AgentId) (pconf : types.ConfLevel)
    (hnd : (s.pending.entries.val.map Prod.fst).Nodup) :
    transitions.ingest_clear_hold s a pconf ⦃ b =>
      b = true ↔ ∀ p ∈ s.pending.entries.val,
        p.2.agent = a → confLeC pconf p.2.policy.conf_clearance = true ⦄ := by
  unfold transitions.ingest_clear_hold
  exact ingestClearHoldLoop_spec s a pconf hnd true 0#usize (by simp) (by simp)

/-! ## `vouched` -/

/-- Pure value of `PendingInvocation.vouched`: `true` iff the admission is `Inspected`. -/
def vouchedC (j : types.PendingInvocation) : Bool :=
  match j.admission with
  | .Inspected _ => true
  | _ => false

theorem vouched_eq (j : types.PendingInvocation) :
    types.PendingInvocation.vouched j = .ok (vouchedC j) := by
  unfold types.PendingInvocation.vouched vouchedC
  cases j.admission <;> rfl

/-! ## `ingest_integ_hold` -/

theorem ingestIntegHoldLoop_spec (s : state.KernelState) (a : types.AgentId)
    (pinteg : types.IntegLevel) (hnd : (s.pending.entries.val.map Prod.fst).Nodup)
    (ok1 : Bool) (i0 : Usize) (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hstart : ok1 = true ↔ ∀ p ∈ s.pending.entries.val.take i0.val, p.2.agent = a →
      (integLeC p.2.policy.integ_floor pinteg = true ∨
        (integLeC p.2.policy.integ_inspect pinteg = true ∧ vouchedC p.2 = true))) :
    transitions.ingest_integ_hold_loop s a pinteg ok1 i0 ⦃ b =>
      b = true ↔ ∀ p ∈ s.pending.entries.val, p.2.agent = a →
        (integLeC p.2.policy.integ_floor pinteg = true ∨
          (integLeC p.2.policy.integ_inspect pinteg = true ∧ vouchedC p.2 = true)) ⦄ := by
  unfold transitions.ingest_integ_hold_loop
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ s.pending.entries.val.length ∧
      (p.1 = true ↔ ∀ q ∈ s.pending.entries.val.take p.2.val, q.2.agent = a →
        (integLeC q.2.policy.integ_floor pinteg = true ∨
          (integLeC q.2.policy.integ_inspect pinteg = true ∧ vouchedC q.2 = true))))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.ingest_integ_hold_loop.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]; simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]; exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, integLevel_le_spec, vouched_eq, bind_tc_ok]
      set p := (s.pending.entries.val[i.val]'hlt) with hpdef
      have htk : (∀ q ∈ s.pending.entries.val.take (i.val + 1), q.2.agent = a →
            (integLeC q.2.policy.integ_floor pinteg = true ∨
              (integLeC q.2.policy.integ_inspect pinteg = true ∧ vouchedC q.2 = true))) ↔
          ((∀ q ∈ s.pending.entries.val.take i.val, q.2.agent = a →
            (integLeC q.2.policy.integ_floor pinteg = true ∨
              (integLeC q.2.policy.integ_inspect pinteg = true ∧ vouchedC q.2 = true)))
            ∧ (p.2.agent = a →
              (integLeC p.2.policy.integ_floor pinteg = true ∨
                (integLeC p.2.policy.integ_inspect pinteg = true ∧ vouchedC p.2 = true)))) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hpdef]
        constructor
        · intro hh; exact ⟨fun q hq => hh q (Or.inl hq), hh p (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ q (hq | hq)
          · exact h1 q hq
          · subst hq; exact h2
      by_cases hag : p.2.agent = a
      · simp only [hag, decide_true, reduceIte]
        by_cases ha : integLeC p.2.policy.integ_floor pinteg = true
        · simp only [ha, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
          exact ⟨fun hh => ⟨hh, fun _ => Or.inl ha⟩, fun hh => hh.1⟩
        · rw [Bool.not_eq_true] at ha
          simp only [ha, Bool.false_eq_true, reduceIte]
          by_cases hi : integLeC p.2.policy.integ_inspect pinteg = true
          · simp only [hi, reduceIte]
            by_cases hv : vouchedC p.2 = true
            · simp only [hv, reduceIte]
              step*
              refine ⟨by scalar_tac, ?_, by scalar_tac⟩
              rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
              exact ⟨fun hh => ⟨hh, fun _ => Or.inr ⟨hi, hv⟩⟩, fun hh => hh.1⟩
            · rw [Bool.not_eq_true] at hv
              simp only [hv, Bool.false_eq_true, reduceIte]
              step*
              refine ⟨by scalar_tac, ?_, by scalar_tac⟩
              rw [show i2.val = i.val + 1 from by scalar_tac, htk]
              constructor
              · intro hc; exact absurd hc (by simp)
              · rintro ⟨_, h2⟩; rcases h2 hag with hh | ⟨_, hh⟩
                · rw [ha] at hh; exact absurd hh (by simp)
                · rw [hv] at hh; exact absurd hh (by simp)
          · rw [Bool.not_eq_true] at hi
            simp only [hi, Bool.false_eq_true, reduceIte]
            step*
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            rw [show i2.val = i.val + 1 from by scalar_tac, htk]
            constructor
            · intro hc; exact absurd hc (by simp)
            · rintro ⟨_, h2⟩; rcases h2 hag with hh | ⟨hh, _⟩
              · rw [ha] at hh; exact absurd hh (by simp)
              · rw [hi] at hh; exact absurd hh (by simp)
      · simp only [hag, decide_false, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        exact ⟨fun hh => ⟨hh, fun hc => absurd hc hag⟩, fun hh => hh.1⟩
    case isFalse h =>
      have heq' : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

theorem ingestIntegHold_spec (s : state.KernelState) (a : types.AgentId)
    (pinteg : types.IntegLevel) (hnd : (s.pending.entries.val.map Prod.fst).Nodup) :
    transitions.ingest_integ_hold s a pinteg ⦃ b =>
      b = true ↔ ∀ p ∈ s.pending.entries.val, p.2.agent = a →
        (integLeC p.2.policy.integ_floor pinteg = true ∨
          (integLeC p.2.policy.integ_inspect pinteg = true ∧ vouchedC p.2 = true)) ⦄ := by
  unfold transitions.ingest_integ_hold
  exact ingestIntegHoldLoop_spec s a pinteg hnd true 0#usize (by simp) (by simp)

/-! ## `ingest_conf_hold` (nested: per pending record, per egress channel) -/

/-- Per-egress admissibility of `pconf` for a vouched-or-not pending record. -/
def egressCondC (bg : background.BackgroundTheory) (pconf : types.ConfLevel) (vouched : Bool)
    (E : types.EgressKind) : Prop :=
  ceilAdmitsC bg.allow_ceiling pconf E = true ∨
    (ceilAdmitsC bg.inspect_ceiling pconf E = true ∧ vouched = true)

theorem ingestConfInnerLoop_spec (bg : background.BackgroundTheory) (pconf : types.ConfLevel)
    (vs : collections.VecSet types.EgressKind) (ok1 vouched : Bool) (e0 : Usize)
    (he0 : e0.val ≤ vs.items.val.length)
    (hstart : ok1 = true ↔ okStart = true ∧
      ∀ E ∈ vs.items.val.take e0.val, egressCondC bg pconf vouched E) :
    transitions.ingest_conf_hold_loop0_loop0 bg pconf ok1 vs vouched e0 ⦃ b =>
      b = true ↔ okStart = true ∧ ∀ E ∈ vs.items.val, egressCondC bg pconf vouched E ⦄ := by
  unfold transitions.ingest_conf_hold_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => vs.items.val.length - p.2.2.val)
    (inv := fun p => p.2.1 = vouched ∧ p.2.2.val ≤ vs.items.val.length ∧
      (p.1 = true ↔ okStart = true ∧
        ∀ E ∈ vs.items.val.take p.2.2.val, egressCondC bg pconf vouched E))
  · rintro ⟨okc, vc, e⟩ ⟨hvc, hile, hinv⟩
    subst hvc
    simp only [transitions.ingest_conf_hold_loop0_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : e.val < vs.items.val.length := by scalar_tac
      step as ⟨eg, heg⟩
      obtain ⟨ba, hbaEq, hba⟩ := spec_imp_exists (flowAllows_spec bg pconf eg)
      obtain ⟨bi, hbiEq, hbi⟩ := spec_imp_exists (flowInspects_spec bg pconf eg)
      have htk : (∀ E ∈ vs.items.val.take (e.val + 1), egressCondC bg pconf vc E) ↔
          (∀ E ∈ vs.items.val.take e.val, egressCondC bg pconf vc E) ∧ egressCondC bg pconf vc eg := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← heg]
        constructor
        · intro hh; exact ⟨fun E hE => hh E (Or.inl hE), hh eg (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ E (hE | hE)
          · exact h1 E hE
          · subst hE; exact h2
      rw [hbaEq]; simp only [bind_tc_ok]
      by_cases hea : ceilAdmitsC bg.allow_ceiling pconf eg = true
      · have hba' : ba = true := hba.trans hea
        simp only [hba', reduceIte, bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show e1.val = e.val + 1 from by scalar_tac, htk, hinv]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2, Or.inl hea⟩
        · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
      · have hban : ba = false := by rw [hba]; simpa using hea
        simp only [hban, Bool.false_eq_true, reduceIte, bind_tc_ok]
        rw [hbiEq]; simp only [bind_tc_ok]
        by_cases hei : ceilAdmitsC bg.inspect_ceiling pconf eg = true
        · have hbi' : bi = true := hbi.trans hei
          simp only [hbi', reduceIte, bind_tc_ok]
          by_cases hv : vc = true
          · subst hv; simp only [reduceIte, bind_tc_ok]
            step*
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            rw [show e1.val = e.val + 1 from by scalar_tac, htk, hinv]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨h1, h2, Or.inr ⟨hei, rfl⟩⟩
            · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
          · have hvn : vc = false := by simpa using hv
            subst hvn; simp only [reduceCtorEq, reduceIte, bind_tc_ok]
            step*
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            rw [show e1.val = e.val + 1 from by scalar_tac, htk]
            constructor
            · intro hc; exact absurd hc (by decide)
            · rintro ⟨_, _, hcond⟩
              rcases hcond with hh | ⟨_, hh⟩
              · exact absurd hh hea
              · exact absurd hh (by decide)
        · have hbin : bi = false := by
            cases hbc : bi with
            | false => rfl
            | true => rw [hbc] at hbi; exact absurd hbi.symm hei
          rw [hbin]; simp only [reduceCtorEq, reduceIte, bind_tc_ok]
          step*
          refine ⟨by omega, ?_, by omega⟩
          rw [show e1.val = e.val + 1 from e1_post, htk]
          constructor
          · intro hc; exact absurd hc (by decide)
          · rintro ⟨_, _, hcond⟩
            rcases hcond with hh | ⟨hh, _⟩
            · exact absurd hh hea
            · exact absurd hh hei
    case isFalse h =>
      have heq' : e.val = vs.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨rfl, he0, by simpa using hstart⟩

/-- Per-pending confidentiality admissibility: every attested egress of `p` admits `pconf`. -/
def confRecordC (bg : background.BackgroundTheory) (pconf : types.ConfLevel)
    (p : types.InvocationId × types.PendingInvocation) : Prop :=
  ∀ E ∈ p.2.egress.items.val, egressCondC bg pconf (vouchedC p.2) E

theorem ingestConfHoldLoop_spec (s : state.KernelState) (bg : background.BackgroundTheory)
    (a : types.AgentId) (pconf : types.ConfLevel)
    (hnd : (s.pending.entries.val.map Prod.fst).Nodup)
    (ok1 : Bool) (i0 : Usize) (hi0 : i0.val ≤ s.pending.entries.val.length)
    (hstart : ok1 = true ↔ ∀ p ∈ s.pending.entries.val.take i0.val,
      p.2.agent = a → confRecordC bg pconf p) :
    transitions.ingest_conf_hold_loop0 s bg a pconf ok1 i0 ⦃ b =>
      b = true ↔ ∀ p ∈ s.pending.entries.val, p.2.agent = a → confRecordC bg pconf p ⦄ := by
  unfold transitions.ingest_conf_hold_loop0
  apply loop.spec_decr_nat
    (measure := fun p => s.pending.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ s.pending.entries.val.length ∧
      (p.1 = true ↔ ∀ q ∈ s.pending.entries.val.take p.2.val,
        q.2.agent = a → confRecordC bg pconf q))
  · rintro ⟨okc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.ingest_conf_hold_loop0.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < s.pending.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone s.pending i hlt)
      rw [hkEq]; simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec s.pending k)
      have hlast : vmLastEntry s.pending.entries.val k =
          some ((s.pending.entries.val[i.val]'hlt).1, (s.pending.entries.val[i.val]'hlt).2) := by
        rw [hk]; exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, vouched_eq, bind_tc_ok]
      set p := (s.pending.entries.val[i.val]'hlt) with hpdef
      have hget : s.pending.entries.val[i.val]? = some (p.1, p.2) := by
        rw [List.getElem?_eq_getElem hlt]
      have htk : (∀ q ∈ s.pending.entries.val.take (i.val + 1),
            q.2.agent = a → confRecordC bg pconf q) ↔
          ((∀ q ∈ s.pending.entries.val.take i.val, q.2.agent = a → confRecordC bg pconf q)
            ∧ (p.2.agent = a → confRecordC bg pconf p)) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hpdef]
        constructor
        · intro hh; exact ⟨fun q hq => hh q (Or.inl hq), hh p (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ q (hq | hq)
          · exact h1 q hq
          · subst hq; exact h2
      by_cases hag : p.2.agent = a
      · simp only [hag, decide_true, reduceIte]
        obtain ⟨ok2, hok2Eq, hok2⟩ := spec_imp_exists
          (ingestConfInnerLoop_spec (okStart := okc) bg pconf p.2.egress okc (vouchedC p.2)
            0#usize (by simp) (by simp))
        rw [hok2Eq]; simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hok2, hinv]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2 hag⟩
      · simp only [hag, decide_false, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        exact ⟨fun hh => ⟨hh, fun hc => absurd hc hag⟩, fun hh => hh.1⟩
    case isFalse h =>
      have heq' : i.val = s.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

theorem ingestConfHold_spec (s : state.KernelState) (bg : background.BackgroundTheory)
    (a : types.AgentId) (pconf : types.ConfLevel)
    (hnd : (s.pending.entries.val.map Prod.fst).Nodup) :
    transitions.ingest_conf_hold s bg a pconf ⦃ b =>
      b = true ↔ ∀ p ∈ s.pending.entries.val, p.2.agent = a → confRecordC bg pconf p ⦄ := by
  unfold transitions.ingest_conf_hold
  exact ingestConfHoldLoop_spec s bg a pconf hnd true 0#usize (by simp) (by simp)

/-! ## Bridges from concrete `∀`-over-entries hold results to abstract hold predicates -/

/-- `vouched` correspondence under `admissionRel`. -/
theorem vouchedC_bridge
    (J : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind types.EgressKind
      types.AttestationId types.PolicyDigest) (cj : types.PendingInvocation)
    (h : admissionRel J.admission cj.admission) :
    Tzimtzum.vouched J ↔ vouchedC cj = true := by
  unfold Tzimtzum.vouched vouchedC
  cases haa : J.admission <;> cases hca : cj.admission <;>
    simp_all [admissionRel]

/-- Bridge helper: an abstract pending record `some J` corresponds to a concrete last-match entry. -/
theorem abs_pending_to_entry (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (I : types.InvocationId)
    (J : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind types.EgressKind
      types.AttestationId types.PolicyDigest) (hJ : a.pending I = some J) :
    ∃ cj, (I, cj) ∈ st.pending.entries.val ∧ pendingRel J cj := by
  have hRp := hR.pending I; rw [hJ] at hRp
  cases hpc : pendingC st I with
  | none => rw [hpc] at hRp; simp only [optRel] at hRp
  | some cj =>
    rw [hpc] at hRp; simp only [optRel] at hRp
    have hlast : vmLastEntry st.pending.entries.val I = some (I, cj) := by
      unfold pendingC at hpc
      cases hL : vmLastEntry st.pending.entries.val I with
      | none => rw [hL] at hpc; simp at hpc
      | some q =>
        obtain ⟨qk, qv⟩ := q
        have hq1 : qk = I := vmLastEntry_fst _ _ _ hL
        rw [hL] at hpc; simp only [Option.map_some, Option.some_inj] at hpc
        rw [hq1, hpc]
    exact ⟨cj, (vmLastEntry_nodup _ _ _ hR.ndPending).mp hlast, hRp⟩

/-- Bridge helper: a concrete last-match entry corresponds to an abstract `some J`. -/
theorem entry_to_abs_pending (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (p : types.InvocationId × types.PendingInvocation)
    (hp : p ∈ st.pending.entries.val) :
    ∃ J, a.pending p.1 = some J ∧ pendingRel J p.2 := by
  have hlast : vmLastEntry st.pending.entries.val p.1 = some (p.1, p.2) :=
    (vmLastEntry_nodup _ _ _ hR.ndPending).mpr (by simpa using hp)
  have hpc : pendingC st p.1 = some p.2 := by unfold pendingC; rw [hlast]; rfl
  have hRp := hR.pending p.1; rw [hpc] at hRp
  cases haI : a.pending p.1 with
  | none => rw [haI] at hRp; simp only [optRel] at hRp
  | some J => rw [haI] at hRp; simp only [optRel] at hRp; exact ⟨J, rfl, hRp⟩

theorem ingestClearHold_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId) (pconf : types.ConfLevel) :
    (∀ p ∈ st.pending.entries.val, p.2.agent = agent →
        confLeC pconf p.2.policy.conf_clearance = true) ↔
      Tzimtzum.ingestClearHold a agent (confA pconf) := by
  constructor
  · intro hconc I J hpJ hJa
    obtain ⟨cj, hmem, hpr⟩ := abs_pending_to_entry st bg a hR I J hpJ
    obtain ⟨hag, hsnap, _⟩ := hpr
    obtain ⟨_, _, hclear, _⟩ := hsnap
    have hcja : cj.agent = agent := by rw [← hag]; exact hJa
    have := hconc (I, cj) hmem hcja
    show Tzimtzum.le_conf (confA pconf) J.policy.conf_clearance
    rw [hclear, le_conf_confLeC_both]; exact this
  · intro habs p hp hpa
    obtain ⟨J, haI, hpr⟩ := entry_to_abs_pending st bg a hR p hp
    obtain ⟨hag, hsnap, _⟩ := hpr
    obtain ⟨_, _, hclear, _⟩ := hsnap
    have hJa : J.agent = agent := by rw [hag]; exact hpa
    have := habs p.1 J haI hJa
    show confLeC pconf p.2.policy.conf_clearance = true
    rw [← le_conf_confLeC_both, ← hclear]; exact this

theorem ingestIntegHold_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId) (pinteg : types.IntegLevel) :
    (∀ p ∈ st.pending.entries.val, p.2.agent = agent →
        (integLeC p.2.policy.integ_floor pinteg = true ∨
          (integLeC p.2.policy.integ_inspect pinteg = true ∧ vouchedC p.2 = true))) ↔
      Tzimtzum.ingestIntegHold a agent (integA pinteg) := by
  constructor
  · intro hconc I J hpJ hJa
    obtain ⟨cj, hmem, hpr⟩ := abs_pending_to_entry st bg a hR I J hpJ
    obtain ⟨hag, hsnap, _, hadm, _⟩ := hpr
    obtain ⟨_, _, _, hfloor, hinspect, _⟩ := hsnap
    have hcja : cj.agent = agent := by rw [← hag]; exact hJa
    rcases hconc (I, cj) hmem hcja with hh | ⟨h1, h2⟩
    · left
      show Tzimtzum.le_integ J.policy.integ_floor (integA pinteg)
      rw [hfloor, le_integ_integLeC_both]; exact hh
    · right
      refine ⟨?_, (vouchedC_bridge J cj hadm).mpr h2⟩
      show Tzimtzum.le_integ J.policy.integ_inspect (integA pinteg)
      rw [hinspect, le_integ_integLeC_both]; exact h1
  · intro habs p hp hpa
    obtain ⟨J, haI, hpr⟩ := entry_to_abs_pending st bg a hR p hp
    obtain ⟨hag, hsnap, _, hadm, _⟩ := hpr
    obtain ⟨_, _, _, hfloor, hinspect, _⟩ := hsnap
    have hJa : J.agent = agent := by rw [hag]; exact hpa
    rcases habs p.1 J haI hJa with hh | ⟨h1, h2⟩
    · left; rw [← le_integ_integLeC_both, ← hfloor]; exact hh
    · right
      refine ⟨?_, (vouchedC_bridge J p.2 hadm).mp h2⟩
      rw [← le_integ_integLeC_both, ← hinspect]; exact h1

theorem ingestConfHold_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId) (pconf : types.ConfLevel) :
    (∀ p ∈ st.pending.entries.val, p.2.agent = agent → confRecordC bg pconf p) ↔
      Tzimtzum.ingestConfHold a agent (confA pconf) := by
  have hfa : ∀ E, a.flow_allows (confA pconf) E ↔ ceilAdmitsC bg.allow_ceiling pconf E = true := by
    intro E; rw [hR.flowAllows]; simp
  have hfi : ∀ E, a.flow_inspects (confA pconf) E ↔ ceilAdmitsC bg.inspect_ceiling pconf E = true := by
    intro E; rw [hR.flowInspects]; simp
  constructor
  · intro hconc I J E hpJ hJa hJE
    obtain ⟨cj, hmem, hpr⟩ := abs_pending_to_entry st bg a hR I J hpJ
    obtain ⟨hag, _, hegress, hadm, _⟩ := hpr
    have hcja : cj.agent = agent := by rw [← hag]; exact hJa
    have hcjE : E ∈ cj.egress.items.val := (hegress E).mp hJE
    rcases hconc (I, cj) hmem hcja E hcjE with hh | ⟨h1, h2⟩
    · exact Or.inl ((hfa E).mpr hh)
    · exact Or.inr ⟨(hfi E).mpr h1, (vouchedC_bridge J cj hadm).mpr h2⟩
  · intro habs p hp hpa E hpE
    obtain ⟨J, haI, hpr⟩ := entry_to_abs_pending st bg a hR p hp
    obtain ⟨hag, _, hegress, hadm, _⟩ := hpr
    have hJa : J.agent = agent := by rw [hag]; exact hpa
    have hJE : J.egress E := (hegress E).mpr hpE
    rcases habs p.1 J E haI hJa hJE with hh | ⟨h1, h2⟩
    · exact Or.inl ((hfa E).mp hh)
    · exact Or.inr ⟨(hfi E).mp h1, (vouchedC_bridge J p.2 hadm).mp h2⟩

/-! ## `demote_all_of` -/

/-- Re-key an entry, demoting the removed agent's records to `MonitorBypassed`. -/
def demoteEntry (agent : types.AgentId) (p : types.InvocationId × types.PendingInvocation) :
    types.InvocationId × types.PendingInvocation :=
  (p.1, { p.2 with disposition :=
    if p.2.agent = agent then types.Disposition.MonitorBypassed else p.2.disposition })

theorem demoteAllLoop_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.pending.entries.val.map Prod.fst).Nodup)
    (rebuilt : collections.VecMap types.InvocationId types.PendingInvocation) (i0 : Usize)
    (hi0 : i0.val ≤ self.pending.entries.val.length)
    (hr0 : rebuilt.entries.val = (self.pending.entries.val.take i0.val).map (demoteEntry agent)) :
    state.KernelState.demote_all_of_loop self agent rebuilt i0 ⦃ out =>
      ∃ r1, out = (self.agent_active, self.agent_parent, self.agent_cap, self.taint_levels,
        self.integ_levels, self.challenges, self.consumed_ids, self.consumed_attestations,
        self.consumed_crossings, self.crossing_grants, self.tool_registered, r1) ∧
        r1.entries.val = self.pending.entries.val.map (demoteEntry agent) ⦄ := by
  unfold state.KernelState.demote_all_of_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.pending.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.pending.entries.val.length ∧
      p.1.entries.val = (self.pending.entries.val.take p.2.val).map (demoteEntry agent))
  · rintro ⟨reb, i⟩ ⟨hile, hreb⟩
    simp only [state.KernelState.demote_all_of_loop.body, collections.VecMap.len,
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
      simp only [Option.map_some, agentId_eq_spec, bind_tc_ok]
      set p := (self.pending.entries.val[i.val]'hlt) with hpdef
      rw [show (if decide (p.2.agent = agent) = true then ok types.Disposition.MonitorBypassed
            else ok p.2.disposition)
          = ok (if p.2.agent = agent then types.Disposition.MonitorBypassed else p.2.disposition)
          from by by_cases hag : p.2.agent = agent <;> simp [hag]]
      simp only [bind_tc_ok]
      have hget : self.pending.entries.val[i.val]? = some (p.1, p.2) := by
        rw [List.getElem?_eq_getElem hlt]
      have hcapk : reb.entries.val.length < Usize.max := by
        have hle : reb.entries.val.length ≤ i.val := by
          rw [hreb, List.length_map, List.length_take]; exact Nat.min_le_left _ _
        scalar_tac
      have hfresh : ∀ q ∈ reb.entries.val, q.1 ≠ k := by
        have hni := fst_getElem_not_mem_map_take self.pending.entries.val i.val hlt hnd
        rw [hreb]; intro q hq hqc
        obtain ⟨q0, hq0, hq0e⟩ := List.mem_map.mp hq
        have hq01 : q0.1 = k := by
          have hqe : (demoteEntry agent q0).1 = q0.1 := rfl
          rw [hq0e] at hqe; rw [← hqe]; exact hqc
        have hmem : q0.1 ∈ (self.pending.entries.val.take i.val).map Prod.fst :=
          List.mem_map.mpr ⟨q0, hq0, rfl⟩
        rw [hq01, hk] at hmem
        exact hni hmem
      have hval : ({ p.2 with disposition :=
            if p.2.agent = agent then types.Disposition.MonitorBypassed else p.2.disposition }) =
          (demoteEntry agent p).2 := rfl
      obtain ⟨r1, hr1Eq, hr1⟩ := spec_imp_exists
        (vecMapInsert_append_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone reb k
          { p.2 with disposition :=
            if p.2.agent = agent then types.Disposition.MonitorBypassed else p.2.disposition }
          hcapk hfresh)
      rw [hr1Eq]; simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hr1, hreb, show i2.val = i.val + 1 from by scalar_tac, List.take_add_one, hget]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, demoteEntry, hk]
    case isFalse h =>
      have heq' : i.val = self.pending.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hreb ⊢
      exact ⟨reb, rfl, hreb⟩
  · exact ⟨hi0, by simpa using hr0⟩

theorem demoteAllOf_spec (self : state.KernelState) (agent : types.AgentId)
    (hnd : (self.pending.entries.val.map Prod.fst).Nodup) :
    state.KernelState.demote_all_of self agent ⦃ st' =>
      st'.agent_active = self.agent_active ∧ st'.agent_parent = self.agent_parent ∧
      st'.agent_cap = self.agent_cap ∧ st'.taint_levels = self.taint_levels ∧
      st'.integ_levels = self.integ_levels ∧ st'.challenges = self.challenges ∧
      st'.consumed_ids = self.consumed_ids ∧
      st'.consumed_attestations = self.consumed_attestations ∧
      st'.consumed_crossings = self.consumed_crossings ∧
      st'.crossing_grants = self.crossing_grants ∧ st'.tool_registered = self.tool_registered ∧
      st'.pending.entries.val = self.pending.entries.val.map (demoteEntry agent) ⦄ := by
  unfold state.KernelState.demote_all_of
  simp only [collections.VecMap.new, bind_tc_ok]
  obtain ⟨out, houtEq, r1, houtVal, hrVal⟩ := spec_imp_exists
    (demoteAllLoop_spec self agent hnd { entries := alloc.vec.Vec.new _ } 0#usize (by scalar_tac)
      (by simp))
  rw [houtEq]; simp only [bind_tc_ok, houtVal, spec_ok]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hrVal⟩

/-! ## Source-domination loops -/

theorem ingestLoop0_spec (pconf : types.ConfLevel) (src_taint : collections.VecSet types.ConfLevel)
    (dom : Bool) (i0 : Usize) (hi0 : i0.val ≤ src_taint.items.val.length)
    (hstart : dom = true ↔ st0 = true ∧ ∀ l ∈ src_taint.items.val.take i0.val, confLeC l pconf = true) :
    transitions.ingest_loop0 pconf dom src_taint i0 ⦃ b =>
      b = true ↔ st0 = true ∧ ∀ l ∈ src_taint.items.val, confLeC l pconf = true ⦄ := by
  unfold transitions.ingest_loop0
  apply loop.spec_decr_nat
    (measure := fun p => src_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ src_taint.items.val.length ∧
      (p.1 = true ↔ st0 = true ∧ ∀ l ∈ src_taint.items.val.take p.2.val, confLeC l pconf = true))
  · rintro ⟨dc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.ingest_loop0.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < src_taint.items.val.length := by scalar_tac
      step as ⟨l, hl⟩
      simp only [confLevel_le_spec, bind_tc_ok]
      have htk : (∀ x ∈ src_taint.items.val.take (i.val + 1), confLeC x pconf = true) ↔
          (∀ x ∈ src_taint.items.val.take i.val, confLeC x pconf = true) ∧ confLeC l pconf = true := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hl]
        constructor
        · intro hh; exact ⟨fun x hx => hh x (Or.inl hx), hh l (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | hx)
          · exact h1 x hx
          · subst hx; exact h2
      by_cases hcl : confLeC l pconf = true
      · simp only [hcl, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        exact ⟨fun hh => ⟨hh.1, hh.2, hcl⟩, fun hh => ⟨hh.1, hh.2.1⟩⟩
      · rw [Bool.not_eq_true] at hcl
        simp only [hcl, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk]
        constructor
        · intro hc; exact absurd hc (by decide)
        · rintro ⟨_, _, hh⟩; rw [hcl] at hh; exact absurd hh (by decide)
    case isFalse h =>
      have heq' : i.val = src_taint.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

theorem ingestLoop1_spec (pinteg : types.IntegLevel)
    (src_integ : collections.VecSet types.IntegLevel) (dom : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ src_integ.items.val.length)
    (hstart : dom = true ↔ st0 = true ∧
      ∀ l ∈ src_integ.items.val.take i0.val, integLeC pinteg l = true) :
    transitions.ingest_loop1 pinteg dom src_integ i0 ⦃ b =>
      b = true ↔ st0 = true ∧ ∀ l ∈ src_integ.items.val, integLeC pinteg l = true ⦄ := by
  unfold transitions.ingest_loop1
  apply loop.spec_decr_nat
    (measure := fun p => src_integ.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ src_integ.items.val.length ∧
      (p.1 = true ↔ st0 = true ∧ ∀ l ∈ src_integ.items.val.take p.2.val, integLeC pinteg l = true))
  · rintro ⟨dc, i⟩ ⟨hile, hinv⟩
    simp only [transitions.ingest_loop1.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < src_integ.items.val.length := by scalar_tac
      step as ⟨l, hl⟩
      simp only [integLevel_le_spec, bind_tc_ok]
      have htk : (∀ x ∈ src_integ.items.val.take (i.val + 1), integLeC pinteg x = true) ↔
          (∀ x ∈ src_integ.items.val.take i.val, integLeC pinteg x = true) ∧ integLeC pinteg l = true := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hl]
        constructor
        · intro hh; exact ⟨fun x hx => hh x (Or.inl hx), hh l (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ x (hx | hx)
          · exact h1 x hx
          · subst hx; exact h2
      by_cases hil : integLeC pinteg l = true
      · simp only [hil, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        exact ⟨fun hh => ⟨hh.1, hh.2, hil⟩, fun hh => ⟨hh.1, hh.2.1⟩⟩
      · rw [Bool.not_eq_true] at hil
        simp only [hil, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk]
        constructor
        · intro hc; exact absurd hc (by decide)
        · rintro ⟨_, _, hh⟩; rw [hil] at hh; exact absurd hh (by decide)
    case isFalse h =>
      have heq' : i.val = src_integ.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

/-! ## R-clause helpers for the taint/integ insert and pending demotion -/

theorem ingest_taint_clause (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (agent : types.AgentId) (pconf : types.ConfLevel)
    (vm : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (hvm : ∀ k v, vmsMemLast vm k v ↔ vmsMemLast st.taint_levels k v ∨ (k = agent ∧ v = pconf))
    (A : types.AgentId) (L : Tzimtzum.ConfLevel) :
    (a.taint_levels A L ∨ (A = agent ∧ L = confA pconf)) ↔ vmsMemLast vm A (confC L) := by
  rw [hvm, ← hR.taint A L]
  constructor
  · rintro (h | ⟨hA, hL⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hA, by rw [hL, confC_confA]⟩
  · rintro (h | ⟨hA, hv⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hA, ?_⟩; have := congrArg confA hv; rwa [confA_confC] at this

theorem ingest_integ_clause (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (agent : types.AgentId) (pinteg : types.IntegLevel)
    (vm : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (hvm : ∀ k v, vmsMemLast vm k v ↔ vmsMemLast st.integ_levels k v ∨ (k = agent ∧ v = pinteg))
    (A : types.AgentId) (L : Tzimtzum.IntegLevel) :
    (a.integ_levels A L ∨ (A = agent ∧ L = integA pinteg)) ↔ vmsMemLast vm A (integC L) := by
  rw [hvm, ← hR.integ A L]
  constructor
  · rintro (h | ⟨hA, hL⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hA, by rw [hL, integC_integA]⟩
  · rintro (h | ⟨hA, hv⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hA, ?_⟩; have := congrArg integA hv; rwa [integA_integC] at this

/-! ## Helper: last-match under a key-preserving map (for the demote clause) -/

theorem vmLastEntry_map_key {K V W : Type} [DecidableEq K] (l : List (K × V)) (f : K × V → K × W)
    (hf : ∀ p, (f p).1 = p.1) (key : K) :
    vmLastEntry (l.map f) key = (vmLastEntry l key).map f := by
  unfold vmLastEntry
  have hfilt : (l.map f).filter (vmKeyEq key) = (l.filter (vmKeyEq key)).map f := by
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.filter_cons, vmKeyEq, hf]
      by_cases hh : hd.1 = key <;> simp [hh, ih]
  rw [hfilt, List.getLast?_map]

/-- The pending `R`-clause under `demote_all_of`. -/
theorem ingest_demote_pending_clause (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (agent : types.AgentId) (I : types.InvocationId) :
    optRel pendingRel (Tzimtzum.demoteAllOf a.pending agent I)
      ((vmLastEntry (st.pending.entries.val.map (demoteEntry agent)) I).map Prod.snd) := by
  rw [vmLastEntry_map_key _ (demoteEntry agent) (fun p => rfl) I]
  have hRp := hR.pending I; unfold pendingC at hRp
  cases hL : vmLastEntry st.pending.entries.val I with
  | none =>
    rw [hL] at hRp; simp only [Option.map_none] at hRp ⊢
    cases haI : a.pending I with
    | none => simp [Tzimtzum.demoteAllOf, haI, optRel]
    | some J => rw [haI] at hRp; simp only [optRel] at hRp
  | some p =>
    rw [hL] at hRp; simp only [Option.map_some] at hRp ⊢
    cases haI : a.pending I with
    | none => rw [haI] at hRp; simp only [optRel] at hRp
    | some J =>
      rw [haI] at hRp; simp only [optRel] at hRp
      obtain ⟨hag, hsnap, hegr, hadm, hdisp, hauth, hquar⟩ := hRp
      simp only [Tzimtzum.demoteAllOf, haI, demoteEntry]
      by_cases hja : J.agent = agent
      · have hpa : p.2.agent = agent := by rw [← hag]; exact hja
        rw [if_pos hja, if_pos hpa]
        exact ⟨hag, hsnap, hegr, hadm, rfl, hauth, hquar⟩
      · have hpa : ¬ p.2.agent = agent := by rw [← hag]; exact hja
        rw [if_neg hja, if_neg hpa]
        exact ⟨hag, hsnap, hegr, hadm, hdisp, hauth, hquar⟩

/-- Combined: `ingest_holds` decides the abstract `ingestHolds`. -/
theorem ingestHoldsAbs_spec (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (agent : types.AgentId) (pconf : types.ConfLevel) (pinteg : types.IntegLevel) :
    transitions.ingest_holds st bg agent pconf pinteg ⦃ b =>
      b = true ↔ Tzimtzum.ingestHolds a agent (confA pconf) (integA pinteg) ⦄ := by
  unfold transitions.ingest_holds Tzimtzum.ingestHolds
  obtain ⟨bc, hbcEq, hbc⟩ := spec_imp_exists (ingestConfHold_spec st bg agent pconf hR.ndPending)
  rw [hbcEq]; simp only [bind_tc_ok]
  by_cases hbcv : bc = true
  · simp only [hbcv, reduceIte]
    obtain ⟨bcl, hbclEq, hbcl⟩ := spec_imp_exists (ingestClearHold_spec st agent pconf hR.ndPending)
    rw [hbclEq]; simp only [bind_tc_ok]
    by_cases hbclv : bcl = true
    · simp only [hbclv, reduceIte]
      obtain ⟨bi, hbiEq, hbi⟩ := spec_imp_exists (ingestIntegHold_spec st agent pinteg hR.ndPending)
      rw [hbiEq]; simp only [spec_ok, hbi]
      have hconf := hbc.mp hbcv
      have hclear := hbcl.mp hbclv
      constructor
      · intro hinteg
        exact ⟨(ingestConfHold_bridge st bg a hR agent pconf).mp hconf,
          (ingestClearHold_bridge st bg a hR agent pconf).mp hclear,
          (ingestIntegHold_bridge st bg a hR agent pinteg).mp hinteg⟩
      · rintro ⟨_, _, hinteg⟩
        exact (ingestIntegHold_bridge st bg a hR agent pinteg).mpr hinteg
    · rw [Bool.not_eq_true] at hbclv
      simp only [hbclv, Bool.false_eq_true, reduceIte, spec_ok]
      have hnclear : ¬ Tzimtzum.ingestClearHold a agent (confA pconf) := by
        rw [← ingestClearHold_bridge st bg a hR agent pconf]; intro hc
        rw [hbcl.mpr hc] at hbclv; exact Bool.noConfusion hbclv
      constructor
      · intro hc; exact absurd hc (by decide)
      · rintro ⟨_, hcl, _⟩; exact absurd hcl hnclear
  · rw [Bool.not_eq_true] at hbcv
    simp only [hbcv, Bool.false_eq_true, reduceIte, spec_ok]
    have hnconf : ¬ Tzimtzum.ingestConfHold a agent (confA pconf) := by
      rw [← ingestConfHold_bridge st bg a hR agent pconf]; intro hc
      rw [hbc.mpr hc] at hbcv; exact Bool.noConfusion hbcv
    constructor
    · intro hc; exact absurd hc (by decide)
    · rintro ⟨hcf, _, _⟩; exact absurd hcf hnconf

/-! ## Source-domination bridges -/

theorem taint_domination_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (src_agent : types.AgentId) (pconf : types.ConfLevel)
    (src_taint : collections.VecSet types.ConfLevel)
    (hst : ∀ l, vsMem src_taint l ↔ vmsMemLast st.taint_levels src_agent l) :
    (∀ l ∈ src_taint.items.val, confLeC l pconf = true) ↔
      (∀ L, a.taint_levels src_agent L → Tzimtzum.le_conf L (confA pconf)) := by
  constructor
  · intro hc L hL
    have hml : vmsMemLast st.taint_levels src_agent (confC L) := (hR.taint src_agent L).mp hL
    have := hc (confC L) ((hst (confC L)).mpr hml)
    rw [le_conf_confLeC]; exact this
  · intro habs l hl
    have hml : vmsMemLast st.taint_levels src_agent l := (hst l).mp hl
    have haL : a.taint_levels src_agent (confA l) :=
      (hR.taint src_agent (confA l)).mpr (by rw [confC_confA]; exact hml)
    rw [← le_conf_confLeC_both]; exact habs (confA l) haL

theorem integ_domination_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (src_agent : types.AgentId) (pinteg : types.IntegLevel)
    (src_integ : collections.VecSet types.IntegLevel)
    (hst : ∀ l, vsMem src_integ l ↔ vmsMemLast st.integ_levels src_agent l) :
    (∀ l ∈ src_integ.items.val, integLeC pinteg l = true) ↔
      (∀ L, a.integ_levels src_agent L → Tzimtzum.le_integ (integA pinteg) L) := by
  constructor
  · intro hc L hL
    have hml : vmsMemLast st.integ_levels src_agent (integC L) := (hR.integ src_agent L).mp hL
    have := hc (integC L) ((hst (integC L)).mpr hml)
    rw [le_integ_integLeC']; exact this
  · intro habs l hl
    have hml : vmsMemLast st.integ_levels src_agent l := (hst l).mp hl
    have haL : a.integ_levels src_agent (integA l) :=
      (hR.integ src_agent (integA l)).mpr (by rw [integC_integA]; exact hml)
    have hle := (le_integ_integLeC' pinteg (integA l)).mp (habs (integA l) haL)
    rwa [integC_integA] at hle

/-! ## Disposition / Mode equality specs -/

deriving instance DecidableEq for types.Disposition
deriving instance DecidableEq for types.Mode

@[simp] theorem disposition_eq_spec (x y : types.Disposition) :
    types.Disposition.Insts.CoreCmpPartialEqDisposition.eq x y = .ok (decide (x = y)) := by
  cases x <;> cases y <;>
    simp [types.Disposition.Insts.CoreCmpPartialEqDisposition.eq, types.Disposition.read_discriminant]

@[simp] theorem mode_eq_spec (x y : types.Mode) :
    types.Mode.Insts.CoreCmpPartialEqMode.eq x y = .ok (decide (x = y)) := by
  cases x <;> cases y <;>
    simp [types.Mode.Insts.CoreCmpPartialEqMode.eq, types.Mode.read_discriminant]

/-! ## Main preservation -/

/-- The abstract `ingest` post-image at disposition `d`. -/
noncomputable def ingestAbs (a : AbsState) (a_agent : types.AgentId) (pconf : types.ConfLevel)
    (pinteg : types.IntegLevel) (d : Tzimtzum.Disposition) : AbsState :=
  { a with
    taint_levels := fun A L => a.taint_levels A L ∨ (A = a_agent ∧ L = confA pconf),
    integ_levels := fun A L => a.integ_levels A L ∨ (A = a_agent ∧ L = integA pinteg),
    pending := if d = Tzimtzum.Disposition.monitor_bypassed then
      Tzimtzum.demoteAllOf a.pending a_agent else a.pending }

/-- `R`-transport after a taint/integ insert (both permitted and monitor-bypassed leaves). -/
theorem ingest_insert_R (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (a_agent : types.AgentId) (pconf : types.ConfLevel) (pinteg : types.IntegLevel)
    (d : Tzimtzum.Disposition)
    (vm : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (vm1 : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (hvm : ∀ k v, vmsMemLast vm k v ↔ vmsMemLast st.taint_levels k v ∨ (k = a_agent ∧ v = pconf))
    (hvm1 : ∀ k v, vmsMemLast vm1 k v ↔ vmsMemLast st.integ_levels k v ∨ (k = a_agent ∧ v = pinteg))
    (hvmnd : vmNodupKeys vm) (hvm1nd : vmNodupKeys vm1)
    (st' : state.KernelState)
    (hactive' : st'.agent_active = st.agent_active) (hparent' : st'.agent_parent = st.agent_parent)
    (hcap' : st'.agent_cap = st.agent_cap) (htaint' : st'.taint_levels = vm)
    (hinteg' : st'.integ_levels = vm1) (htool' : st'.tool_registered = st.tool_registered)
    (hchal' : st'.challenges = st.challenges) (hgr' : st'.crossing_grants = st.crossing_grants)
    (hci' : st'.consumed_ids = st.consumed_ids)
    (hca' : st'.consumed_attestations = st.consumed_attestations)
    (hcc' : st'.consumed_crossings = st.consumed_crossings)
    (hpendClause : ∀ I, optRel pendingRel ((ingestAbs a a_agent pconf pinteg d).pending I) (pendingC st' I))
    (hpendNd : vmNodupKeys st'.pending) :
    R st' bg (ingestAbs a a_agent pconf pinteg d) := by
  refine
    { root := hR.root, mode := hR.mode
      active := ?_, tool_reg := ?_, parent := ?_, cap := ?_, taint := ?_, integ := ?_
      pending := hpendClause, challenges := ?_, grants := ?_
      consumedIds := ?_, consumedAtt := ?_, consumedCross := ?_
      flowAllows := hR.flowAllows, flowInspects := hR.flowInspects
      ndParent := ?_, ndCap := ?_, ndTaint := ?_, ndInteg := ?_
      ndPending := hpendNd, ndChallenges := ?_, ndGrants := ?_ }
  · intro x; rw [hactive']; exact hR.active x
  · intro t; rw [htool']; exact hR.tool_reg t
  · intro C P; rw [hparent']; exact hR.parent C P
  · intro N C; rw [hcap']; exact hR.cap N C
  · intro A L; rw [htaint']; exact ingest_taint_clause st bg a hR a_agent pconf vm hvm A L
  · intro A L; rw [hinteg']; exact ingest_integ_clause st bg a hR a_agent pinteg vm1 hvm1 A L
  · intro I; show optRel challengeRel (a.challenges I) (challengeC st' I)
    unfold challengeC; rw [hchal']; exact hR.challenges I
  · intro A D
    show optRel crossingGrantRel (a.crossing_grants A D)
      (crossingGrantC st' { agent := A, assignment := D })
    unfold crossingGrantC; rw [hgr']; exact hR.grants A D
  · intro I; rw [hci']; exact hR.consumedIds I
  · intro Att; rw [hca']; exact hR.consumedAtt Att
  · intro X; rw [hcc']; exact hR.consumedCross X
  · rw [hparent']; exact hR.ndParent
  · rw [hcap']; exact hR.ndCap
  · rw [htaint']; exact hvmnd
  · rw [hinteg']; exact hvm1nd
  · rw [hchal']; exact hR.ndChallenges
  · rw [hgr']; exact hR.ndGrants

/-- The shared holds → insert → disposition dispatch (identical for both source cases). -/
theorem ingest_after_holds (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (a_agent : types.AgentId) (src : Option types.AgentId)
    (pconf : types.ConfLevel) (pinteg : types.IntegLevel)
    (hcapTE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIS : ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (hactive : a.agent_active a_agent)
    (hdomGuard : ∀ src', src = some src' →
      (∀ L, a.taint_levels src' L → Tzimtzum.le_conf L (confA pconf)) ∧
      (∀ L, a.integ_levels src' L → Tzimtzum.le_integ (integA pinteg) L))
    (holds : Bool) (hholds : holds = true ↔ Tzimtzum.ingestHolds a a_agent (confA pconf) (integA pinteg))
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok :
      (if holds = true then do
          let ai ← types.AgentId.Insts.CoreCloneClone.clone a_agent
          let vm ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
            types.ConfLevel.Insts.CoreCmpPartialEqConfLevel st.taint_levels ai pconf
          let vm1 ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId types.IntegLevel.Insts.CoreCloneClone
            types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel st.integ_levels ai pinteg
          let b1 ← types.Disposition.Insts.CoreCmpPartialEqDisposition.eq
            types.Disposition.Permitted types.Disposition.MonitorBypassed
          if b1 = true then do
              let s1 ← state.KernelState.demote_all_of
                { st with taint_levels := vm, integ_levels := vm1 } a_agent
              ok (.Ok (s1, event.KernelAction.Ingest a_agent src pconf pinteg
                types.Disposition.Permitted))
            else ok (.Ok ({ st with taint_levels := vm, integ_levels := vm1 },
              event.KernelAction.Ingest a_agent src pconf pinteg types.Disposition.Permitted))
        else do
          let m ← background.BackgroundTheory.impl.mode bg
          let b1 ← types.Mode.Insts.CoreCmpPartialEqMode.eq m types.Mode.Monitor
          if b1 = true then do
              let ai ← types.AgentId.Insts.CoreCloneClone.clone a_agent
              let vm ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
                types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
                types.ConfLevel.Insts.CoreCmpPartialEqConfLevel st.taint_levels ai pconf
              let vm1 ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
                types.AgentId.Insts.CoreCmpPartialEqAgentId types.IntegLevel.Insts.CoreCloneClone
                types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel st.integ_levels ai pinteg
              let b2 ← types.Disposition.Insts.CoreCmpPartialEqDisposition.eq
                types.Disposition.MonitorBypassed types.Disposition.MonitorBypassed
              if b2 = true then do
                  let s1 ← state.KernelState.demote_all_of
                    { st with taint_levels := vm, integ_levels := vm1 } a_agent
                  ok (.Ok (s1, event.KernelAction.Ingest a_agent src pconf pinteg
                    types.Disposition.MonitorBypassed))
                else ok (.Ok ({ st with taint_levels := vm, integ_levels := vm1 },
                  event.KernelAction.Ingest a_agent src pconf pinteg
                  types.Disposition.MonitorBypassed))
            else ok (.Err error.KernelError.IngestHoldFailed)) =
        (.ok (.Ok (st', ev)) :
          Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError))) :
    ∃ (d : Tzimtzum.Disposition) (a' : AbsState),
      (Tzimtzum.ingest a_agent src (confA pconf) (integA pinteg) d).guard a ∧
      (Tzimtzum.ingest a_agent src (confA pconf) (integA pinteg) d).next a a' ∧ R st' bg a' := by
  -- shared insert obtain
  have hinsertT := fun (s : state.KernelState) =>
    vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels a_agent pconf hcapTE hcapTS
  by_cases hh : holds = true
  · -- permitted
    simp only [hh, reduceIte, agentId_clone_spec, bind_tc_ok] at hok
    obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.taint_levels a_agent pconf hcapTE hcapTS)
    rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm1, hvm1Eq, hvm1⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        integLevel_eq_spec integLevel_clone_spec st.integ_levels a_agent pinteg hcapIE hcapIS)
    rw [hvm1Eq] at hok; simp only [bind_tc_ok, disposition_eq_spec, reduceCtorEq, decide_false,
      Bool.false_eq_true, reduceIte, Result.ok.injEq, core.result.Result.Ok.injEq,
      Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _hEv⟩ := hok; subst hStateEq
    obtain ⟨vmnd, hvmndEq, hvmnd⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.taint_levels a_agent pconf hcapTE hcapTS)
    obtain ⟨vm1nd, hvm1ndEq, hvm1nd⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        integLevel_eq_spec integLevel_clone_spec st.integ_levels a_agent pinteg hcapIE hcapIS)
    have hvmnd' : vmNodupKeys vm := by
      have := Result.ok.inj (hvmndEq.symm.trans hvmEq); rw [← this]; exact hvmnd hR.ndTaint
    have hvm1nd' : vmNodupKeys vm1 := by
      have := Result.ok.inj (hvm1ndEq.symm.trans hvm1Eq); rw [← this]; exact hvm1nd hR.ndInteg
    refine ⟨Tzimtzum.Disposition.permitted, ingestAbs a a_agent pconf pinteg .permitted, ?_, ?_, ?_⟩
    · exact ⟨hactive, hdomGuard, by decide, fun _ => hholds.mp hh,
        fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    · simp [Tzimtzum.ingest, ingestAbs]
    · refine ingest_insert_R st bg a hR a_agent pconf pinteg .permitted vm vm1 hvm hvm1 hvmnd'
        hvm1nd' { st with taint_levels := vm, integ_levels := vm1 } rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl ?_ hR.ndPending
      intro I; show optRel pendingRel ((ingestAbs a a_agent pconf pinteg .permitted).pending I)
        (pendingC { st with taint_levels := vm, integ_levels := vm1 } I)
      simp only [ingestAbs, reduceCtorEq, if_false]; exact hR.pending I
  · -- not holds
    rw [Bool.not_eq_true] at hh
    simp only [hh, Bool.false_eq_true, reduceIte, background.BackgroundTheory.impl.mode,
      mode_eq_spec, bind_tc_ok] at hok
    by_cases hm : bg.mode = types.Mode.Monitor
    · simp only [hm, decide_true, reduceIte, agentId_clone_spec, bind_tc_ok] at hok
      obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels a_agent pconf hcapTE hcapTS)
      rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
      obtain ⟨vm1, hvm1Eq, hvm1⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels a_agent pinteg hcapIE hcapIS)
      rw [hvm1Eq] at hok; simp only [bind_tc_ok, disposition_eq_spec, decide_true, reduceIte] at hok
      obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1ch, hs1ci, hs1ca, hs1cc, hs1g, hs1tr,
          hs1pend⟩ := spec_imp_exists
        (demoteAllOf_spec { st with taint_levels := vm, integ_levels := vm1 } a_agent hR.ndPending)
      rw [hs1Eq] at hok
      simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨hStateEq, _hEv⟩ := hok; subst hStateEq
      obtain ⟨vmnd, hvmndEq, hvmnd⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels a_agent pconf hcapTE hcapTS)
      obtain ⟨vm1nd, hvm1ndEq, hvm1nd⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels a_agent pinteg hcapIE hcapIS)
      have hvmnd' : vmNodupKeys vm := by
        have := Result.ok.inj (hvmndEq.symm.trans hvmEq); rw [← this]; exact hvmnd hR.ndTaint
      have hvm1nd' : vmNodupKeys vm1 := by
        have := Result.ok.inj (hvm1ndEq.symm.trans hvm1Eq); rw [← this]; exact hvm1nd hR.ndInteg
      refine ⟨Tzimtzum.Disposition.monitor_bypassed,
        ingestAbs a a_agent pconf pinteg .monitor_bypassed, ?_, ?_, ?_⟩
      · exact ⟨hactive, hdomGuard, by decide, fun h => absurd h (by decide),
          fun _ => by rw [← hholds]; intro hc; rw [hc] at hh; exact Bool.noConfusion hh,
          fun _ => hR.mode.trans (by rw [hm]; rfl)⟩
      · simp [Tzimtzum.ingest, ingestAbs]
      · refine ingest_insert_R st bg a hR a_agent pconf pinteg .monitor_bypassed vm vm1 hvm hvm1
          hvmnd' hvm1nd' s1 hs1a hs1p hs1c hs1t hs1i hs1tr hs1ch hs1g hs1ci hs1ca hs1cc ?_ ?_
        · intro I
          show optRel pendingRel ((ingestAbs a a_agent pconf pinteg .monitor_bypassed).pending I)
            (pendingC s1 I)
          simp only [ingestAbs, if_pos rfl]
          unfold pendingC; rw [hs1pend]
          exact ingest_demote_pending_clause st bg a hR a_agent I
        · unfold vmNodupKeys; rw [hs1pend, List.map_map]
          have hfe : Prod.fst ∘ demoteEntry a_agent =
              (Prod.fst : types.InvocationId × types.PendingInvocation → types.InvocationId) := by
            funext x; rfl
          rw [hfe]; exact hR.ndPending
    · simp [hm] at hok

/-- `ingest` preserves the unified `R`. -/
theorem ingest_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (a_agent : types.AgentId) (src : Option types.AgentId) (pconf : types.ConfLevel)
    (pinteg : types.IntegLevel) (hR : R st bg a)
    (hcapTE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIS : ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.ingest st bg a_agent src pconf pinteg = .ok (.Ok (st', ev))) :
    ∃ (d : Tzimtzum.Disposition) (a' : AbsState),
      (Tzimtzum.ingest a_agent src (confA pconf) (integA pinteg) d).guard a ∧
      (Tzimtzum.ingest a_agent src (confA pconf) (integA pinteg) d).next a a' ∧ R st' bg a' := by
  simp only [transitions.ingest] at hok
  obtain ⟨ba, hbaEq, hbaIff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active a_agent)
  rw [hbaEq] at hok; simp only [bind_tc_ok] at hok
  have hba : ba = true := by cases ba with | true => rfl | false => simp at hok
  simp only [hba, reduceIte] at hok
  have hactive : a.agent_active a_agent := (hR.active a_agent).mpr (hbaIff.mp hba)
  cases src with
  | none =>
    dsimp only at hok
    obtain ⟨holds, hEq, hholds⟩ := spec_imp_exists (ingestHoldsAbs_spec st bg a hR a_agent pconf pinteg)
    rw [hEq] at hok; simp only [bind_tc_ok] at hok
    exact ingest_after_holds st bg a hR a_agent none pconf pinteg hcapTE hcapTS hcapIE hcapIS
      hactive (fun _ h => absurd h (by simp)) holds hholds st' ev hok
  | some src_agent =>
    dsimp only at hok
    obtain ⟨src_taint, hstEq, hst⟩ := spec_imp_exists
      (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_clone_spec st.taint_levels src_agent)
    rw [hstEq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨dom, hdomEq, hdom⟩ := spec_imp_exists
      (ingestLoop0_spec (st0 := true) pconf src_taint true 0#usize (by simp) (by simp))
    rw [hdomEq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨src_integ, hsiEq, hsi⟩ := spec_imp_exists
      (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        integLevel_clone_spec st.integ_levels src_agent)
    rw [hsiEq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨dom1, hdom1Eq, hdom1⟩ := spec_imp_exists
      (ingestLoop1_spec (st0 := dom) pinteg src_integ dom 0#usize (by simp) (by simp))
    rw [hdom1Eq] at hok; simp only [bind_tc_ok] at hok
    by_cases hd1 : dom1 = true
    · simp only [hd1, reduceIte] at hok
      have hdomGuard : ∀ src', some src_agent = some src' →
          (∀ L, a.taint_levels src' L → Tzimtzum.le_conf L (confA pconf)) ∧
          (∀ L, a.integ_levels src' L → Tzimtzum.le_integ (integA pinteg) L) := by
        intro src' hsrc; injection hsrc with hsrc; subst hsrc
        obtain ⟨hdomv, hintegAll⟩ := hdom1.mp hd1
        exact ⟨(taint_domination_bridge st bg a hR src_agent pconf src_taint hst).mp
            (hdom.mp hdomv).2,
          (integ_domination_bridge st bg a hR src_agent pinteg src_integ hsi).mp hintegAll⟩
      obtain ⟨holds, hEq, hholds⟩ := spec_imp_exists
        (ingestHoldsAbs_spec st bg a hR a_agent pconf pinteg)
      rw [hEq] at hok; simp only [bind_tc_ok] at hok
      exact ingest_after_holds st bg a hR a_agent (some src_agent) pconf pinteg hcapTE hcapTS
        hcapIE hcapIS hactive hdomGuard holds hholds st' ev hok
    · rw [Bool.not_eq_true] at hd1
      simp only [hd1, Bool.false_eq_true, reduceIte] at hok
      simp at hok

end ArgusLean.Refinement
