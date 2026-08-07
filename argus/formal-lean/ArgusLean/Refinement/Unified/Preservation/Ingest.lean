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

end ArgusLean.Refinement
