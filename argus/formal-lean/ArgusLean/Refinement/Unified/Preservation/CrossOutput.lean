import ArgusLean.Refinement.Unified.Preservation.SettleInvocation

/-! # Layer 1 — `cross_output` preserves the unified `R` (V4)

The concrete trichotomy is bridged to the single abstract crossing action. Endorsed crossings
consume exact fresh evidence and one receiver grant use; unendorsed crossings copy source labels;
fail crossings release no labels. Every successful branch consumes the crossing identifier, and
monitor bypass demotes the receiver's pending records.
-/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

deriving instance DecidableEq for types.CrossBranch

@[simp] theorem crossBranch_eq_spec (x y : types.CrossBranch) :
    types.CrossBranch.Insts.CoreCmpPartialEqCrossBranch.eq x y = .ok (decide (x = y)) := by
  cases x <;> cases y <;>
    simp [types.CrossBranch.Insts.CoreCmpPartialEqCrossBranch.eq,
      types.CrossBranch.read_discriminant]

/-- Concrete crossing branches mapped constructor-for-constructor to the abstract trichotomy. -/
def crossBranchA : types.CrossBranch → Tzimtzum.CrossBranch
  | .Endorsed => .endorsed
  | .Unendorsed => .unendorsed
  | .Fail => .fail

/-! ## Source-pending scan -/

/-- Prefix invariant for the extracted scan that rejects a source with pending work. -/
def sourceInFlightPrefix (vm : collections.VecMap types.InvocationId types.PendingInvocation)
    (src : types.AgentId) (n : Nat) : Prop :=
  ∃ p ∈ vm.entries.val.take n, p.2.agent = src

theorem crossOutputLoop0_spec (vm : collections.VecMap types.InvocationId types.PendingInvocation)
    (src : types.AgentId) (hnd : vmNodupKeys vm) (found : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ vm.entries.val.length)
    (hstart : found = true ↔ sourceInFlightPrefix vm src i0.val) :
    transitions.cross_output_loop0 vm src found i0 ⦃ b =>
      b = true ↔ ∃ p ∈ vm.entries.val, p.2.agent = src ⦄ := by
  unfold transitions.cross_output_loop0
  apply loop.spec_decr_nat
    (measure := fun p => vm.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ vm.entries.val.length ∧
      (p.1 = true ↔ sourceInFlightPrefix vm src p.2.val))
  · rintro ⟨seen, i⟩ ⟨hile, hinv⟩
    simp only [transitions.cross_output_loop0.body, collections.VecMap.len,
      alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < vm.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone vm i hlt)
      rw [hkEq]
      simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec vm k)
      have hlast : vmLastEntry vm.entries.val k =
          some ((vm.entries.val[i.val]'hlt).1, (vm.entries.val[i.val]'hlt).2) := by
        rw [hk]
        exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, agentId_eq_spec, bind_tc_ok]
      set p := vm.entries.val[i.val]'hlt with hp
      have hprefix : sourceInFlightPrefix vm src (i.val + 1) ↔
          sourceInFlightPrefix vm src i.val ∨ p.2.agent = src := by
        unfold sourceInFlightPrefix
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hp]
        constructor
        · rintro ⟨q, hq | hq, ha⟩
          · exact Or.inl ⟨q, hq, ha⟩
          · subst hq
            exact Or.inr ha
        · rintro (⟨q, hq, ha⟩ | ha)
          · exact ⟨q, Or.inl hq, ha⟩
          · exact ⟨p, Or.inr rfl, ha⟩
      by_cases hps : p.2.agent = src
      · simp only [hps, decide_true, reduceIte]
        step*
      · simp only [hps, decide_false, Bool.false_eq_true, reduceIte]
        step*
    case isFalse h =>
      have hi : i.val = vm.entries.val.length := by scalar_tac
      simp only [spec_ok, hi, List.take_length] at hinv ⊢
      simpa [sourceInFlightPrefix] using hinv
  · exact ⟨hi0, hstart⟩

/-- A false concrete source scan is exactly the abstract no-in-flight-source guard. -/
theorem sourceNotInFlight_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (src : types.AgentId)
    (hnone : ¬∃ p ∈ st.pending.entries.val, p.2.agent = src) :
    ∀ I J, a.pending I = some J → J.agent ≠ src := by
  intro I J hJ hJa
  obtain ⟨cj, hmem, hrel⟩ := abs_pending_to_entry st bg a hR I J hJ
  apply hnone
  exact ⟨(I, cj), hmem, by rw [← hrel.1, hJa]⟩

/-! ## Endorsement and receiver holds -/

/-- Concrete evidence half of endorsement, before the grant lookup. -/
def endorsedEvidenceC (st : state.KernelState) (q : types.CrossInput) : Prop :=
  ∃ e, q.evidence = some e ∧ e.positive = true ∧ ¬vsMem st.consumed_attestations e.id ∧
    e.output = q.output_hash ∧ e.src = q.src ∧ e.rcv = q.rcv ∧
    e.descriptor = q.descriptor ∧ e.assignment = q.assignment

/-- Exact input correspondence transports the evidence half of endorsement. -/
theorem endorsedEvidence_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) (hq : crossInputRel qA q) :
    endorsedEvidenceC st q ↔
      ∃ e, qA.evidence = some e ∧ e.positive ∧ ¬a.consumed_attestations e.id ∧
        e.output = qA.output_hash ∧ e.src = qA.src ∧ e.rcv = qA.rcv ∧
        e.descriptor = qA.descriptor ∧ e.assignment = qA.assignment := by
  obtain ⟨hsrc, hrcv, _, hout, hdesc, _, _, _, hassign, hev, _, _⟩ := hq
  cases hqe : q.evidence with
  | none =>
    cases hqAe : qA.evidence with
    | none => simp [endorsedEvidenceC, hqe, hqAe]
    | some eA => simp [hqe, hqAe, optRel] at hev
  | some e =>
    cases hqAe : qA.evidence with
    | none => simp [hqe, hqAe, optRel] at hev
    | some eA =>
      have herel : conformanceAttestationRel eA e := by
        simpa [hqe, hqAe, optRel] using hev
      obtain ⟨hid, heout, hesrc, hercv, hedesc, heassign, hepos⟩ := herel
      constructor
      · rintro ⟨e', he', hp, hfresh, ho, hs, hr, hd, ha⟩
        rw [hqe] at he'
        injection he' with he'
        subst e'
        refine ⟨eA, rfl, hepos.mpr hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hc
          apply hfresh
          exact (hR.consumedAtt e.id).mp (by rw [← hid]; exact hc)
        · rw [heout, hout, ho]
        · rw [hesrc, hsrc, hs]
        · rw [hercv, hrcv, hr]
        · rw [hedesc, hdesc, hd]
        · rw [heassign, hassign, ha]
      · rintro ⟨eA', heA', hp, hfresh, ho, hs, hr, hd, ha⟩
        injection heA' with heA'
        subst eA'
        refine ⟨e, hqe, hepos.mp hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hc
          apply hfresh
          rw [hid]
          exact (hR.consumedAtt e.id).mpr hc
        · rw [← heout, ← hout, ho]
        · rw [← hesrc, ← hsrc, hs]
        · rw [← hercv, ← hrcv, hr]
        · rw [← hedesc, ← hdesc, hd]
        · rw [← heassign, ← hassign, ha]

/-- Concrete grant half of endorsement. -/
def endorsedGrantC (st : state.KernelState) (q : types.CrossInput) : Prop :=
  ∃ g, crossingGrantC st { agent := q.rcv, assignment := q.assignment } = some g ∧
    0 < g.remaining.val

/-- `R` transports the receiver/assignment grant half of endorsement. -/
theorem endorsedGrant_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) (hq : crossInputRel qA q) :
    endorsedGrantC st q ↔
      ∃ g, a.crossing_grants qA.rcv qA.assignment = some g ∧ 0 < g.remaining := by
  obtain ⟨_, hrcv, _, _, _, _, _, _, hassign, _, _, _⟩ := hq
  have hgr := hR.grants qA.rcv qA.assignment
  cases hc : crossingGrantC st { agent := q.rcv, assignment := q.assignment } with
  | none =>
    have hcA : crossingGrantC st { agent := qA.rcv, assignment := qA.assignment } = none := by
      rw [hrcv, hassign]
      exact hc
    rw [hcA] at hgr
    cases ha : a.crossing_grants qA.rcv qA.assignment with
    | none => simp [endorsedGrantC, hc, ha]
    | some gA => simp [ha, optRel] at hgr
  | some g =>
    have hcA : crossingGrantC st { agent := qA.rcv, assignment := qA.assignment } = some g := by
      rw [hrcv, hassign]
      exact hc
    rw [hcA] at hgr
    cases ha : a.crossing_grants qA.rcv qA.assignment with
    | none => simp [ha, optRel] at hgr
    | some gA =>
      have hrel : crossingGrantRel gA g := by simpa [ha, optRel] using hgr
      simp only [endorsedGrantC, hc, true_and, ha, Option.some.injEq, exists_eq_left']
      rw [hrel.1]

/-- The extracted implementation of `endorsed_ok`, stated wholly in concrete views. -/
theorem endorsedOKC_spec (st : state.KernelState) (q : types.CrossInput) :
    transitions.endorsed_ok st q ⦃ b =>
      b = true ↔ endorsedEvidenceC st q ∧ endorsedGrantC st q ⦄ := by
  unfold transitions.endorsed_ok
  cases hqe : q.evidence with
  | none => simp [endorsedEvidenceC, hqe]
  | some e =>
    simp only [hqe]
    by_cases hp : e.positive = true
    · simp only [hp, reduceIte]
      obtain ⟨bc, hbcEq, hbc⟩ := spec_imp_exists
        (vecSetContains_spec types.AttestationId.Insts.CoreCloneClone
          types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
          st.consumed_attestations e.id)
      rw [hbcEq]
      simp only [bind_tc_ok]
      by_cases hc : bc = true
      · simp [hc, endorsedEvidenceC, hqe]
        intro _ hfresh
        exact absurd (hbc.mp hc) hfresh
      · have hcF : bc = false := by simpa using hc
        simp only [hcF, Bool.false_eq_true, reduceIte, contentHash_eq_spec, bind_tc_ok]
        by_cases ho : e.output = q.output_hash
        · simp only [ho, decide_true, reduceIte, agentId_eq_spec, bind_tc_ok]
          by_cases hs : e.src = q.src
          · simp only [hs, decide_true, reduceIte, agentId_eq_spec, bind_tc_ok]
            by_cases hr : e.rcv = q.rcv
            · simp only [hr, decide_true, reduceIte, contentHash_eq_spec, bind_tc_ok]
              by_cases hd : e.descriptor = q.descriptor
              · simp only [hd, decide_true, reduceIte, assignmentDigest_eq_spec, bind_tc_ok]
                by_cases ha : e.assignment = q.assignment
                · simp only [ha, decide_true, reduceIte, agentId_clone_spec,
                    assignmentDigest_clone_spec, bind_tc_ok]
                  change (do
                    let og ← collections.VecMap.get_cloned
                      types.CrossingKey.Insts.CoreCloneClone
                      types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey
                      types.CrossingGrant.Insts.CoreCloneClone st.crossing_grants
                      { agent := q.rcv, assignment := q.assignment }
                    match og with
                    | none => ok false
                    | some g => ok (g.remaining > 0#u32)) ⦃ b =>
                      b = true ↔ endorsedEvidenceC st q ∧ endorsedGrantC st q ⦄
                  obtain ⟨og, hogEq, hog⟩ := spec_imp_exists
                    (vecMapGetCloned_spec types.CrossingKey.Insts.CoreCloneClone
                      types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
                      types.CrossingGrant.Insts.CoreCloneClone (fun g => rfl)
                      st.crossing_grants { agent := q.rcv, assignment := q.assignment })
                  rw [hogEq]
                  simp only [bind_tc_ok]
                  cases hogO : og with
                  | none =>
                    simp only [hogO, spec_ok, Bool.false_eq_true, false_iff]
                    rintro ⟨_, hgrant⟩
                    obtain ⟨g, hg, _⟩ := hgrant
                    unfold crossingGrantC at hg
                    rw [← hog, hogO] at hg
                    contradiction
                  | some g =>
                    simp only [hogO, spec_ok]
                    have hcg : crossingGrantC st
                        { agent := q.rcv, assignment := q.assignment } = some g := by
                      unfold crossingGrantC
                      rw [← hog, hogO]
                    have hevidence : endorsedEvidenceC st q :=
                      ⟨e, hqe, hp, by
                        intro hm
                        have := hbc.mpr hm
                        rw [hcF] at this
                        contradiction,
                      ho, hs, hr, hd, ha⟩
                    constructor
                    · intro hgt
                      exact ⟨hevidence, g, hcg, by simpa using hgt⟩
                    · rintro ⟨_, g', hg', hrem⟩
                      rw [hcg] at hg'
                      injection hg' with hg'
                      subst g'
                      simpa using hrem
                · simp [ha, endorsedEvidenceC, hqe]
              · simp [hd, endorsedEvidenceC, hqe]
            · simp [hr, endorsedEvidenceC, hqe]
          · simp [hs, endorsedEvidenceC, hqe]
        · simp [ho, endorsedEvidenceC, hqe]
    · have hpF : e.positive = false := by simpa using hp
      simp [hpF, endorsedEvidenceC, hqe]

/-- Concrete endorsement is exactly abstract `endorsedOK`. -/
theorem endorsedOK_spec (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) (hq : crossInputRel qA q) :
    transitions.endorsed_ok st q ⦃ b => b = true ↔ Tzimtzum.endorsedOK a qA ⦄ := by
  obtain ⟨b, hbEq, hb⟩ := spec_imp_exists (endorsedOKC_spec st q)
  rw [hbEq]
  simp only [spec_ok]
  rw [hb, Tzimtzum.endorsedOK_iff, endorsedEvidence_bridge st bg a hR q qA hq,
    endorsedGrant_bridge st bg a hR q qA hq]


/-! ## Receiver hold decision -/

theorem crossHoldsLoop0_spec (st : state.KernelState) (bg : background.BackgroundTheory)
    (rcv : types.AgentId) (srcTaint : collections.VecSet types.ConfLevel)
    (hnd : (st.pending.entries.val.map Prod.fst).Nodup)
    (ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ srcTaint.items.val.length)
    (hstart : ok0 = true ↔
      ∀ l ∈ srcTaint.items.val.take i0.val,
        (∀ p ∈ st.pending.entries.val, p.2.agent = rcv → confRecordC bg l p) ∧
        (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
          confLeC l p.2.policy.conf_clearance = true)) :
    transitions.cross_holds_loop0 st.agent_active st.agent_parent st.agent_cap st.taint_levels
      st.integ_levels st.pending st.challenges st.consumed_ids st.consumed_attestations
      st.consumed_crossings st.crossing_grants st.tool_registered bg rcv ok0 srcTaint i0 ⦃ b =>
      b = true ↔
        ∀ l ∈ srcTaint.items.val,
          (∀ p ∈ st.pending.entries.val, p.2.agent = rcv → confRecordC bg l p) ∧
          (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
            confLeC l p.2.policy.conf_clearance = true) ⦄ := by
  unfold transitions.cross_holds_loop0
  let inv := fun (i : Usize) (ok : Bool) => ok = true ↔
    ∀ l ∈ srcTaint.items.val.take i.val,
      (∀ p ∈ st.pending.entries.val, p.2.agent = rcv → confRecordC bg l p) ∧
      (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
        confLeC l p.2.policy.conf_clearance = true)
  apply loop.spec_decr_nat
    (measure := fun p => srcTaint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ srcTaint.items.val.length ∧ inv p.2 p.1)
  · rintro ⟨ok, i⟩ ⟨hi, hinv⟩
    simp only [transitions.cross_holds_loop0.body, collections.VecSet.len,
      collections.VecSet.at, alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < srcTaint.items.val.length := by scalar_tac
      simp only [inv] at hinv
      step as ⟨l, hlEq⟩
      obtain ⟨bConf, hbConfEq, hbConf⟩ := spec_imp_exists
        (ingestConfHold_spec st bg rcv l hnd)
      rw [hbConfEq]
      simp only [bind_tc_ok]
      have htk :
          (∀ x ∈ srcTaint.items.val.take (i.val + 1),
            (∀ p ∈ st.pending.entries.val, p.2.agent = rcv → confRecordC bg x p) ∧
            (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
              confLeC x p.2.policy.conf_clearance = true)) ↔
          ((∀ x ∈ srcTaint.items.val.take i.val,
            (∀ p ∈ st.pending.entries.val, p.2.agent = rcv → confRecordC bg x p) ∧
            (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
              confLeC x p.2.policy.conf_clearance = true)) ∧
            (∀ p ∈ st.pending.entries.val, p.2.agent = rcv → confRecordC bg l p) ∧
            (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
              confLeC l p.2.policy.conf_clearance = true)) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hlEq]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), (hh l (Or.inr rfl)).1,
            (hh l (Or.inr rfl)).2⟩
        · rintro ⟨hpre, hconf, hclear⟩ x (hx | hx)
          · exact hpre x hx
          · subst hx
            exact ⟨hconf, hclear⟩
      by_cases hconf : ∀ p ∈ st.pending.entries.val,
          p.2.agent = rcv → confRecordC bg l p
      · have hbConfT : bConf = true := hbConf.mpr hconf
        simp only [hbConfT, reduceIte]
        obtain ⟨bClear, hbClearEq, hbClear⟩ := spec_imp_exists
          (ingestClearHold_spec st rcv l hnd)
        rw [hbClearEq]
        simp only [bind_tc_ok]
        by_cases hclear : ∀ p ∈ st.pending.entries.val,
            p.2.agent = rcv → confLeC l p.2.policy.conf_clearance = true
        · have hbClearT : bClear = true := hbClear.mpr hclear
          simp only [hbClearT, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [inv]
          rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
          exact ⟨fun hok => ⟨hok, hconf, hclear⟩, fun hall => hall.1⟩
        · have hbClearF : bClear = false := by
            rw [← Bool.not_eq_true]
            exact fun ht => hclear (hbClear.mp ht)
          simp only [hbClearF, Bool.false_eq_true, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simp only [inv]
          rw [show i2.val = i.val + 1 from by scalar_tac, htk]
          constructor
          · intro hf
            contradiction
          · rintro ⟨_, _, hc⟩
            exact absurd hc hclear
      · have hbConfF : bConf = false := by
          rw [← Bool.not_eq_true]
          exact fun ht => hconf (hbConf.mp ht)
        simp only [hbConfF, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        simp only [inv]
        rw [show i2.val = i.val + 1 from by scalar_tac, htk]
        constructor
        · intro hf
          contradiction
        · rintro ⟨_, hc, _⟩
          exact absurd hc hconf
    case isFalse h =>
      have hi : i.val = srcTaint.items.val.length := by scalar_tac
      simp only [spec_ok, inv, hi, List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, hstart⟩

theorem crossHoldsLoop1_spec (st : state.KernelState) (okStart : Bool)
    (rcv : types.AgentId) (srcInteg : collections.VecSet types.IntegLevel)
    (hnd : (st.pending.entries.val.map Prod.fst).Nodup)
    (ok0 : Bool) (i0 : Usize) (hi0 : i0.val ≤ srcInteg.items.val.length)
    (hstart : ok0 = true ↔ okStart = true ∧
      ∀ l ∈ srcInteg.items.val.take i0.val,
        ∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
          (integLeC p.2.policy.integ_floor l = true ∨
            (integLeC p.2.policy.integ_inspect l = true ∧ vouchedC p.2 = true))) :
    transitions.cross_holds_loop1 st.agent_active st.agent_parent st.agent_cap st.taint_levels
      st.integ_levels st.pending st.challenges st.consumed_ids st.consumed_attestations
      st.consumed_crossings st.crossing_grants st.tool_registered rcv ok0 srcInteg i0 ⦃ b =>
      b = true ↔ okStart = true ∧
        ∀ l ∈ srcInteg.items.val,
          ∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
            (integLeC p.2.policy.integ_floor l = true ∨
              (integLeC p.2.policy.integ_inspect l = true ∧ vouchedC p.2 = true)) ⦄ := by
  unfold transitions.cross_holds_loop1
  let inv := fun (i : Usize) (ok : Bool) => ok = true ↔ okStart = true ∧
    ∀ l ∈ srcInteg.items.val.take i.val,
      ∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
        (integLeC p.2.policy.integ_floor l = true ∨
          (integLeC p.2.policy.integ_inspect l = true ∧ vouchedC p.2 = true))
  apply loop.spec_decr_nat
    (measure := fun p => srcInteg.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ srcInteg.items.val.length ∧ inv p.2 p.1)
  · rintro ⟨ok, i⟩ ⟨hi, hinv⟩
    simp only [transitions.cross_holds_loop1.body, collections.VecSet.len,
      collections.VecSet.at, alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < srcInteg.items.val.length := by scalar_tac
      simp only [inv] at hinv
      step as ⟨l, hlEq⟩
      obtain ⟨bInteg, hbIntegEq, hbInteg⟩ := spec_imp_exists
        (ingestIntegHold_spec st rcv l hnd)
      rw [hbIntegEq]
      simp only [bind_tc_ok]
      have htk :
          (∀ x ∈ srcInteg.items.val.take (i.val + 1),
            ∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
              (integLeC p.2.policy.integ_floor x = true ∨
                (integLeC p.2.policy.integ_inspect x = true ∧ vouchedC p.2 = true))) ↔
          ((∀ x ∈ srcInteg.items.val.take i.val,
            ∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
              (integLeC p.2.policy.integ_floor x = true ∨
                (integLeC p.2.policy.integ_inspect x = true ∧ vouchedC p.2 = true))) ∧
            (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
              (integLeC p.2.policy.integ_floor l = true ∨
                (integLeC p.2.policy.integ_inspect l = true ∧ vouchedC p.2 = true)))) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hlEq]
        constructor
        · intro hh
          exact ⟨fun x hx => hh x (Or.inl hx), hh l (Or.inr rfl)⟩
        · rintro ⟨hpre, hhold⟩ x (hx | hx)
          · exact hpre x hx
          · subst hx
            exact hhold
      by_cases hhold : ∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
          (integLeC p.2.policy.integ_floor l = true ∨
            (integLeC p.2.policy.integ_inspect l = true ∧ vouchedC p.2 = true))
      · have hbIntegT : bInteg = true := hbInteg.mpr hhold
        simp only [hbIntegT, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        simp only [inv]
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        exact ⟨fun hok => ⟨hok.1, hok.2, hhold⟩,
          fun hall => ⟨hall.1, hall.2.1⟩⟩
      · have hbIntegF : bInteg = false := by
          rw [← Bool.not_eq_true]
          exact fun ht => hhold (hbInteg.mp ht)
        simp only [hbIntegF, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        simp only [inv]
        rw [show i2.val = i.val + 1 from by scalar_tac, htk]
        constructor
        · intro hf
          contradiction
        · rintro ⟨_, _, hh⟩
          exact absurd hh hhold
    case isFalse h =>
      have hi : i.val = srcInteg.items.val.length := by scalar_tac
      simp only [spec_ok, inv, hi, List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, hstart⟩


/-- The two source-label scans are exactly the abstract unendorsed receiver-hold guard. -/
theorem unendorsedHolds_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (src rcv : types.AgentId)
    (srcTaint : collections.VecSet types.ConfLevel)
    (hst : ∀ l, vsMem srcTaint l ↔ vmsMemLast st.taint_levels src l)
    (srcInteg : collections.VecSet types.IntegLevel)
    (hsi : ∀ l, vsMem srcInteg l ↔ vmsMemLast st.integ_levels src l) :
    ((∀ l ∈ srcTaint.items.val,
        (∀ p ∈ st.pending.entries.val, p.2.agent = rcv → confRecordC bg l p) ∧
        (∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
          confLeC l p.2.policy.conf_clearance = true)) ∧
      (∀ l ∈ srcInteg.items.val,
        ∀ p ∈ st.pending.entries.val, p.2.agent = rcv →
          (integLeC p.2.policy.integ_floor l = true ∨
            (integLeC p.2.policy.integ_inspect l = true ∧ vouchedC p.2 = true)))) ↔
      ((∀ L, a.taint_levels src L →
          Tzimtzum.ingestConfHold a rcv L ∧ Tzimtzum.ingestClearHold a rcv L) ∧
        (∀ L, a.integ_levels src L → Tzimtzum.ingestIntegHold a rcv L)) := by
  constructor
  · rintro ⟨hconf, hinteg⟩
    constructor
    · intro L hL
      have hm : confC L ∈ srcTaint.items.val :=
        (hst (confC L)).mpr ((hR.taint src L).mp hL)
      obtain ⟨hc, hclear⟩ := hconf (confC L) hm
      exact ⟨by
          simpa using (ingestConfHold_bridge st bg a hR rcv (confC L)).mp hc,
        by simpa using (ingestClearHold_bridge st bg a hR rcv (confC L)).mp hclear⟩
    · intro L hL
      have hm : integC L ∈ srcInteg.items.val :=
        (hsi (integC L)).mpr ((hR.integ src L).mp hL)
      have hh := hinteg (integC L) hm
      simpa using (ingestIntegHold_bridge st bg a hR rcv (integC L)).mp hh
  · rintro ⟨hconf, hinteg⟩
    constructor
    · intro l hl
      have hL : a.taint_levels src (confA l) :=
        (hR.taint src (confA l)).mpr (by simpa using (hst l).mp hl)
      obtain ⟨hc, hclear⟩ := hconf (confA l) hL
      exact ⟨by
          simpa using (ingestConfHold_bridge st bg a hR rcv l).mpr hc,
        by simpa using (ingestClearHold_bridge st bg a hR rcv l).mpr hclear⟩
    · intro l hl
      have hL : a.integ_levels src (integA l) :=
        (hR.integ src (integA l)).mpr (by simpa using (hsi l).mp hl)
      simpa using (ingestIntegHold_bridge st bg a hR rcv l).mpr (hinteg (integA l) hL)

/-- Receiver-hold agreement for the endorsed branch. -/
theorem crossHoldsEndorsed_spec (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) (hq : crossInputRel qA q) :
    transitions.cross_holds st bg q .Endorsed ⦃ b =>
      b = true ↔ Tzimtzum.crossHolds a qA .endorsed ⦄ := by
  obtain ⟨_, hrcv, _, _, _, _, _, _, _, _, hrelConf, hrelInteg⟩ := hq
  simp only [transitions.cross_holds]
  obtain ⟨b, hbEq, hb⟩ := spec_imp_exists
    (ingestHoldsAbs_spec st bg a hR q.rcv q.released_conf q.released_integ)
  rw [hbEq]
  simp only [spec_ok]
  simp only [Tzimtzum.crossHolds_iff]
  rw [hrcv, hrelConf, hrelInteg]
  simpa using hb

/-- Receiver-hold agreement for the unendorsed branch. -/
theorem crossHoldsUnendorsed_spec (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) (hq : crossInputRel qA q) :
    transitions.cross_holds st bg q .Unendorsed ⦃ b =>
      b = true ↔ Tzimtzum.crossHolds a qA .unendorsed ⦄ := by
  obtain ⟨hsrc, hrcv, _, _, _, _, _, _, _, _, _, _⟩ := hq
  simp only [transitions.cross_holds]
  obtain ⟨srcTaint, hstEq, hst⟩ := spec_imp_exists
    (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec st.taint_levels q.src)
  rw [hstEq]
  simp only [bind_tc_ok]
  obtain ⟨bConf, hbConfEq, hbConf⟩ := spec_imp_exists
    (crossHoldsLoop0_spec st bg q.rcv srcTaint hR.ndPending true 0#usize
      (by simp) (by simp))
  rw [hbConfEq]
  simp only [bind_tc_ok]
  obtain ⟨srcInteg, hsiEq, hsi⟩ := spec_imp_exists
    (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_clone_spec st.integ_levels q.src)
  rw [hsiEq]
  simp only [bind_tc_ok]
  obtain ⟨b, hbEq, hb⟩ := spec_imp_exists
    (crossHoldsLoop1_spec st bConf q.rcv srcInteg hR.ndPending bConf 0#usize
      (by simp) (by simp))
  rw [hbEq]
  simp only [spec_ok]
  rw [hb, hbConf, unendorsedHolds_bridge st bg a hR q.src q.rcv srcTaint hst srcInteg hsi]
  simp only [Tzimtzum.crossHolds_iff]
  rw [hsrc, hrcv]
  simp

/-- Receiver-hold agreement for the fail branch. -/
theorem crossHoldsFail_spec (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) :
    transitions.cross_holds st bg q .Fail ⦃ b =>
      b = true ↔ Tzimtzum.crossHolds a qA .fail ⦄ := by
  simp [transitions.cross_holds, Tzimtzum.crossHolds_iff]


/-! ## Label-copy post state -/

def copyRel {L : Type} (before after : collections.VecMap types.AgentId (collections.VecSet L))
    (rcv : types.AgentId) (xs : List L) : Prop :=
  ∀ A l, vmsMemLast after A l ↔
    vmsMemLast before A l ∨ (A = rcv ∧ ∃ x ∈ xs, l = x)

/-- Capacities needed at each actual append-like write in a source-set copy. -/
def CopyCapacity {L : Type} (before : collections.VecMap types.AgentId (collections.VecSet L))
    (rcv : types.AgentId) (src : collections.VecSet L) : Prop :=
  ∀ (i : Usize) (vm : collections.VecMap types.AgentId (collections.VecSet L)),
    i.val < src.items.val.length → copyRel before vm rcv (src.items.val.take i.val) →
      vm.entries.val.length < Usize.max ∧
      ∀ p ∈ vm.entries.val, p.2.items.val.length < Usize.max

theorem crossOutputCopyConfLoop2_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.ConfLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop2 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  unfold transitions.cross_output_loop2
  apply loop.spec_decr_nat
    (measure := fun p => src.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ src.items.val.length ∧
      copyRel before p.1 rcv (src.items.val.take p.2.val) ∧ vmNodupKeys p.1)
  · rintro ⟨vm, i⟩ ⟨hi, hrel, hvmnd⟩
    simp only [transitions.cross_output_loop2.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < src.items.val.length := by scalar_tac
      step as ⟨l, hl⟩
      simp only [agentId_clone_spec, bind_tc_ok]
      obtain ⟨hcapE, hcapS⟩ := hcap i vm hlt hrel
      obtain ⟨vm', hvmEq, hvmRel⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec vm rcv l hcapE hcapS)
      rw [hvmEq]
      simp only [bind_tc_ok]
      obtain ⟨vmnd, hvmndEq, hvmndPost⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec vm rcv l hcapE hcapS)
      have hsame : vmnd = vm' := Result.ok.inj (hvmndEq.symm.trans hvmEq)
      have hvmnd' : vmNodupKeys vm' := by rw [← hsame]; exact hvmndPost hvmnd
      step*
      refine ⟨by scalar_tac, ?_, hvmnd', by scalar_tac⟩
      intro A x
      rw [show i2.val = i.val + 1 from by scalar_tac, hvmRel A x, hrel A x]
      have htake : (∃ y ∈ src.items.val.take (i.val + 1), x = y) ↔
          (∃ y ∈ src.items.val.take i.val, x = y) ∨ x = l := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hl]
        aesop
      rw [htake]
      aesop
    case isFalse h =>
      have hi' : i.val = src.items.val.length := by scalar_tac
      simp only [spec_ok]
      exact ⟨by simpa [hi'] using hrel, hvmnd⟩
  · exact ⟨by simp, by
      intro A l
      simp [copyRel], hnd⟩

theorem crossOutputCopyIntegLoop3_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.IntegLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop3 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  unfold transitions.cross_output_loop3
  apply loop.spec_decr_nat
    (measure := fun p => src.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ src.items.val.length ∧
      copyRel before p.1 rcv (src.items.val.take p.2.val) ∧ vmNodupKeys p.1)
  · rintro ⟨vm, i⟩ ⟨hi, hrel, hvmnd⟩
    simp only [transitions.cross_output_loop3.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < src.items.val.length := by scalar_tac
      step as ⟨l, hl⟩
      simp only [agentId_clone_spec, bind_tc_ok]
      obtain ⟨hcapE, hcapS⟩ := hcap i vm hlt hrel
      obtain ⟨vm', hvmEq, hvmRel⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec vm rcv l hcapE hcapS)
      rw [hvmEq]
      simp only [bind_tc_ok]
      obtain ⟨vmnd, hvmndEq, hvmndPost⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec vm rcv l hcapE hcapS)
      have hsame : vmnd = vm' := Result.ok.inj (hvmndEq.symm.trans hvmEq)
      have hvmnd' : vmNodupKeys vm' := by rw [← hsame]; exact hvmndPost hvmnd
      step*
      refine ⟨by scalar_tac, ?_, hvmnd', by scalar_tac⟩
      intro A x
      rw [show i2.val = i.val + 1 from by scalar_tac, hvmRel A x, hrel A x]
      have htake : (∃ y ∈ src.items.val.take (i.val + 1), x = y) ↔
          (∃ y ∈ src.items.val.take i.val, x = y) ∨ x = l := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, ← hl]
        aesop
      rw [htake]
      aesop
    case isFalse h =>
      have hi' : i.val = src.items.val.length := by scalar_tac
      simp only [spec_ok]
      exact ⟨by simpa [hi'] using hrel, hvmnd⟩
  · exact ⟨by simp, by
      intro A l
      simp [copyRel], hnd⟩


-- Extraction duplicates the same source-copy loops in each syntactic successful path.
theorem crossOutputCopyConfLoop4_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.ConfLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop4 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop4, transitions.cross_output_loop4.body,
    transitions.cross_output_loop2, transitions.cross_output_loop2.body] using
    crossOutputCopyConfLoop2_spec before rcv src hcap hnd

theorem crossOutputCopyIntegLoop5_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.IntegLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop5 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop5, transitions.cross_output_loop5.body,
    transitions.cross_output_loop3, transitions.cross_output_loop3.body] using
    crossOutputCopyIntegLoop3_spec before rcv src hcap hnd

theorem crossOutputCopyConfLoop6_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.ConfLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop6 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop6, transitions.cross_output_loop6.body,
    transitions.cross_output_loop2, transitions.cross_output_loop2.body] using
    crossOutputCopyConfLoop2_spec before rcv src hcap hnd

theorem crossOutputCopyIntegLoop7_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.IntegLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop7 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop7, transitions.cross_output_loop7.body,
    transitions.cross_output_loop3, transitions.cross_output_loop3.body] using
    crossOutputCopyIntegLoop3_spec before rcv src hcap hnd

theorem crossOutputCopyConfLoop8_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.ConfLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop8 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop8, transitions.cross_output_loop8.body,
    transitions.cross_output_loop2, transitions.cross_output_loop2.body] using
    crossOutputCopyConfLoop2_spec before rcv src hcap hnd

theorem crossOutputCopyIntegLoop9_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.IntegLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop9 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop9, transitions.cross_output_loop9.body,
    transitions.cross_output_loop3, transitions.cross_output_loop3.body] using
    crossOutputCopyIntegLoop3_spec before rcv src hcap hnd

theorem crossOutputCopyConfLoop10_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.ConfLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop10 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop10, transitions.cross_output_loop10.body,
    transitions.cross_output_loop2, transitions.cross_output_loop2.body] using
    crossOutputCopyConfLoop2_spec before rcv src hcap hnd

theorem crossOutputCopyIntegLoop11_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.IntegLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop11 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop11, transitions.cross_output_loop11.body,
    transitions.cross_output_loop3, transitions.cross_output_loop3.body] using
    crossOutputCopyIntegLoop3_spec before rcv src hcap hnd

theorem crossOutputCopyConfLoop12_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.ConfLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop12 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop12, transitions.cross_output_loop12.body,
    transitions.cross_output_loop2, transitions.cross_output_loop2.body] using
    crossOutputCopyConfLoop2_spec before rcv src hcap hnd

theorem crossOutputCopyIntegLoop13_spec
    (before : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel))
    (rcv : types.AgentId) (src : collections.VecSet types.IntegLevel)
    (hcap : CopyCapacity before rcv src) (hnd : vmNodupKeys before) :
    transitions.cross_output_loop13 before rcv src 0#usize ⦃ vm =>
      copyRel before vm rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
  simpa [transitions.cross_output_loop13, transitions.cross_output_loop13.body,
    transitions.cross_output_loop3, transitions.cross_output_loop3.body] using
    crossOutputCopyIntegLoop3_spec before rcv src hcap hnd


/-! ## Canonical abstract post and `R` assembly -/

noncomputable def crossStateAbs (a : AbsState)
    (q : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash)
    (branch : Tzimtzum.CrossBranch) (dispo : Tzimtzum.Disposition) : AbsState :=
  { a with
    taint_levels := fun A L =>
      a.taint_levels A L
      ∨ (branch = .endorsed ∧ A = q.rcv ∧ L = q.released_conf)
      ∨ (branch = .unendorsed ∧ A = q.rcv ∧ a.taint_levels q.src L)
    integ_levels := fun A L =>
      a.integ_levels A L
      ∨ (branch = .endorsed ∧ A = q.rcv ∧ L = q.released_integ)
      ∨ (branch = .unendorsed ∧ A = q.rcv ∧ a.integ_levels q.src L)
    consumed_crossings := fun X => a.consumed_crossings X ∨ X = q.crossing
    consumed_attestations := fun X =>
      a.consumed_attestations X
      ∨ (branch = .endorsed ∧ ∃ e, q.evidence = some e ∧ X = e.id)
    crossing_grants := if branch = .endorsed then
      Tzimtzum.decrementGrantAt a.crossing_grants q.rcv q.assignment
      else a.crossing_grants
    pending := if dispo = .monitor_bypassed then
      Tzimtzum.demoteAllOf a.pending q.rcv else a.pending }

 theorem crossStateAbs_next (a : AbsState)
    (q : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash)
    (branch : Tzimtzum.CrossBranch) (dispo : Tzimtzum.Disposition) :
    (Tzimtzum.cross_output q branch dispo).next a (crossStateAbs a q branch dispo) := by
  simp [Tzimtzum.cross_output, crossStateAbs]

/-- Assemble `R` once each concrete field has been related to the canonical crossing post. -/
theorem cross_post_R (st st' : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a)
    (q : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash)
    (branch : Tzimtzum.CrossBranch) (dispo : Tzimtzum.Disposition)
    (hactive : st'.agent_active = st.agent_active)
    (hparent : st'.agent_parent = st.agent_parent)
    (hcap : st'.agent_cap = st.agent_cap)
    (htool : st'.tool_registered = st.tool_registered)
    (hchal : st'.challenges = st.challenges)
    (hids : st'.consumed_ids = st.consumed_ids)
    (htaint : ∀ A L,
      (crossStateAbs a q branch dispo).taint_levels A L ↔
        vmsMemLast st'.taint_levels A (confC L))
    (hinteg : ∀ A L,
      (crossStateAbs a q branch dispo).integ_levels A L ↔
        vmsMemLast st'.integ_levels A (integC L))
    (hpending : ∀ I,
      optRel pendingRel ((crossStateAbs a q branch dispo).pending I) (pendingC st' I))
    (hatt : ∀ Att,
      (crossStateAbs a q branch dispo).consumed_attestations Att ↔
        vsMem st'.consumed_attestations Att)
    (hcross : ∀ X,
      (crossStateAbs a q branch dispo).consumed_crossings X ↔
        vsMem st'.consumed_crossings X)
    (hgrants : ∀ A D,
      optRel crossingGrantRel ((crossStateAbs a q branch dispo).crossing_grants A D)
        (crossingGrantC st' { agent := A, assignment := D }))
    (hndT : vmNodupKeys st'.taint_levels)
    (hndI : vmNodupKeys st'.integ_levels)
    (hndP : vmNodupKeys st'.pending)
    (hndG : vmNodupKeys st'.crossing_grants) :
    R st' bg (crossStateAbs a q branch dispo) := by
  refine
    { root := hR.root, mode := hR.mode
      active := ?_, tool_reg := ?_, parent := ?_, cap := ?_
      taint := htaint, integ := hinteg, pending := hpending
      challenges := ?_, grants := hgrants
      consumedIds := ?_, consumedAtt := hatt, consumedCross := hcross
      flowAllows := hR.flowAllows, flowInspects := hR.flowInspects
      ndParent := ?_, ndCap := ?_, ndTaint := hndT, ndInteg := hndI
      ndPending := hndP, ndChallenges := ?_, ndGrants := hndG }
  · intro x; rw [hactive]; exact hR.active x
  · intro t; rw [htool]; exact hR.tool_reg t
  · intro C P; rw [hparent]; exact hR.parent C P
  · intro N C; rw [hcap]; exact hR.cap N C
  · intro I
    show optRel challengeRel (a.challenges I) (challengeC st' I)
    unfold challengeC
    rw [hchal]
    exact hR.challenges I
  · intro I
    rw [hids]
    exact hR.consumedIds I
  · rw [hparent]
    exact hR.ndParent
  · rw [hcap]
    exact hR.ndCap
  · rw [hchal]
    exact hR.ndChallenges


/-! ## Grant decrement bridge -/

theorem decrementGrantAt_spec (st : state.KernelState) (a : AbsState)
    (hgr : ∀ A D, optRel crossingGrantRel (a.crossing_grants A D)
      (crossingGrantC st { agent := A, assignment := D }))
    (hnd : vmNodupKeys st.crossing_grants) (agent : types.AgentId)
    (assignment : types.AssignmentDigest) (gA : Tzimtzum.CrossingGrant)
    (g : types.CrossingGrant)
    (hA : a.crossing_grants agent assignment = some gA)
    (hC : crossingGrantC st { agent := agent, assignment := assignment } = some g)
    (hrel : crossingGrantRel gA g) (hpos : 0 < gA.remaining)
    (hcap : st.crossing_grants.entries.val.length < Usize.max) :
    state.KernelState.decrement_grant_at st agent assignment ⦃ st' =>
      (∀ A D,
        optRel crossingGrantRel
          (Tzimtzum.decrementGrantAt a.crossing_grants agent assignment A D)
          (crossingGrantC st' { agent := A, assignment := D }))
      ∧ vmNodupKeys st'.crossing_grants
      ∧ st'.agent_active = st.agent_active
      ∧ st'.agent_parent = st.agent_parent
      ∧ st'.agent_cap = st.agent_cap
      ∧ st'.taint_levels = st.taint_levels
      ∧ st'.integ_levels = st.integ_levels
      ∧ st'.pending = st.pending
      ∧ st'.challenges = st.challenges
      ∧ st'.consumed_ids = st.consumed_ids
      ∧ st'.consumed_attestations = st.consumed_attestations
      ∧ st'.consumed_crossings = st.consumed_crossings
      ∧ st'.tool_registered = st.tool_registered ⦄ := by
  unfold state.KernelState.decrement_grant_at
  simp only [agentId_clone_spec, assignmentDigest_clone_spec, bind_tc_ok]
  obtain ⟨og, hogEq, hog⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.CrossingKey.Insts.CoreCloneClone
      types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
      types.CrossingGrant.Insts.CoreCloneClone (fun x => rfl)
      st.crossing_grants { agent := agent, assignment := assignment })
  have hogSome : og = some g := by
    unfold crossingGrantC at hC
    rw [hog, hC]
  rw [hogEq]
  simp only [bind_tc_ok, hogSome]
  have hgpos : 0 < g.remaining.val := by rw [← hrel.1]; exact hpos
  step as ⟨remaining, hremaining⟩
  obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.CrossingKey.Insts.CoreCloneClone
      types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
      types.CrossingGrant.Insts.CoreCloneClone st.crossing_grants
      { agent := agent, assignment := assignment } { g with remaining := remaining } hcap)
  rw [hvmEq]
  simp only [bind_tc_ok, spec_ok]
  obtain ⟨vmnd, hvmndEq, hvmnd⟩ := spec_imp_exists
    (vecMapInsert_nodup types.CrossingKey.Insts.CoreCloneClone
      types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
      types.CrossingGrant.Insts.CoreCloneClone st.crossing_grants
      { agent := agent, assignment := assignment } { g with remaining := remaining } hcap)
  have hsame : vmnd = vm := Result.ok.inj (hvmndEq.symm.trans hvmEq)
  constructor
  · intro A D
    unfold crossingGrantC
    rw [hvm]
    by_cases hk : (A = agent ∧ D = assignment)
    · obtain ⟨rfl, rfl⟩ := hk
      rw [Tzimtzum.decrementGrantAt_self a.crossing_grants A D gA hA]
      simp only [if_pos rfl, Option.map_some, optRel]
      constructor
      · rw [hrel.1, hremaining]
      · exact hrel.2
    · have hkey : ({ agent := A, assignment := D } : types.CrossingKey) ≠
          { agent := agent, assignment := assignment } := by
        intro heq
        apply hk
        exact ⟨congrArg types.CrossingKey.agent heq,
          congrArg types.CrossingKey.assignment heq⟩
      simp only [hkey, if_false]
      rw [Tzimtzum.decrementGrantAt_other]
      · exact hgr A D
      · intro hAD
        exact hk ⟨hAD.1, hAD.2⟩
  · refine ⟨?_, by simp⟩
    rw [← hsame]
    exact hvmnd hnd


/-! ## Shared successful tail -/

noncomputable def crossTail
    (copyConf : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel) →
      types.AgentId → collections.VecSet types.ConfLevel → Result
        (collections.VecMap types.AgentId (collections.VecSet types.ConfLevel)))
    (copyInteg : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel) →
      types.AgentId → collections.VecSet types.IntegLevel → Result
        (collections.VecMap types.AgentId (collections.VecSet types.IntegLevel)))
    (st : state.KernelState) (q : types.CrossInput) (branch : types.CrossBranch)
    (dispo : types.Disposition) :
    Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError) := do
  let (taint, integ) ← match branch with
    | .Endorsed => do
      let rcv ← types.AgentId.Insts.CoreCloneClone.clone q.rcv
      let taint ← collections.VecMapKVecSet.insert_into
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        st.taint_levels rcv q.released_conf
      let integ ← collections.VecMapKVecSet.insert_into
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        st.integ_levels rcv q.released_integ
      ok (taint, integ)
    | .Unendorsed => do
      let srcTaint ← collections.VecMapKVecSet.get_set_or_empty
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        st.taint_levels q.src
      let taint ← copyConf st.taint_levels q.rcv srcTaint
      let srcInteg ← collections.VecMapKVecSet.get_set_or_empty
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        st.integ_levels q.src
      let integ ← copyInteg st.integ_levels q.rcv srcInteg
      ok (taint, integ)
    | .Fail => ok (st.taint_levels, st.integ_levels)
  let crossing ← types.CrossingId.Insts.CoreCloneClone.clone q.crossing
  let consumedCrossings ← collections.VecSet.insert
    types.CrossingId.Insts.CoreCloneClone types.CrossingId.Insts.CoreCmpPartialEqCrossingId
    st.consumed_crossings crossing
  let isEndorsed ← types.CrossBranch.Insts.CoreCmpPartialEqCrossBranch.eq branch .Endorsed
  let st1 ← if isEndorsed then do
      let consumedAttestations ← match q.evidence with
        | none => ok st.consumed_attestations
        | some e => do
          let att ← types.AttestationId.Insts.CoreCloneClone.clone e.id
          collections.VecSet.insert types.AttestationId.Insts.CoreCloneClone
            types.AttestationId.Insts.CoreCmpPartialEqAttestationId st.consumed_attestations att
      state.KernelState.decrement_grant_at
        { st with
          taint_levels := taint
          integ_levels := integ
          consumed_attestations := consumedAttestations
          consumed_crossings := consumedCrossings } q.rcv q.assignment
    else ok { st with
      taint_levels := taint
      integ_levels := integ
      consumed_crossings := consumedCrossings }
  let isBypassed ← types.Disposition.Insts.CoreCmpPartialEqDisposition.eq dispo .MonitorBypassed
  let st2 ← if isBypassed then
      state.KernelState.demote_all_of st1 q.rcv else ok st1
  ok (.Ok (st2, .CrossOutput q.src q.rcv q.crossing branch dispo))


/-- Shared post-state proof for every successful crossing tail. -/
theorem crossTail_preservesR
    (copyConf : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel) →
      types.AgentId → collections.VecSet types.ConfLevel → Result
        (collections.VecMap types.AgentId (collections.VecSet types.ConfLevel)))
    (copyInteg : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel) →
      types.AgentId → collections.VecSet types.IntegLevel → Result
        (collections.VecMap types.AgentId (collections.VecSet types.IntegLevel)))
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) (hR : R st bg a)
    (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) (hq : crossInputRel qA q)
    (branch : types.CrossBranch) (dispo : types.Disposition)
    (hguard : (Tzimtzum.cross_output qA (crossBranchA branch) (dispA dispo)).guard a)
    (hcopyConf : branch = .Unendorsed → ∀ src,
      collections.VecMapKVecSet.get_set_or_empty
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        st.taint_levels q.src = .ok src →
      copyConf st.taint_levels q.rcv src ⦃ vm =>
        copyRel st.taint_levels vm q.rcv src.items.val ∧ vmNodupKeys vm ⦄)
    (hcopyInteg : branch = .Unendorsed → ∀ src,
      collections.VecMapKVecSet.get_set_or_empty
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        st.integ_levels q.src = .ok src →
      copyInteg st.integ_levels q.rcv src ⦃ vm =>
        copyRel st.integ_levels vm q.rcv src.items.val ∧ vmNodupKeys vm ⦄)
    (hcapTE : branch = .Endorsed → st.taint_levels.entries.val.length < Usize.max)
    (hcapTS : branch = .Endorsed →
      ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIE : branch = .Endorsed → st.integ_levels.entries.val.length < Usize.max)
    (hcapIS : branch = .Endorsed →
      ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapCross : st.consumed_crossings.items.val.length < Usize.max)
    (hcapAtt : branch = .Endorsed → st.consumed_attestations.items.val.length < Usize.max)
    (hcapGrant : branch = .Endorsed → st.crossing_grants.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : crossTail copyConf copyInteg st q branch dispo = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.cross_output qA (crossBranchA branch) (dispA dispo)).next a a'
      ∧ R st' bg a' := by
  obtain ⟨hsrcQ, hrcvQ, hcrossQ, houtQ, hdescQ, hfallQ, htintegQ, htconfQ,
    hassignQ, hevidenceQ, hrelConfQ, hrelIntegQ⟩ := hq
  rcases hguard with ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, hselE, hselU, hselF,
    hboundI, hboundC, hboundNC, hnotBlocked, hpermitted, hbypass⟩
  cases branch <;> cases dispo
  all_goals try { exfalso; exact hnotBlocked rfl }
  case Endorsed.Permitted =>
    have hEnd := hselE rfl
    obtain ⟨⟨eA, hqAe, hePos, heFresh, heOut, heSrc, heRcv, heDesc, heAssign⟩,
      gA, hgA, hgPos⟩ := hEnd
    cases hqe : q.evidence with
    | none => simp [hqAe, hqe, optRel] at hevidenceQ
    | some e =>
      have heRel : conformanceAttestationRel eA e := by
        simpa [hqAe, hqe, optRel] using hevidenceQ
      simp only [crossTail, agentId_clone_spec, bind_tc_ok, crossingId_clone_spec,
        crossBranch_eq_spec, decide_true, reduceIte, attestationId_clone_spec,
        disposition_eq_spec, reduceCtorEq, decide_false, Bool.false_eq_true, hqe] at hok
      obtain ⟨vmT, hvmTEq, hvmT⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels q.rcv q.released_conf
          (hcapTE rfl) (hcapTS rfl))
      rw [hvmTEq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨vmTnd, hvmTndEq, hvmTndPost⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels q.rcv q.released_conf
          (hcapTE rfl) (hcapTS rfl))
      have hvmTsame : vmTnd = vmT := Result.ok.inj (hvmTndEq.symm.trans hvmTEq)
      have hvmTnd : vmNodupKeys vmT := by rw [← hvmTsame]; exact hvmTndPost hR.ndTaint
      obtain ⟨vmI, hvmIEq, hvmI⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels q.rcv q.released_integ
          (hcapIE rfl) (hcapIS rfl))
      rw [hvmIEq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨vmInd, hvmIndEq, hvmIndPost⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels q.rcv q.released_integ
          (hcapIE rfl) (hcapIS rfl))
      have hvmIsame : vmInd = vmI := Result.ok.inj (hvmIndEq.symm.trans hvmIEq)
      have hvmInd : vmNodupKeys vmI := by rw [← hvmIsame]; exact hvmIndPost hR.ndInteg
      obtain ⟨crossed, hcrossEq, hcrossMem⟩ := spec_imp_exists
        (vecSetInsert_spec types.CrossingId.Insts.CoreCloneClone
          types.CrossingId.Insts.CoreCmpPartialEqCrossingId crossingId_eq_spec
          st.consumed_crossings q.crossing hcapCross)
      rw [hcrossEq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨atts, hattEq, hattMem⟩ := spec_imp_exists
        (vecSetInsert_spec types.AttestationId.Insts.CoreCloneClone
          types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
          st.consumed_attestations e.id (hcapAtt rfl))
      rw [hattEq] at hok
      simp only [bind_tc_ok] at hok
      let base : state.KernelState :=
        { st with
          taint_levels := vmT
          integ_levels := vmI
          consumed_attestations := atts
          consumed_crossings := crossed }
      have hbaseGr : ∀ A D, optRel crossingGrantRel (a.crossing_grants A D)
          (crossingGrantC base { agent := A, assignment := D }) := by
        intro A D
        exact hR.grants A D
      obtain ⟨g, hstCg, hgRel⟩ : ∃ g,
          crossingGrantC st { agent := q.rcv, assignment := q.assignment } = some g ∧
            crossingGrantRel gA g := by
        have hgr := hR.grants qA.rcv qA.assignment
        rw [hgA, hrcvQ, hassignQ] at hgr
        cases hc : crossingGrantC st { agent := q.rcv, assignment := q.assignment } with
        | none => rw [hc] at hgr; simp [optRel] at hgr
        | some g =>
          rw [hc] at hgr
          exact ⟨g, rfl, hgr⟩
      have hbaseCg : crossingGrantC base { agent := q.rcv, assignment := q.assignment } =
          some g := by
        unfold crossingGrantC at hstCg ⊢
        exact hstCg
      obtain ⟨s1, hs1Eq, hs1gr, hs1nd, hs1a, hs1p, hs1c, hs1t, hs1i, hs1pend,
        hs1ch, hs1ci, hs1ca, hs1cc, hs1tr⟩ := spec_imp_exists
        (decrementGrantAt_spec base a hbaseGr hR.ndGrants q.rcv q.assignment gA g
          (by simpa [hrcvQ, hassignQ] using hgA) hbaseCg hgRel hgPos (hcapGrant rfl))
      change (do
        let s1 ← state.KernelState.decrement_grant_at base q.rcv q.assignment
        ok (core.result.Result.Ok (s1, event.KernelAction.CrossOutput
          q.src q.rcv q.crossing .Endorsed .Permitted))) =
          Result.ok (core.result.Result.Ok (st', ev)) at hok
      rw [hs1Eq] at hok
      simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq,
        Prod.mk.injEq] at hok
      obtain ⟨rfl, _⟩ := hok
      let a' := crossStateAbs a qA .endorsed .permitted
      refine ⟨a', crossStateAbs_next a qA .endorsed .permitted, ?_⟩
      apply cross_post_R st s1 bg a hR qA .endorsed .permitted
      · exact hs1a.trans rfl
      · exact hs1p.trans rfl
      · exact hs1c.trans rfl
      · exact hs1tr.trans rfl
      · exact hs1ch.trans rfl
      · exact hs1ci.trans rfl
      · intro A L
        simp only [a', crossStateAbs, reduceCtorEq, true_and, true_or, false_and,
          false_or]
        rw [hs1t]
        simpa [hrcvQ, hrelConfQ] using
          ingest_taint_clause st bg a hR q.rcv q.released_conf vmT hvmT A L
      · intro A L
        simp only [a', crossStateAbs, reduceCtorEq, true_and, true_or, false_and,
          false_or]
        rw [hs1i]
        simpa [hrcvQ, hrelIntegQ] using
          ingest_integ_clause st bg a hR q.rcv q.released_integ vmI hvmI A L
      · intro I
        simp only [a', crossStateAbs, reduceCtorEq, if_false]
        unfold pendingC
        rw [hs1pend]
        exact hR.pending I
      · intro Att
        simp only [a', crossStateAbs, reduceCtorEq, true_and, true_or]
        rw [hs1ca, hattMem, ← hR.consumedAtt Att]
        constructor
        · rintro (hold | ⟨eA', heq, rfl⟩)
          · exact Or.inl hold
          · rw [hqAe] at heq
            injection heq with heq
            subst eA'
            exact Or.inr (by rw [heRel.1])
        · rintro (hold | heq)
          · exact Or.inl hold
          · exact Or.inr ⟨eA, hqAe, by rw [heRel.1]; exact heq⟩
      · intro X
        simp only [a', crossStateAbs]
        rw [hs1cc, hcrossMem, ← hR.consumedCross X, hcrossQ]
      · intro A D
        simp only [a', crossStateAbs, reduceCtorEq, if_pos rfl]
        rw [hrcvQ, hassignQ]
        exact hs1gr A D
      · rw [hs1t]
        exact hvmTnd
      · rw [hs1i]
        exact hvmInd
      · rw [hs1pend]
        exact hR.ndPending
      · exact hs1nd
  case Endorsed.MonitorBypassed =>
    have hEnd := hselE rfl
    obtain ⟨⟨eA, hqAe, hePos, heFresh, heOut, heSrc, heRcv, heDesc, heAssign⟩,
      gA, hgA, hgPos⟩ := hEnd
    cases hqe : q.evidence with
    | none => simp [hqAe, hqe, optRel] at hevidenceQ
    | some e =>
      have heRel : conformanceAttestationRel eA e := by
        simpa [hqAe, hqe, optRel] using hevidenceQ
      simp only [crossTail, agentId_clone_spec, bind_tc_ok, crossingId_clone_spec,
        crossBranch_eq_spec, decide_true, reduceIte, attestationId_clone_spec,
        disposition_eq_spec, reduceCtorEq, decide_false, Bool.false_eq_true, decide_true, hqe] at hok
      obtain ⟨vmT, hvmTEq, hvmT⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels q.rcv q.released_conf
          (hcapTE rfl) (hcapTS rfl))
      rw [hvmTEq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨vmTnd, hvmTndEq, hvmTndPost⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels q.rcv q.released_conf
          (hcapTE rfl) (hcapTS rfl))
      have hvmTsame : vmTnd = vmT := Result.ok.inj (hvmTndEq.symm.trans hvmTEq)
      have hvmTnd : vmNodupKeys vmT := by rw [← hvmTsame]; exact hvmTndPost hR.ndTaint
      obtain ⟨vmI, hvmIEq, hvmI⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels q.rcv q.released_integ
          (hcapIE rfl) (hcapIS rfl))
      rw [hvmIEq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨vmInd, hvmIndEq, hvmIndPost⟩ := spec_imp_exists
        (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels q.rcv q.released_integ
          (hcapIE rfl) (hcapIS rfl))
      have hvmIsame : vmInd = vmI := Result.ok.inj (hvmIndEq.symm.trans hvmIEq)
      have hvmInd : vmNodupKeys vmI := by rw [← hvmIsame]; exact hvmIndPost hR.ndInteg
      obtain ⟨crossed, hcrossEq, hcrossMem⟩ := spec_imp_exists
        (vecSetInsert_spec types.CrossingId.Insts.CoreCloneClone
          types.CrossingId.Insts.CoreCmpPartialEqCrossingId crossingId_eq_spec
          st.consumed_crossings q.crossing hcapCross)
      rw [hcrossEq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨atts, hattEq, hattMem⟩ := spec_imp_exists
        (vecSetInsert_spec types.AttestationId.Insts.CoreCloneClone
          types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
          st.consumed_attestations e.id (hcapAtt rfl))
      rw [hattEq] at hok
      simp only [bind_tc_ok] at hok
      let base : state.KernelState :=
        { st with
          taint_levels := vmT
          integ_levels := vmI
          consumed_attestations := atts
          consumed_crossings := crossed }
      have hbaseGr : ∀ A D, optRel crossingGrantRel (a.crossing_grants A D)
          (crossingGrantC base { agent := A, assignment := D }) := by
        intro A D
        exact hR.grants A D
      obtain ⟨g, hstCg, hgRel⟩ : ∃ g,
          crossingGrantC st { agent := q.rcv, assignment := q.assignment } = some g ∧
            crossingGrantRel gA g := by
        have hgr := hR.grants qA.rcv qA.assignment
        rw [hgA, hrcvQ, hassignQ] at hgr
        cases hc : crossingGrantC st { agent := q.rcv, assignment := q.assignment } with
        | none => rw [hc] at hgr; simp [optRel] at hgr
        | some g =>
          rw [hc] at hgr
          exact ⟨g, rfl, hgr⟩
      have hbaseCg : crossingGrantC base { agent := q.rcv, assignment := q.assignment } =
          some g := by
        unfold crossingGrantC at hstCg ⊢
        exact hstCg
      obtain ⟨s1, hs1Eq, hs1gr, hs1nd, hs1a, hs1p, hs1c, hs1t, hs1i, hs1pend,
        hs1ch, hs1ci, hs1ca, hs1cc, hs1tr⟩ := spec_imp_exists
        (decrementGrantAt_spec base a hbaseGr hR.ndGrants q.rcv q.assignment gA g
          (by simpa [hrcvQ, hassignQ] using hgA) hbaseCg hgRel hgPos (hcapGrant rfl))
      change (do
        let s1 ← state.KernelState.decrement_grant_at base q.rcv q.assignment
        let s2 ← state.KernelState.demote_all_of s1 q.rcv
        ok (core.result.Result.Ok (s2, event.KernelAction.CrossOutput
          q.src q.rcv q.crossing .Endorsed .MonitorBypassed))) =
          Result.ok (core.result.Result.Ok (st', ev)) at hok
      rw [hs1Eq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨s2, hs2Eq, hs2a, hs2p, hs2c, hs2t, hs2i, hs2ch, hs2ci, hs2ca, hs2cc,
        hs2g, hs2tr, hs2pend⟩ := spec_imp_exists
        (demoteAllOf_spec s1 q.rcv (by rw [hs1pend]; exact hR.ndPending))
      rw [hs2Eq] at hok
      simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq,
        Prod.mk.injEq] at hok
      obtain ⟨rfl, _⟩ := hok
      let a' := crossStateAbs a qA .endorsed .monitor_bypassed
      refine ⟨a', crossStateAbs_next a qA .endorsed .monitor_bypassed, ?_⟩
      apply cross_post_R st s2 bg a hR qA .endorsed .monitor_bypassed
      · exact hs2a.trans hs1a
      · exact hs2p.trans hs1p
      · exact hs2c.trans hs1c
      · exact hs2tr.trans hs1tr
      · exact hs2ch.trans hs1ch
      · exact hs2ci.trans hs1ci
      · intro A L
        simp only [a', crossStateAbs, reduceCtorEq, true_and, true_or, false_and,
          false_or]
        rw [hs2t, hs1t]
        simpa [hrcvQ, hrelConfQ] using
          ingest_taint_clause st bg a hR q.rcv q.released_conf vmT hvmT A L
      · intro A L
        simp only [a', crossStateAbs, reduceCtorEq, true_and, true_or, false_and,
          false_or]
        rw [hs2i, hs1i]
        simpa [hrcvQ, hrelIntegQ] using
          ingest_integ_clause st bg a hR q.rcv q.released_integ vmI hvmI A L
      · intro I
        simp only [a', crossStateAbs, if_pos rfl]
        unfold pendingC
        rw [hs2pend, hs1pend]
        simpa [hrcvQ] using ingest_demote_pending_clause st bg a hR q.rcv I
      · intro Att
        simp only [a', crossStateAbs, reduceCtorEq, true_and, true_or]
        rw [hs2ca, hs1ca, hattMem, ← hR.consumedAtt Att]
        constructor
        · rintro (hold | ⟨eA', heq, rfl⟩)
          · exact Or.inl hold
          · rw [hqAe] at heq
            injection heq with heq
            subst eA'
            exact Or.inr (by rw [heRel.1])
        · rintro (hold | heq)
          · exact Or.inl hold
          · exact Or.inr ⟨eA, hqAe, by rw [heRel.1]; exact heq⟩
      · intro X
        simp only [a', crossStateAbs]
        rw [hs2cc, hs1cc, hcrossMem, ← hR.consumedCross X, hcrossQ]
      · intro A D
        simp only [a', crossStateAbs, reduceCtorEq, if_pos rfl]
        unfold crossingGrantC
        rw [hs2g]
        rw [hrcvQ, hassignQ]
        exact hs1gr A D
      · rw [hs2t, hs1t]
        exact hvmTnd
      · rw [hs2i, hs1i]
        exact hvmInd
      · unfold vmNodupKeys
        rw [hs2pend, List.map_map, hs1pend]
        have hfe : Prod.fst ∘ demoteEntry q.rcv =
            (Prod.fst : types.InvocationId × types.PendingInvocation → types.InvocationId) := by
          funext x
          rfl
        rw [hfe]
        exact hR.ndPending
      · rw [hs2g]
        exact hs1nd
  case Unendorsed.Permitted =>
    simp only [crossTail, bind_tc_ok, crossBranch_eq_spec, reduceCtorEq, decide_false,
      Bool.false_eq_true, reduceIte, crossingId_clone_spec, disposition_eq_spec] at hok
    obtain ⟨srcT, hsrcTEq, hsrcT⟩ := spec_imp_exists
      (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_clone_spec st.taint_levels q.src)
    rw [hsrcTEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨vmT, hvmTEq, hvmT, hvmTnd⟩ := spec_imp_exists (hcopyConf rfl srcT hsrcTEq)
    rw [hvmTEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨srcI, hsrcIEq, hsrcI⟩ := spec_imp_exists
      (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        integLevel_clone_spec st.integ_levels q.src)
    rw [hsrcIEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨vmI, hvmIEq, hvmI, hvmInd⟩ := spec_imp_exists (hcopyInteg rfl srcI hsrcIEq)
    rw [hvmIEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨crossed, hcrossEq, hcrossMem⟩ := spec_imp_exists
      (vecSetInsert_spec types.CrossingId.Insts.CoreCloneClone
        types.CrossingId.Insts.CoreCmpPartialEqCrossingId crossingId_eq_spec
        st.consumed_crossings q.crossing hcapCross)
    rw [hcrossEq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq,
      Prod.mk.injEq] at hok
    obtain ⟨rfl, _⟩ := hok
    let a' := crossStateAbs a qA .unendorsed .permitted
    refine ⟨a', crossStateAbs_next a qA .unendorsed .permitted, ?_⟩
    apply cross_post_R st
      { st with taint_levels := vmT, integ_levels := vmI, consumed_crossings := crossed }
      bg a hR qA .unendorsed .permitted
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or, true_and]
      rw [hvmT A (confC L), ← hR.taint A L]
      have hm : (∃ x ∈ srcT.items.val, confC L = x) ↔ a.taint_levels q.src L := by
        constructor
        · rintro ⟨x, hx, heq⟩
          subst x
          exact (hR.taint q.src L).mpr ((hsrcT (confC L)).mp hx)
        · intro ha
          exact ⟨confC L, (hsrcT (confC L)).mpr ((hR.taint q.src L).mp ha), rfl⟩
      rw [hm, hsrcQ, hrcvQ]
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or, true_and]
      rw [hvmI A (integC L), ← hR.integ A L]
      have hm : (∃ x ∈ srcI.items.val, integC L = x) ↔ a.integ_levels q.src L := by
        constructor
        · rintro ⟨x, hx, heq⟩
          subst x
          exact (hR.integ q.src L).mpr ((hsrcI (integC L)).mp hx)
        · intro ha
          exact ⟨integC L, (hsrcI (integC L)).mpr ((hR.integ q.src L).mp ha), rfl⟩
      rw [hm, hsrcQ, hrcvQ]
    · intro I
      simp only [a', crossStateAbs, reduceCtorEq, if_false]
      exact hR.pending I
    · intro Att
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      simpa using hR.consumedAtt Att
    · intro X
      simp only [a', crossStateAbs]
      rw [hcrossMem, ← hR.consumedCross X, hcrossQ]
    · intro A D
      simp only [a', crossStateAbs, reduceCtorEq, if_false]
      exact hR.grants A D
    · exact hvmTnd
    · exact hvmInd
    · exact hR.ndPending
    · exact hR.ndGrants
  case Unendorsed.MonitorBypassed =>
    simp only [crossTail, bind_tc_ok, crossBranch_eq_spec, reduceCtorEq, decide_false,
      Bool.false_eq_true, reduceIte, crossingId_clone_spec, disposition_eq_spec,
      decide_true] at hok
    obtain ⟨srcT, hsrcTEq, hsrcT⟩ := spec_imp_exists
      (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_clone_spec st.taint_levels q.src)
    rw [hsrcTEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨vmT, hvmTEq, hvmT, hvmTnd⟩ := spec_imp_exists (hcopyConf rfl srcT hsrcTEq)
    rw [hvmTEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨srcI, hsrcIEq, hsrcI⟩ := spec_imp_exists
      (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        integLevel_clone_spec st.integ_levels q.src)
    rw [hsrcIEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨vmI, hvmIEq, hvmI, hvmInd⟩ := spec_imp_exists (hcopyInteg rfl srcI hsrcIEq)
    rw [hvmIEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨crossed, hcrossEq, hcrossMem⟩ := spec_imp_exists
      (vecSetInsert_spec types.CrossingId.Insts.CoreCloneClone
        types.CrossingId.Insts.CoreCmpPartialEqCrossingId crossingId_eq_spec
        st.consumed_crossings q.crossing hcapCross)
    rw [hcrossEq] at hok
    change (do
      let s1 ← state.KernelState.demote_all_of
        { st with
          taint_levels := vmT
          integ_levels := vmI
          consumed_crossings := crossed } q.rcv
      ok (core.result.Result.Ok (s1, event.KernelAction.CrossOutput
        q.src q.rcv q.crossing .Unendorsed .MonitorBypassed))) =
        Result.ok (core.result.Result.Ok (st', ev)) at hok
    obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1ch, hs1ci, hs1ca, hs1cc,
      hs1g, hs1tr, hs1pend⟩ := spec_imp_exists
      (demoteAllOf_spec
        { st with taint_levels := vmT, integ_levels := vmI, consumed_crossings := crossed }
        q.rcv hR.ndPending)
    rw [hs1Eq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq,
      Prod.mk.injEq] at hok
    obtain ⟨rfl, _⟩ := hok
    let a' := crossStateAbs a qA .unendorsed .monitor_bypassed
    refine ⟨a', crossStateAbs_next a qA .unendorsed .monitor_bypassed, ?_⟩
    apply cross_post_R st s1 bg a hR qA .unendorsed .monitor_bypassed
    · exact hs1a
    · exact hs1p
    · exact hs1c
    · exact hs1tr
    · exact hs1ch
    · exact hs1ci
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or, true_and]
      rw [hs1t, hvmT A (confC L), ← hR.taint A L]
      have hm : (∃ x ∈ srcT.items.val, confC L = x) ↔ a.taint_levels q.src L := by
        constructor
        · rintro ⟨x, hx, heq⟩
          subst x
          exact (hR.taint q.src L).mpr ((hsrcT (confC L)).mp hx)
        · intro ha
          exact ⟨confC L, (hsrcT (confC L)).mpr ((hR.taint q.src L).mp ha), rfl⟩
      rw [hm, hsrcQ, hrcvQ]
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or, true_and]
      rw [hs1i, hvmI A (integC L), ← hR.integ A L]
      have hm : (∃ x ∈ srcI.items.val, integC L = x) ↔ a.integ_levels q.src L := by
        constructor
        · rintro ⟨x, hx, heq⟩
          subst x
          exact (hR.integ q.src L).mpr ((hsrcI (integC L)).mp hx)
        · intro ha
          exact ⟨integC L, (hsrcI (integC L)).mpr ((hR.integ q.src L).mp ha), rfl⟩
      rw [hm, hsrcQ, hrcvQ]
    · intro I
      simp only [a', crossStateAbs, if_pos rfl]
      unfold pendingC
      rw [hs1pend]
      simpa [hrcvQ] using ingest_demote_pending_clause st bg a hR q.rcv I
    · intro Att
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      rw [hs1ca]
      simpa using hR.consumedAtt Att
    · intro X
      simp only [a', crossStateAbs]
      rw [hs1cc, hcrossMem, ← hR.consumedCross X, hcrossQ]
    · intro A D
      simp only [a', crossStateAbs, reduceCtorEq, if_false]
      unfold crossingGrantC
      rw [hs1g]
      exact hR.grants A D
    · rw [hs1t]
      exact hvmTnd
    · rw [hs1i]
      exact hvmInd
    · unfold vmNodupKeys
      rw [hs1pend, List.map_map]
      have hfe : Prod.fst ∘ demoteEntry q.rcv =
          (Prod.fst : types.InvocationId × types.PendingInvocation → types.InvocationId) := by
        funext x
        rfl
      rw [hfe]
      exact hR.ndPending
    · rw [hs1g]
      exact hR.ndGrants
  case Fail.Permitted =>
    simp only [crossTail, crossingId_clone_spec, bind_tc_ok, crossBranch_eq_spec,
      reduceCtorEq, decide_false, Bool.false_eq_true, reduceIte,
      disposition_eq_spec] at hok
    obtain ⟨crossed, hcrossEq, hcrossMem⟩ := spec_imp_exists
      (vecSetInsert_spec types.CrossingId.Insts.CoreCloneClone
        types.CrossingId.Insts.CoreCmpPartialEqCrossingId crossingId_eq_spec
        st.consumed_crossings q.crossing hcapCross)
    rw [hcrossEq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq,
      Prod.mk.injEq] at hok
    obtain ⟨rfl, _⟩ := hok
    let a' := crossStateAbs a qA .fail .permitted
    refine ⟨a', crossStateAbs_next a qA .fail .permitted, ?_⟩
    apply cross_post_R st { st with consumed_crossings := crossed } bg a hR qA .fail .permitted
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      simpa using hR.taint A L
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      simpa using hR.integ A L
    · intro I
      simp only [a', crossStateAbs, reduceCtorEq, if_false]
      exact hR.pending I
    · intro Att
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      simpa using hR.consumedAtt Att
    · intro X
      simp only [a', crossStateAbs]
      rw [hcrossMem, ← hR.consumedCross X, hcrossQ]
    · intro A D
      simp only [a', crossStateAbs, reduceCtorEq, if_false]
      exact hR.grants A D
    · exact hR.ndTaint
    · exact hR.ndInteg
    · exact hR.ndPending
    · exact hR.ndGrants
  case Fail.MonitorBypassed =>
    simp only [crossTail, crossingId_clone_spec, bind_tc_ok, crossBranch_eq_spec,
      reduceCtorEq, decide_false, Bool.false_eq_true, reduceIte,
      disposition_eq_spec, decide_true] at hok
    obtain ⟨crossed, hcrossEq, hcrossMem⟩ := spec_imp_exists
      (vecSetInsert_spec types.CrossingId.Insts.CoreCloneClone
        types.CrossingId.Insts.CoreCmpPartialEqCrossingId crossingId_eq_spec
        st.consumed_crossings q.crossing hcapCross)
    rw [hcrossEq] at hok
    change (do
      let s1 ← state.KernelState.demote_all_of
        { st with consumed_crossings := crossed } q.rcv
      ok (core.result.Result.Ok (s1, event.KernelAction.CrossOutput
        q.src q.rcv q.crossing .Fail .MonitorBypassed))) =
        Result.ok (core.result.Result.Ok (st', ev)) at hok
    obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1ch, hs1ci, hs1ca, hs1cc,
      hs1g, hs1tr, hs1pend⟩ := spec_imp_exists
      (demoteAllOf_spec { st with consumed_crossings := crossed } q.rcv hR.ndPending)
    rw [hs1Eq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq,
      Prod.mk.injEq] at hok
    obtain ⟨rfl, _⟩ := hok
    let a' := crossStateAbs a qA .fail .monitor_bypassed
    refine ⟨a', crossStateAbs_next a qA .fail .monitor_bypassed, ?_⟩
    apply cross_post_R st s1 bg a hR qA .fail .monitor_bypassed
    · exact hs1a
    · exact hs1p
    · exact hs1c
    · exact hs1tr
    · exact hs1ch
    · exact hs1ci
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      rw [hs1t]
      simpa using hR.taint A L
    · intro A L
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      rw [hs1i]
      simpa using hR.integ A L
    · intro I
      simp only [a', crossStateAbs, if_pos rfl]
      unfold pendingC
      rw [hs1pend]
      simpa [hrcvQ] using ingest_demote_pending_clause st bg a hR q.rcv I
    · intro Att
      simp only [a', crossStateAbs, reduceCtorEq, false_and, false_or]
      rw [hs1ca]
      simpa using hR.consumedAtt Att
    · intro X
      simp only [a', crossStateAbs]
      rw [hs1cc, hcrossMem, ← hR.consumedCross X, hcrossQ]
    · intro A D
      simp only [a', crossStateAbs, reduceCtorEq, if_false]
      unfold crossingGrantC
      rw [hs1g]
      exact hR.grants A D
    · rw [hs1t]
      exact hR.ndTaint
    · rw [hs1i]
      exact hR.ndInteg
    · unfold vmNodupKeys
      rw [hs1pend, List.map_map]
      have hfe : Prod.fst ∘ demoteEntry q.rcv =
          (Prod.fst : types.InvocationId × types.PendingInvocation → types.InvocationId) := by
        funext x
        rfl
      rw [hfe]
      exact hR.ndPending
    · rw [hs1g]
      exact hR.ndGrants


/-- The non-declassifying endorsed bound scan checks every source taint label. -/
theorem crossOutputLoop1_spec (released : types.ConfLevel)
    (src : collections.VecSet types.ConfLevel) :
    transitions.cross_output_loop1 released src true 0#usize ⦃ b =>
      b = true ↔ ∀ l ∈ src.items.val, confLeC l released = true ⦄ := by
  simpa [transitions.cross_output_loop1, transitions.cross_output_loop1.body,
    transitions.ingest_loop0, transitions.ingest_loop0.body] using
    (ingestLoop0_spec (st0 := true) released src true 0#usize (by simp) (by simp))


noncomputable def crossEndorsedTail (st : state.KernelState) (q : types.CrossInput)
    (dispo : types.Disposition) :
    Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError) := do
  let rcv ← types.AgentId.Insts.CoreCloneClone.clone q.rcv
  let taint ← collections.VecMapKVecSet.insert_into
    types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
    types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
    st.taint_levels rcv q.released_conf
  let integ ← collections.VecMapKVecSet.insert_into
    types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
    types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
    st.integ_levels rcv q.released_integ
  let crossing ← types.CrossingId.Insts.CoreCloneClone.clone q.crossing
  let crossings ← collections.VecSet.insert types.CrossingId.Insts.CoreCloneClone
    types.CrossingId.Insts.CoreCmpPartialEqCrossingId st.consumed_crossings crossing
  let isEndorsed ← types.CrossBranch.Insts.CoreCmpPartialEqCrossBranch.eq
    .Endorsed .Endorsed
  let st1 ← if isEndorsed then do
      let attestations ← match q.evidence with
        | none => ok st.consumed_attestations
        | some e => do
          let att ← types.AttestationId.Insts.CoreCloneClone.clone e.id
          collections.VecSet.insert types.AttestationId.Insts.CoreCloneClone
            types.AttestationId.Insts.CoreCmpPartialEqAttestationId st.consumed_attestations att
      state.KernelState.decrement_grant_at
        { st with
          taint_levels := taint
          integ_levels := integ
          consumed_attestations := attestations
          consumed_crossings := crossings } q.rcv q.assignment
    else ok { st with
      taint_levels := taint
      integ_levels := integ
      consumed_crossings := crossings }
  let bypass ← types.Disposition.Insts.CoreCmpPartialEqDisposition.eq dispo .MonitorBypassed
  let st2 ← if bypass then state.KernelState.demote_all_of st1 q.rcv else ok st1
  ok (.Ok (st2, .CrossOutput q.src q.rcv q.crossing .Endorsed dispo))

theorem crossTail_endorsed_eq
    (copyC : collections.VecMap types.AgentId (collections.VecSet types.ConfLevel) →
      types.AgentId → collections.VecSet types.ConfLevel → Result
        (collections.VecMap types.AgentId (collections.VecSet types.ConfLevel)))
    (copyI : collections.VecMap types.AgentId (collections.VecSet types.IntegLevel) →
      types.AgentId → collections.VecSet types.IntegLevel → Result
        (collections.VecMap types.AgentId (collections.VecSet types.IntegLevel)))
    (st : state.KernelState) (q : types.CrossInput) (d : types.Disposition) :
    crossTail copyC copyI st q .Endorsed d = crossEndorsedTail st q d := by
  cases d <;> simp [crossTail, crossEndorsedTail]

/-! ## Main preservation -/

theorem cross_output_preservesR (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (q : types.CrossInput)
    (qA : Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash) (hq : crossInputRel qA q)
    (hcapEndT : Tzimtzum.endorsedOK a qA →
      st.taint_levels.entries.val.length < Usize.max)
    (hcapEndTS : Tzimtzum.endorsedOK a qA →
      ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapEndI : Tzimtzum.endorsedOK a qA →
      st.integ_levels.entries.val.length < Usize.max)
    (hcapEndIS : Tzimtzum.endorsedOK a qA →
      ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapCopyT : ¬Tzimtzum.endorsedOK a qA → qA.fallback = .release_unendorsed →
      ∀ src, collections.VecMapKVecSet.get_set_or_empty
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        st.taint_levels q.src = .ok src → CopyCapacity st.taint_levels q.rcv src)
    (hcapCopyI : ¬Tzimtzum.endorsedOK a qA → qA.fallback = .release_unendorsed →
      ∀ src, collections.VecMapKVecSet.get_set_or_empty
        types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        st.integ_levels q.src = .ok src → CopyCapacity st.integ_levels q.rcv src)
    (hcapCross : st.consumed_crossings.items.val.length < Usize.max)
    (hcapAtt : Tzimtzum.endorsedOK a qA →
      st.consumed_attestations.items.val.length < Usize.max)
    (hcapGrant : Tzimtzum.endorsedOK a qA →
      st.crossing_grants.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.cross_output st bg q = .ok (.Ok (st', ev))) :
    ∃ branch dispo a',
      (Tzimtzum.cross_output qA branch dispo).guard a ∧
      (Tzimtzum.cross_output qA branch dispo).next a a' ∧ R st' bg a' := by
  obtain ⟨hsrcQ, hrcvQ, hcrossQ, houtQ, hdescQ, hfallQ, htintegQ, htconfQ,
    hassignQ, hevidenceQ, hrelConfQ, hrelIntegQ⟩ := hq
  have hqRel : crossInputRel qA q := ⟨hsrcQ, hrcvQ, hcrossQ, houtQ, hdescQ, hfallQ,
    htintegQ, htconfQ, hassignQ, hevidenceQ, hrelConfQ, hrelIntegQ⟩
  unfold transitions.cross_output at hok
  obtain ⟨bSrc, hbSrcEq, hbSrc⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active q.src)
  rw [hbSrcEq] at hok
  simp only [bind_tc_ok] at hok
  have hbSrcT : bSrc = true := by
    cases h : bSrc
    · simp only [h, Bool.false_eq_true, reduceIte, Result.ok.injEq] at hok
      cases hok
    · rfl
  simp only [hbSrcT, reduceIte] at hok
  have hactSrc : a.agent_active qA.src := by
    rw [hsrcQ, hR.active]
    exact hbSrc.mp hbSrcT
  obtain ⟨bRcv, hbRcvEq, hbRcv⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active q.rcv)
  rw [hbRcvEq] at hok
  simp only [bind_tc_ok] at hok
  have hbRcvT : bRcv = true := by
    cases h : bRcv
    · simp only [h, Bool.false_eq_true, reduceIte, Result.ok.injEq] at hok
      cases hok
    · rfl
  simp only [hbRcvT, reduceIte] at hok
  have hactRcv : a.agent_active qA.rcv := by
    rw [hrcvQ, hR.active]
    exact hbRcv.mp hbRcvT
  obtain ⟨inFlight, hifEq, hif⟩ := spec_imp_exists
    (crossOutputLoop0_spec st.pending q.src hR.ndPending false 0#usize
      (by simp) (by simp [sourceInFlightPrefix]))
  rw [hifEq] at hok
  simp only [bind_tc_ok] at hok
  have hifF : inFlight = false := by
    cases h : inFlight
    · rfl
    · simp only [h, reduceIte, Result.ok.injEq] at hok
      cases hok
  simp only [hifF, Bool.false_eq_true, reduceIte] at hok
  have hsrcFree : ∀ I J, a.pending I = some J → J.agent ≠ qA.src := by
    rw [hsrcQ]
    apply sourceNotInFlight_bridge st bg a hR q.src
    intro hex
    have ht := hif.mpr hex
    rw [hifF] at ht
    contradiction
  obtain ⟨replayed, hrEq, hr⟩ := spec_imp_exists
    (vecSetContains_spec types.CrossingId.Insts.CoreCloneClone
      types.CrossingId.Insts.CoreCmpPartialEqCrossingId crossingId_eq_spec
      st.consumed_crossings q.crossing)
  rw [hrEq] at hok
  simp only [bind_tc_ok] at hok
  have hrF : replayed = false := by
    cases h : replayed
    · rfl
    · simp only [h, reduceIte, Result.ok.injEq] at hok
      cases hok
  simp only [hrF, Bool.false_eq_true, reduceIte] at hok
  have hfreshCross : ¬a.consumed_crossings qA.crossing := by
    rw [hcrossQ, hR.consumedCross]
    intro hm
    have := hr.mpr hm
    rw [hrF] at this
    contradiction
  obtain ⟨endorsed, heq, hendorsed⟩ := spec_imp_exists (endorsedOK_spec st bg a hR q qA hqRel)
  rw [heq] at hok
  simp only [bind_tc_ok] at hok
  cases hend : endorsed with
  | true =>
    have hEnd : Tzimtzum.endorsedOK a qA := hendorsed.mp hend
    simp only [hend, reduceIte] at hok
    simp only [crossBranch_eq_spec, decide_true, bind_tc_ok, reduceIte] at hok
    rw [integLevel_le_spec] at hok
    simp only [bind_tc_ok] at hok
    have hbIT : integLeC q.released_integ q.t_integ = true := by
      cases h : integLeC q.released_integ q.t_integ
      · simp only [h, Bool.false_eq_true, reduceIte, Result.ok.injEq] at hok
        cases hok
      · rfl
    simp only [hbIT, reduceIte] at hok
    have hboundI : Tzimtzum.le_integ qA.released_integ qA.t_integ := by
      rw [hrelIntegQ, htintegQ, le_integ_integLeC_both]
      exact hbIT
    cases htc : q.t_conf with
    | none =>
      simp only [htc] at hok
      obtain ⟨srcT, hsrcTEq, hsrcT⟩ := spec_imp_exists
        (getSetOrEmpty_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_clone_spec st.taint_levels q.src)
      rw [hsrcTEq] at hok
      simp only [bind_tc_ok] at hok
      obtain ⟨bound, hboundEq, hbound⟩ := spec_imp_exists
        (crossOutputLoop1_spec q.released_conf srcT)
      rw [hboundEq] at hok
      simp only [bind_tc_ok] at hok
      have hboundT : bound = true := by cases bound <;> simp_all
      simp only [hboundT, reduceIte] at hok
      have hboundC : ∀ c, qA.t_conf = some c →
          Tzimtzum.le_conf qA.released_conf c := by
        intro c hc
        rw [htconfQ, htc] at hc
        contradiction
      have hboundNC : qA.t_conf = none → ∀ L,
          a.taint_levels qA.src L → Tzimtzum.le_conf L qA.released_conf := by
        intro _ L hL
        have hm : confC L ∈ srcT.items.val :=
          (hsrcT (confC L)).mpr ((hR.taint q.src L).mp (by simpa [hsrcQ] using hL))
        rw [hrelConfQ, le_conf_confLeC]
        exact hbound.mp hboundT (confC L) hm
      let permC := fun vm r src => transitions.cross_output_loop2 vm r src 0#usize
      let permI := fun vm r src => transitions.cross_output_loop3 vm r src 0#usize
      let monC := fun vm r src => transitions.cross_output_loop4 vm r src 0#usize
      let monI := fun vm r src => transitions.cross_output_loop5 vm r src 0#usize
      simp at hok
      have hqSame : ({ q with t_conf := none } : types.CrossInput) = q := by rw [← htc]
      rw [hqSame] at hok
      obtain ⟨holds, hholdsEq, hholds⟩ := spec_imp_exists
        (crossHoldsEndorsed_spec st bg a hR q qA hqRel)
      rw [hholdsEq] at hok
      simp only [bind_tc_ok] at hok
      by_cases hh : holds = true
      · simp only [hh, reduceIte] at hok
        have hguard : (Tzimtzum.cross_output qA .endorsed .permitted).guard a :=
          ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, fun _ => hEnd,
            by simp, by simp, fun _ => hboundI, fun _ => hboundC, fun _ => hboundNC, by simp,
            fun _ => hholds.mp hh, by simp⟩
        let copyC := permC
        let copyI := permI
        have hokDirect : crossEndorsedTail st q .Permitted = .ok (.Ok (st', ev)) := by
          unfold crossEndorsedTail
          simp
          convert hok using 1 <;> rfl
        have hokTail : crossTail copyC copyI st q .Endorsed .Permitted =
            .ok (.Ok (st', ev)) := by rw [crossTail_endorsed_eq]; exact hokDirect
        obtain ⟨a', hn, hR'⟩ := crossTail_preservesR copyC copyI st bg a hR q qA hqRel
          .Endorsed .Permitted hguard (by simp) (by simp)
          (fun _ => hcapEndT hEnd) (fun _ => hcapEndTS hEnd)
          (fun _ => hcapEndI hEnd) (fun _ => hcapEndIS hEnd) hcapCross
          (fun _ => hcapAtt hEnd) (fun _ => hcapGrant hEnd) st' ev hokTail
        exact ⟨.endorsed, .permitted, a', hguard, hn, hR'⟩
      · rw [Bool.not_eq_true] at hh
        simp only [hh, Bool.false_eq_true, reduceIte,
          background.BackgroundTheory.impl.mode, mode_eq_spec, bind_tc_ok] at hok
        by_cases hm : bg.mode = types.Mode.Monitor
        · simp only [hm, decide_true, reduceIte] at hok
          have hmode : a.mode = Tzimtzum.Mode.monitor := hR.mode.trans (by rw [hm]; rfl)
          have hguard : (Tzimtzum.cross_output qA .endorsed .monitor_bypassed).guard a :=
            ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, fun _ => hEnd,
              by simp, by simp, fun _ => hboundI, fun _ => hboundC, fun _ => hboundNC, by simp,
              by simp, fun _ => ⟨by rw [← hholds]; intro ht; rw [hh] at ht; contradiction, hmode⟩⟩
          let copyC := monC
          let copyI := monI
          have hokDirect : crossEndorsedTail st q .MonitorBypassed =
              .ok (.Ok (st', ev)) := by
            unfold crossEndorsedTail
            simp
            convert hok using 1 <;> rfl
          have hokTail : crossTail copyC copyI st q .Endorsed .MonitorBypassed =
              .ok (.Ok (st', ev)) := by rw [crossTail_endorsed_eq]; exact hokDirect
          obtain ⟨a', hn, hR'⟩ := crossTail_preservesR copyC copyI st bg a hR q qA hqRel
            .Endorsed .MonitorBypassed hguard (by simp) (by simp)
            (fun _ => hcapEndT hEnd) (fun _ => hcapEndTS hEnd)
            (fun _ => hcapEndI hEnd) (fun _ => hcapEndIS hEnd) hcapCross
            (fun _ => hcapAtt hEnd) (fun _ => hcapGrant hEnd) st' ev hokTail
          exact ⟨.endorsed, .monitor_bypassed, a', hguard, hn, hR'⟩
        · simp [hm] at hok
    | some c =>
      simp only [htc] at hok
      rw [confLevel_le_spec] at hok
      simp only [bind_tc_ok] at hok
      have hbCT : confLeC q.released_conf c = true := by
        cases h : confLeC q.released_conf c
        · simp only [h, Bool.false_eq_true, reduceIte, Result.ok.injEq] at hok
          cases hok
        · rfl
      simp only [hbCT, reduceIte] at hok
      have hboundC : ∀ cA, qA.t_conf = some cA →
          Tzimtzum.le_conf qA.released_conf cA := by
        intro cA hcA
        rw [htconfQ, htc] at hcA
        injection hcA with hcA
        subst cA
        rw [hrelConfQ, le_conf_confLeC_both]
        exact hbCT
      have hboundNC : qA.t_conf = none → ∀ L,
          a.taint_levels qA.src L → Tzimtzum.le_conf L qA.released_conf := by
        intro hn
        rw [htconfQ, htc] at hn
        contradiction
      let permC := fun vm r src => transitions.cross_output_loop6 vm r src 0#usize
      let permI := fun vm r src => transitions.cross_output_loop7 vm r src 0#usize
      let monC := fun vm r src => transitions.cross_output_loop8 vm r src 0#usize
      let monI := fun vm r src => transitions.cross_output_loop9 vm r src 0#usize
      simp at hok
      have hqSame : ({ q with t_conf := some c } : types.CrossInput) = q := by rw [← htc]
      rw [hqSame] at hok
      obtain ⟨holds, hholdsEq, hholds⟩ := spec_imp_exists
        (crossHoldsEndorsed_spec st bg a hR q qA hqRel)
      rw [hholdsEq] at hok
      simp only [bind_tc_ok] at hok
      by_cases hh : holds = true
      · simp only [hh, reduceIte] at hok
        have hguard : (Tzimtzum.cross_output qA .endorsed .permitted).guard a :=
          ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, fun _ => hEnd,
            by simp, by simp, fun _ => hboundI, fun _ => hboundC, fun _ => hboundNC, by simp,
            fun _ => hholds.mp hh, by simp⟩
        let copyC := permC
        let copyI := permI
        have hokDirect : crossEndorsedTail st q .Permitted = .ok (.Ok (st', ev)) := by
          unfold crossEndorsedTail
          simp
          convert hok using 1 <;> rfl
        have hokTail : crossTail copyC copyI st q .Endorsed .Permitted =
            .ok (.Ok (st', ev)) := by rw [crossTail_endorsed_eq]; exact hokDirect
        obtain ⟨a', hn, hR'⟩ := crossTail_preservesR copyC copyI st bg a hR q qA hqRel
          .Endorsed .Permitted hguard (by simp) (by simp)
          (fun _ => hcapEndT hEnd) (fun _ => hcapEndTS hEnd)
          (fun _ => hcapEndI hEnd) (fun _ => hcapEndIS hEnd) hcapCross
          (fun _ => hcapAtt hEnd) (fun _ => hcapGrant hEnd) st' ev hokTail
        exact ⟨.endorsed, .permitted, a', hguard, hn, hR'⟩
      · rw [Bool.not_eq_true] at hh
        simp only [hh, Bool.false_eq_true, reduceIte,
          background.BackgroundTheory.impl.mode, mode_eq_spec, bind_tc_ok] at hok
        by_cases hm : bg.mode = types.Mode.Monitor
        · simp only [hm, decide_true, reduceIte] at hok
          have hmode : a.mode = Tzimtzum.Mode.monitor := hR.mode.trans (by rw [hm]; rfl)
          have hguard : (Tzimtzum.cross_output qA .endorsed .monitor_bypassed).guard a :=
            ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, fun _ => hEnd,
              by simp, by simp, fun _ => hboundI, fun _ => hboundC, fun _ => hboundNC, by simp,
              by simp, fun _ => ⟨by rw [← hholds]; intro ht; rw [hh] at ht; contradiction, hmode⟩⟩
          let copyC := monC
          let copyI := monI
          have hokDirect : crossEndorsedTail st q .MonitorBypassed =
              .ok (.Ok (st', ev)) := by
            unfold crossEndorsedTail
            simp
            convert hok using 1 <;> rfl
          have hokTail : crossTail copyC copyI st q .Endorsed .MonitorBypassed =
              .ok (.Ok (st', ev)) := by rw [crossTail_endorsed_eq]; exact hokDirect
          obtain ⟨a', hn, hR'⟩ := crossTail_preservesR copyC copyI st bg a hR q qA hqRel
            .Endorsed .MonitorBypassed hguard (by simp) (by simp)
            (fun _ => hcapEndT hEnd) (fun _ => hcapEndTS hEnd)
            (fun _ => hcapEndI hEnd) (fun _ => hcapEndIS hEnd) hcapCross
            (fun _ => hcapAtt hEnd) (fun _ => hcapGrant hEnd) st' ev hokTail
          exact ⟨.endorsed, .monitor_bypassed, a', hguard, hn, hR'⟩
        · simp [hm] at hok
  | false =>
    have hnEnd : ¬Tzimtzum.endorsedOK a qA := by
      intro hEnd
      have ht := hendorsed.mpr hEnd
      rw [hend] at ht
      contradiction
    cases hfb : q.fallback with
    | ReleaseUnendorsed =>
      simp only [hend, Bool.false_eq_true, reduceIte, hfb] at hok
      simp at hok
      have hfall : qA.fallback = Tzimtzum.Fallback.release_unendorsed := by
        rw [hfallQ, hfb]
        rfl
      let permC := fun vm r src => transitions.cross_output_loop10 vm r src 0#usize
      let permI := fun vm r src => transitions.cross_output_loop11 vm r src 0#usize
      let monC := fun vm r src => transitions.cross_output_loop12 vm r src 0#usize
      let monI := fun vm r src => transitions.cross_output_loop13 vm r src 0#usize
      have hqSame : ({ q with fallback := .ReleaseUnendorsed } : types.CrossInput) = q := by
        rw [← hfb]
      rw [hqSame] at hok
      obtain ⟨holds, hholdsEq, hholds⟩ := spec_imp_exists
        (crossHoldsUnendorsed_spec st bg a hR q qA hqRel)
      rw [hholdsEq] at hok
      simp only [bind_tc_ok] at hok
      by_cases hh : holds = true
      · simp only [hh, reduceIte] at hok
        have hguard : (Tzimtzum.cross_output qA .unendorsed .permitted).guard a :=
          ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, by simp,
            fun _ => ⟨hnEnd, hfall⟩, by simp, by simp, by simp, by simp,
            by simp, fun _ => hholds.mp hh, by simp⟩
        let copyC := permC
        let copyI := permI
        have hokTail : crossTail copyC copyI st q .Unendorsed .Permitted =
            .ok (.Ok (st', ev)) := by
          unfold crossTail
          simp
          convert hok using 1 <;> rfl
        have hcopyC : types.CrossBranch.Unendorsed = .Unendorsed → ∀ src,
            collections.VecMapKVecSet.get_set_or_empty
              types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
              types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
              st.taint_levels q.src = .ok src →
            copyC st.taint_levels q.rcv src ⦃ vm =>
              copyRel st.taint_levels vm q.rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
          intro _ src hget
          exact crossOutputCopyConfLoop10_spec st.taint_levels q.rcv src
            (hcapCopyT hnEnd hfall src hget) hR.ndTaint
        have hcopyI : types.CrossBranch.Unendorsed = .Unendorsed → ∀ src,
            collections.VecMapKVecSet.get_set_or_empty
              types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
              types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
              st.integ_levels q.src = .ok src →
            copyI st.integ_levels q.rcv src ⦃ vm =>
              copyRel st.integ_levels vm q.rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
          intro _ src hget
          exact crossOutputCopyIntegLoop11_spec st.integ_levels q.rcv src
            (hcapCopyI hnEnd hfall src hget) hR.ndInteg
        obtain ⟨a', hn, hR'⟩ := crossTail_preservesR copyC copyI st bg a hR q qA hqRel
          .Unendorsed .Permitted hguard hcopyC hcopyI
          (by simp) (by simp) (by simp) (by simp) hcapCross
          (by simp) (by simp) st' ev hokTail
        exact ⟨.unendorsed, .permitted, a', hguard, hn, hR'⟩
      · rw [Bool.not_eq_true] at hh
        simp only [hh, Bool.false_eq_true, reduceIte,
          background.BackgroundTheory.impl.mode, mode_eq_spec, bind_tc_ok] at hok
        by_cases hm : bg.mode = types.Mode.Monitor
        · simp only [hm, decide_true, reduceIte] at hok
          have hmode : a.mode = Tzimtzum.Mode.monitor := hR.mode.trans (by rw [hm]; rfl)
          have hguard : (Tzimtzum.cross_output qA .unendorsed .monitor_bypassed).guard a :=
            ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, by simp,
              fun _ => ⟨hnEnd, hfall⟩, by simp, by simp, by simp, by simp,
              by simp, by simp,
              fun _ => ⟨by rw [← hholds]; intro ht; rw [hh] at ht; contradiction, hmode⟩⟩
          let copyC := monC
          let copyI := monI
          have hokTail : crossTail copyC copyI st q .Unendorsed .MonitorBypassed =
              .ok (.Ok (st', ev)) := by
            unfold crossTail
            simp
            convert hok using 1 <;> rfl
          have hcopyC : types.CrossBranch.Unendorsed = .Unendorsed → ∀ src,
              collections.VecMapKVecSet.get_set_or_empty
                types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
                types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
                st.taint_levels q.src = .ok src →
              copyC st.taint_levels q.rcv src ⦃ vm =>
                copyRel st.taint_levels vm q.rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
            intro _ src hget
            exact crossOutputCopyConfLoop12_spec st.taint_levels q.rcv src
              (hcapCopyT hnEnd hfall src hget) hR.ndTaint
          have hcopyI : types.CrossBranch.Unendorsed = .Unendorsed → ∀ src,
              collections.VecMapKVecSet.get_set_or_empty
                types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
                types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
                st.integ_levels q.src = .ok src →
              copyI st.integ_levels q.rcv src ⦃ vm =>
                copyRel st.integ_levels vm q.rcv src.items.val ∧ vmNodupKeys vm ⦄ := by
            intro _ src hget
            exact crossOutputCopyIntegLoop13_spec st.integ_levels q.rcv src
              (hcapCopyI hnEnd hfall src hget) hR.ndInteg
          obtain ⟨a', hn, hR'⟩ := crossTail_preservesR copyC copyI st bg a hR q qA hqRel
            .Unendorsed .MonitorBypassed hguard hcopyC hcopyI
            (by simp) (by simp) (by simp) (by simp) hcapCross
            (by simp) (by simp) st' ev hokTail
          exact ⟨.unendorsed, .monitor_bypassed, a', hguard, hn, hR'⟩
        · simp [hm] at hok
    | Fail =>
      simp only [hend, Bool.false_eq_true, reduceIte, hfb] at hok
      simp at hok
      have hfall : qA.fallback = Tzimtzum.Fallback.fail := by
        rw [hfallQ, hfb]
        rfl
      let permC := fun vm r src => transitions.cross_output_loop10 vm r src 0#usize
      let permI := fun vm r src => transitions.cross_output_loop11 vm r src 0#usize
      let monC := fun vm r src => transitions.cross_output_loop12 vm r src 0#usize
      let monI := fun vm r src => transitions.cross_output_loop13 vm r src 0#usize
      have hqSame : ({ q with fallback := .Fail } : types.CrossInput) = q := by
        rw [← hfb]
      rw [hqSame] at hok
      obtain ⟨holds, hholdsEq, hholds⟩ := spec_imp_exists
        (crossHoldsFail_spec st bg a q qA)
      rw [hholdsEq] at hok
      simp only [bind_tc_ok] at hok
      have hh : holds = true := hholds.mpr (by simp [Tzimtzum.crossHolds_iff])
      simp only [hh, reduceIte] at hok
      have hguard : (Tzimtzum.cross_output qA .fail .permitted).guard a :=
        ⟨hactSrc, hactRcv, hsrcFree, hfreshCross, by simp, by simp,
          fun _ => ⟨hnEnd, hfall⟩, by simp, by simp, by simp, by simp,
          fun _ => hholds.mp hh, by simp⟩
      let copyC := permC
      let copyI := permI
      have hokTail : crossTail copyC copyI st q .Fail .Permitted =
          .ok (.Ok (st', ev)) := by
        unfold crossTail
        simp
        convert hok using 1 <;> rfl
      obtain ⟨a', hn, hR'⟩ := crossTail_preservesR copyC copyI st bg a hR q qA hqRel
        .Fail .Permitted hguard (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) hcapCross
        (by simp) (by simp) st' ev hokTail
      exact ⟨.fail, .permitted, a', hguard, hn, hR'⟩

end ArgusLean.Refinement
