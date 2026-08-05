import Tzimtzum.Soundness
import Tzimtzum.GrantConservation

/-!
# Task 11 — named per-transition theorems (T-3–T-6, T-8–T-10)

These properties live outside `allInv`: they relate a pre-state to a post-state rather than
classifying one state. Lifecycle monotonicity is stated for agents active on both sides of
the transition, exactly capturing the `delegate` initialization and `revoke` clearing
exceptions without exposing action parameters from the closed transition system.
-/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false

namespace Tzimtzum

/-- Old integrity levels remain present for every agent that survives the transition. -/
def survivingIntegrityMonotone (s s' : KSt) : Prop :=
  ∀ A L, s.agent_active A → s'.agent_active A →
    s.integ_levels A L → s'.integ_levels A L

/-- Old confidentiality taint remains present for every agent that survives the transition. -/
def survivingConfMonotone (s s' : KSt) : Prop :=
  ∀ A L, s.agent_active A → s'.agent_active A →
    s.taint_levels A L → s'.taint_levels A L

private theorem labels_of_frame (s s' : KSt)
    (ht : s'.taint_levels = s.taint_levels) (hi : s'.integ_levels = s.integ_levels) :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  constructor
  · intro A L _ _ hL
    rw [hi]
    exact hL
  · intro A L _ _ hL
    rw [ht]
    exact hL

private theorem labels_of_growth (s s' : KSt)
    (pt : KAgent → ConfLevel → Prop) (pi : KAgent → IntegLevel → Prop)
    (ht : s'.taint_levels = fun A L => s.taint_levels A L ∨ pt A L)
    (hi : s'.integ_levels = fun A L => s.integ_levels A L ∨ pi A L) :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  constructor
  · intro A L _ _ hL
    rw [hi]
    exact Or.inl hL
  · intro A L _ _ hL
    rw [ht]
    exact Or.inl hL

private theorem labels_of_restrict (s s' : KSt) (removed : KAgent)
    (hactive : s'.agent_active = fun A => s.agent_active A ∧ A ≠ removed)
    (ht : s'.taint_levels = fun A L => s.taint_levels A L ∧ A ≠ removed)
    (hi : s'.integ_levels = fun A L => s.integ_levels A L ∧ A ≠ removed) :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  constructor
  · intro A L _ hpost hL
    rw [hactive] at hpost
    rw [hi]
    exact ⟨hL, hpost.2⟩
  · intro A L _ hpost hL
    rw [hactive] at hpost
    rw [ht]
    exact ⟨hL, hpost.2⟩

private theorem labels_register_tool (tool : KTool) (s s' : KSt)
    (hn : (register_tool tool).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_frame s s' ht hi

private theorem labels_unregister_tool (tool : KTool) (s s' : KSt)
    (hn : (unregister_tool tool).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_frame s s' ht hi

private theorem labels_delegate (grantor grantee : KAgent) (s s' : KSt)
    (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, hinactive, -, -⟩ := hg
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  constructor
  · intro A L hpre _ hL
    rw [hi]
    refine ⟨hL, ?_⟩
    intro hA
    subst A
    exact hinactive hpre
  · intro A L hpre _ hL
    rw [ht]
    refine ⟨hL, ?_⟩
    intro hA
    subst A
    exact hinactive hpre

private theorem labels_grant_capability (prnt child : KAgent) (cap : KCap)
    (s s' : KSt) (hn : (grant_capability prnt child cap).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_frame s s' ht hi

private theorem labels_grant_crossing (grantor agent : KAgent) (d : KAssignment) (n : Nat)
    (s s' : KSt) (hn : (grant_crossing grantor agent d n).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_frame s s' ht hi

private theorem labels_revoke (prnt target : KAgent) (s s' : KSt)
    (hn : (revoke prnt target).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨hactive, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_restrict s s' target hactive ht hi

private theorem labels_cascade_revoke (child prnt : KAgent) (s s' : KSt)
    (hn : (cascade_revoke child prnt).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨hactive, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_restrict s s' child hactive ht hi

private theorem labels_ingest (a : KAgent) (src : Option KAgent) (pconf : ConfLevel)
    (pinteg : IntegLevel) (dispo : Disposition) (s s' : KSt)
    (hn : (ingest a src pconf pinteg dispo).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_growth s s'
    (fun A L => A = a ∧ L = pconf) (fun A L => A = a ∧ L = pinteg) ht hi

private theorem labels_begin_invocation (a : KAgent) (inv : KInv) (chal : KChallenge)
    (snap : KSnapshot) (egr : KEgress → Prop) (ah : KContentHash) (authorized : Prop)
    (v : Verdict) (s s' : KSt)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_frame s s' ht hi

private theorem labels_authorize_inspected (inv : KInv) (sc : KChallengeScope)
    (att : InspectionAttestation KInv KChallenge KAttest KPolicy KContentHash) (admit : Bool)
    (s s' : KSt) (hn : (authorize_inspected inv sc att admit).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_frame s s' ht hi

private theorem labels_settle_invocation (inv : KInv) (a : KAgent) (dispo : Disposition)
    (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation KInv KAttest)) (s s' : KSt)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_growth s s'
    (fun A L => outcome ≠ Outcome.ambiguous ∧ A = a ∧ L = clvl)
    (fun A L => outcome ≠ Outcome.ambiguous ∧ A = a ∧ L = ilvl) ht hi

private theorem labels_cross_output
    (q : CrossInput KAgent KAttest KCrossing KAssignment KContentHash)
    (branch : CrossBranch) (dispo : Disposition) (s s' : KSt)
    (hn : (cross_output q branch dispo).next s s') :
    survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  obtain ⟨-, -, -, ht, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hn
  exact labels_of_growth s s'
    (fun A L =>
      (branch = CrossBranch.endorsed ∧ A = q.rcv ∧ L = q.released_conf)
      ∨ (branch = CrossBranch.unendorsed ∧ A = q.rcv ∧ s.taint_levels q.src L))
    (fun A L =>
      (branch = CrossBranch.endorsed ∧ A = q.rcv ∧ L = q.released_integ)
      ∨ (branch = CrossBranch.unendorsed ∧ A = q.rcv ∧ s.integ_levels q.src L)) ht hi

private theorem transition_label_monotonicity :
    ∀ na ∈ ksystem.actions, ∀ s s' : KSt,
      na.2.guard s → na.2.next s s' →
        survivingIntegrityMonotone s s' ∧ survivingConfMonotone s s' := by
  intro na hmem s s' hg hn
  simp only [ksystem, system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Kav.close1] at hn
    obtain ⟨tool, -, hn'⟩ := hn
    exact labels_register_tool tool s s' hn'
  · simp only [Kav.close1] at hn
    obtain ⟨tool, -, hn'⟩ := hn
    exact labels_unregister_tool tool s s' hn'
  · simp only [Kav.close2] at hn
    obtain ⟨grantor, grantee, hg', hn'⟩ := hn
    exact labels_delegate grantor grantee s s' hg' hn'
  · simp only [Kav.close3] at hn
    obtain ⟨prnt, child, cap, -, hn'⟩ := hn
    exact labels_grant_capability prnt child cap s s' hn'
  · simp only [Kav.close4] at hn
    obtain ⟨grantor, agent, d, n, -, hn'⟩ := hn
    exact labels_grant_crossing grantor agent d n s s' hn'
  · simp only [Kav.close2] at hn
    obtain ⟨prnt, target, -, hn'⟩ := hn
    exact labels_revoke prnt target s s' hn'
  · simp only [Kav.close2] at hn
    obtain ⟨child, prnt, -, hn'⟩ := hn
    exact labels_cascade_revoke child prnt s s' hn'
  · simp only [Kav.close5] at hn
    obtain ⟨a, src, pconf, pinteg, dispo, -, hn'⟩ := hn
    exact labels_ingest a src pconf pinteg dispo s s' hn'
  · simp only [Kav.close8] at hn
    obtain ⟨a, inv, chal, snap, egr, ah, authorized, v, -, hn'⟩ := hn
    exact labels_begin_invocation a inv chal snap egr ah authorized v s s' hn'
  · simp only [Kav.close4] at hn
    obtain ⟨inv, sc, att, admit, -, hn'⟩ := hn
    exact labels_authorize_inspected inv sc att admit s s' hn'
  · simp only [Kav.close7] at hn
    obtain ⟨inv, a, dispo, outcome, clvl, ilvl, att, -, hn'⟩ := hn
    exact labels_settle_invocation inv a dispo outcome clvl ilvl att s s' hn'
  · simp only [Kav.close3] at hn
    obtain ⟨q, branch, dispo, -, hn'⟩ := hn
    exact labels_cross_output q branch dispo s s' hn'

/-- **T-3 integrity monotonicity.** Every old integrity observation remains for agents that
survive any registered transition. Adding observations can only lower effective trust. -/
theorem integrity_monotonicity :
    ∀ na ∈ ksystem.actions, ∀ s s' : KSt,
      na.2.guard s → na.2.next s s' → survivingIntegrityMonotone s s' := by
  intro na hmem s s' hg hn
  exact (transition_label_monotonicity na hmem s s' hg hn).1

#print axioms integrity_monotonicity

/-- **T-4 confidentiality no-descent.** Every old taint observation remains for agents that
survive any registered transition. Data-label declassification is isolated in T-6. -/
theorem confidentiality_no_descent :
    ∀ na ∈ ksystem.actions, ∀ s s' : KSt,
      na.2.guard s → na.2.next s s' → survivingConfMonotone s s' := by
  intro na hmem s s' hg hn
  exact (transition_label_monotonicity na hmem s s' hg hn).2

#print axioms confidentiality_no_descent

/-- **T-5 inspection non-restoration.** Challenge resolution frames both label dimensions
and no use of its attestation id can appear on a different invocation. -/
theorem inspection_non_restoration (inv : KInv) (sc : KChallengeScope)
    (att : InspectionAttestation KInv KChallenge KAttest KPolicy KContentHash) (admit : Bool)
    (s s' : KSt) (hinv : allInv s) (hg : (authorize_inspected inv sc att admit).guard s)
    (hn : (authorize_inspected inv sc att admit).next s s') :
    s'.taint_levels = s.taint_levels
    ∧ s'.integ_levels = s.integ_levels
    ∧ (∀ I, I ≠ inv → s'.pending I = s.pending I)
    ∧ (∀ I J, s'.pending I = some J →
        J.admission = Admission.inspected att.id → I = inv) := by
  have hnext := hn
  have hguard := hg
  obtain ⟨-, -, -, ht, hi, hpending, -, -, -, -, -, -, -, -, -, -⟩ := hnext
  obtain ⟨-, -, -, -, -, hfresh, -, -, -⟩ := hguard
  obtain ⟨-, -, -, ⟨-, -, -, hevidence, -, -⟩, -⟩ := hinv
  refine ⟨ht, hi, ?_, ?_⟩
  · intro I hne
    rw [hpending]
    simp [hne]
  · intro I J hJ hadmission
    by_cases hI : I = inv
    · exact hI
    · rw [hpending] at hJ
      simp only [hI, false_and, if_false] at hJ
      exact (hfresh (hevidence I J att.id hJ hadmission)).elim

#print axioms inspection_non_restoration

/-- **T-6 crossing frame and bound (E25).** The exact receiver-label, pending-demotion,
history and grant updates are exposed together with all endorsed release bounds. -/
theorem crossing_frame_and_bound
    (q : CrossInput KAgent KAttest KCrossing KAssignment KContentHash)
    (branch : CrossBranch) (dispo : Disposition) (s s' : KSt)
    (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') :
    s'.taint_levels = (fun A L =>
      s.taint_levels A L
      ∨ (branch = CrossBranch.endorsed ∧ A = q.rcv ∧ L = q.released_conf)
      ∨ (branch = CrossBranch.unendorsed ∧ A = q.rcv ∧ s.taint_levels q.src L))
    ∧ s'.integ_levels = (fun A L =>
      s.integ_levels A L
      ∨ (branch = CrossBranch.endorsed ∧ A = q.rcv ∧ L = q.released_integ)
      ∨ (branch = CrossBranch.unendorsed ∧ A = q.rcv ∧ s.integ_levels q.src L))
    ∧ s'.pending =
      (if dispo = Disposition.monitor_bypassed then demoteAllOf s.pending q.rcv else s.pending)
    ∧ s'.consumed_crossings = (fun X => s.consumed_crossings X ∨ X = q.crossing)
    ∧ s'.consumed_attestations = (fun X =>
      s.consumed_attestations X
      ∨ (branch = CrossBranch.endorsed ∧ ∃ e, q.evidence = some e ∧ X = e.id))
    ∧ s'.crossing_grants =
      (if branch = CrossBranch.endorsed
        then decrementGrantAt s.crossing_grants q.rcv q.assignment
        else s.crossing_grants)
    ∧ (q.src ≠ q.rcv →
      (∀ L, s'.taint_levels q.src L ↔ s.taint_levels q.src L)
      ∧ (∀ L, s'.integ_levels q.src L ↔ s.integ_levels q.src L))
    ∧ (branch = CrossBranch.endorsed → le_integ q.released_integ q.t_integ)
    ∧ (branch = CrossBranch.endorsed →
      ∀ c, q.t_conf = some c → le_conf q.released_conf c)
    ∧ (branch = CrossBranch.endorsed → q.t_conf = none →
      ∀ L, s.taint_levels q.src L → le_conf L q.released_conf) := by
  have hnext := hn
  have hguard := hg
  obtain ⟨-, -, -, ht, hi, hpending, -, -, hatt, hcross, hgrants, -, -, -, -, -⟩ := hnext
  obtain ⟨-, -, -, -, -, -, -, hinteg, hconf, hnodeclass, -, -, -⟩ := hguard
  refine ⟨ht, hi, hpending, hcross, hatt, hgrants, ?_, hinteg, hconf, hnodeclass⟩
  intro hne
  constructor
  · intro L
    rw [ht]
    constructor
    · rintro (hL | ⟨-, heq, -⟩ | ⟨-, heq, -⟩)
      · exact hL
      · exact (hne heq).elim
      · exact (hne heq).elim
    · exact Or.inl
  · intro L
    rw [hi]
    constructor
    · rintro (hL | ⟨-, heq, -⟩ | ⟨-, heq, -⟩)
      · exact hL
      · exact (hne heq).elim
      · exact (hne heq).elim
    · exact Or.inl

#print axioms crossing_frame_and_bound

/-- **T-8 permit stability — ingestion.** Both pending-gate bundles survive every branch;
monitor bypass does so by demoting affected records rather than retaining false claims. -/
theorem permit_stability_ingest (a : KAgent) (src : Option KAgent) (pconf : ConfLevel)
    (pinteg : IntegLevel) (dispo : Disposition) (s s' : KSt)
    (hinv : allInv s) (hg : (ingest a src pconf pinteg dispo).guard s)
    (hn : (ingest a src pconf pinteg dispo).next s s') : invP s' ∧ invPP s' :=
  ⟨presP_ingest a src pconf pinteg dispo s s' hinv hg hn,
   presPP_ingest a src pconf pinteg dispo s s' hinv hg hn⟩

#print axioms permit_stability_ingest

/-- **T-8 permit stability — settlement.** Frozen pairwise checks make free absorption safe;
non-contained settlement demotes siblings instead of invalidating their claimed gates. -/
theorem permit_stability_settlement (inv : KInv) (a : KAgent) (dispo : Disposition)
    (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation KInv KAttest)) (s s' : KSt)
    (hinv : allInv s)
    (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') :
    invP s' ∧ invPP s' :=
  ⟨presP_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
   presPP_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn⟩

#print axioms permit_stability_settlement

/-- **T-8 permit stability — crossing.** Receiver-side holds or monitor demotion preserve
all retained pending and pairwise gate claims. -/
theorem permit_stability_crossing
    (q : CrossInput KAgent KAttest KCrossing KAssignment KContentHash)
    (branch : CrossBranch) (dispo : Disposition) (s s' : KSt)
    (hinv : allInv s) (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') : invP s' ∧ invPP s' :=
  ⟨presP_cross_output q branch dispo s s' hinv hg hn,
   presPP_cross_output q branch dispo s s' hinv hg hn⟩

#print axioms permit_stability_crossing

private theorem consumed_ids_frame (s s' : KSt)
    (hids : s'.consumed_ids = s.consumed_ids) :
    ∀ I, s.consumed_ids I → s'.consumed_ids I := by
  intro I hI
  rw [hids]
  exact hI

private theorem consumed_ids_action_monotone :
    ∀ na ∈ ksystem.actions, ∀ s s' : KSt,
      na.2.guard s → na.2.next s s' →
        ∀ I, s.consumed_ids I → s'.consumed_ids I := by
  intro na hmem s s' _hg hn
  simp only [ksystem, system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Kav.close1] at hn
    obtain ⟨_, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close1] at hn
    obtain ⟨_, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close2] at hn
    obtain ⟨_, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close3] at hn
    obtain ⟨_, _, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close4] at hn
    obtain ⟨_, _, _, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close2] at hn
    obtain ⟨_, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close2] at hn
    obtain ⟨_, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close5] at hn
    obtain ⟨_, _, _, _, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close8] at hn
    obtain ⟨_, _, _, _, _, _, _, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    intro I hI
    rw [hids]
    exact Or.inl hI
  · simp only [Kav.close4] at hn
    obtain ⟨_, _, _, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close7] at hn
    obtain ⟨_, _, _, _, _, _, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids
  · simp only [Kav.close3] at hn
    obtain ⟨_, _, _, _, hn'⟩ := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn'
    exact consumed_ids_frame s s' hids

/-- **T-9 freshness subsumption, persistence half.** Invocation-id history is monotone
across every registered action, including revocation and re-delegation. -/
theorem consumed_ids_monotone :
    ∀ na ∈ ksystem.actions, ∀ s s' : KSt,
      na.2.guard s → na.2.next s s' →
        ∀ I, s.consumed_ids I → s'.consumed_ids I :=
  consumed_ids_action_monotone

#print axioms consumed_ids_monotone

/-- **T-9 freshness subsumption, burn half.** Beginning requires a never-used id and burns
it on every verdict branch, so persistence rules out any later replay. -/
theorem invocation_freshness_subsumption (a : KAgent) (inv : KInv) (chal : KChallenge)
    (snap : KSnapshot) (egr : KEgress → Prop) (ah : KContentHash) (authorized : Prop)
    (v : Verdict) (s s' : KSt)
    (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') :
    ¬ s.consumed_ids inv ∧ s'.consumed_ids inv := by
  have hguard := hg
  obtain ⟨-, -, -, -, -, hfresh, -, -, -, -, -, -, -⟩ := hguard
  obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hn
  refine ⟨hfresh, ?_⟩
  rw [hids]
  exact Or.inr rfl

#print axioms invocation_freshness_subsumption

/-- **T-10 quarantine resolution safety.** A quarantined record can settle only through a
fresh attestation scoped to this invocation and outcome, and that exact id is consumed. -/
theorem quarantine_resolution_safety (inv : KInv) (a : KAgent) (dispo : Disposition)
    (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation KInv KAttest)) (s s' : KSt) (J : KPending)
    (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s')
    (hJ : s.pending inv = some J) (hquarantined : J.quarantined) :
    outcome ≠ Outcome.ambiguous
    ∧ ∃ r, att = some r ∧ r.inv = inv ∧ r.outcome = outcome
      ∧ ¬ s.consumed_attestations r.id
      ∧ ∀ X, s'.consumed_attestations X ↔ s.consumed_attestations X ∨ X = r.id := by
  have hguard := hg
  obtain ⟨-, -, -, -, hresolution, -⟩ := hguard
  obtain ⟨houtcome, r, hatt, hinv, hout, hfresh⟩ := hresolution J hJ hquarantined
  obtain ⟨-, -, -, -, -, -, -, -, hconsumed, -, -, -, -, -, -, -⟩ := hn
  refine ⟨houtcome, r, hatt, hinv, hout, hfresh, ?_⟩
  intro X
  rw [hconsumed, hatt]
  simp

#print axioms quarantine_resolution_safety

/-- **T-10 quarantine participation.** The flag never removes a pending record from the
unrestricted speculative sets; when contained, it also participates in clearance and both
self-pair gate obligations. -/
theorem quarantine_participates (s : KSt) (inv : KInv) (J : KPending)
    (hinv : allInv s) (hJ : s.pending inv = some J) (_hquarantined : J.quarantined) :
    speculative_taint s J.agent J.policy.output_conf
    ∧ speculative_integ s J.agent J.policy.output_integ
    ∧ (contained J →
      speculative_taint_contained s J.agent J.policy.output_conf
      ∧ (∀ E, J.egress E →
        s.flow_allows J.policy.output_conf E
        ∨ (s.flow_inspects J.policy.output_conf E ∧ vouched J))
      ∧ (integ_allows J.policy.output_integ J.policy
        ∨ (integ_inspects J.policy.output_integ J.policy ∧ vouched J))) := by
  obtain ⟨-, -, ⟨hflow, hinteg⟩, -, -⟩ := hinv
  refine ⟨Or.inr ⟨inv, J, hJ, rfl, rfl⟩, Or.inr ⟨inv, J, hJ, rfl, rfl⟩, ?_⟩
  intro hcontained
  refine ⟨Or.inr ⟨inv, J, hJ, rfl, hcontained, rfl⟩, ?_, ?_⟩
  · intro E hE
    exact hflow inv inv J J E hJ hJ rfl hcontained hcontained hE
  · exact hinteg inv inv J J hJ hJ rfl hcontained hcontained

#print axioms quarantine_participates

end Tzimtzum
