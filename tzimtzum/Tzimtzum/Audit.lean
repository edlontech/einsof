import Tzimtzum.Transitions

/-!
# Reachable-step audit theorems

These theorems expose the guard and update facts for evidence-consuming admissions, quarantine
resolutions, endorsed crossings, and delegated compartments. They prove only kernel facts: scope,
freshness, one-use consumption, and state updates. Attestation issuer identity and truth are
external inputs rather than kernel state.
-/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false

namespace Tzimtzum

/-- The integrity checks preserve `integrity_confinement` after invocation admission. -/
theorem audit_integrity_confinement (a : KAgent) (inv : KInv) (chal : KChallenge)
    (snap : KSnapshot) (egr : KEgress → Prop) (ah : KContentHash) (authorized : Prop)
    (v : Verdict) (s s' : KSt) (hinv : allInv s)
    (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') :
    integrity_confinement s' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hresult, -, -⟩ :=
    presP_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn
  exact hresult

#print axioms audit_integrity_confinement

/-- The flow checks preserve `flow_confinement` after invocation admission. -/
theorem audit_flow_confinement (a : KAgent) (inv : KInv) (chal : KChallenge)
    (snap : KSnapshot) (egr : KEgress → Prop) (ah : KContentHash) (authorized : Prop)
    (v : Verdict) (s s' : KSt) (hinv : allInv s)
    (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') :
    flow_confinement s' := by
  obtain ⟨-, -, -, -, -, -, -, hresult, -, -, -, -⟩ :=
    presP_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn
  exact hresult

#print axioms audit_flow_confinement

/-! ## Evidence conservation over reachable steps -/

/-- Kernel conservation claim for an inspected admission event. -/
def InspectionEvidenceConserved : Prop :=
  ∀ (s s' : KSt) (inv : KInv) (sc : KChallengeScope)
    (att : InspectionAttestation KInv KChallenge KAttest KPolicy KContentHash)
    (admit : Bool),
    Kav.Reachable ksystem s → admit = true →
    (authorize_inspected inv sc att admit).guard s →
    (authorize_inspected inv sc att admit).next s s' →
      att.positive
      ∧ att.inv = inv
      ∧ att.challenge = sc.challenge
      ∧ att.args_hash = sc.args_hash
      ∧ att.policy_digest = sc.policy.policy_digest
      ∧ ¬ s.consumed_attestations att.id
      ∧ (∀ X, s'.consumed_attestations X ↔
          s.consumed_attestations X ∨ X = att.id)
      ∧ ∃ J, s'.pending inv = some J
          ∧ J.admission = Admission.inspected att.id

/-- Kernel conservation claim for a quarantined resolution event. -/
def ResolutionEvidenceConserved : Prop :=
  ∀ (s s' : KSt) (inv : KInv) (a : KAgent) (dispo : Disposition)
    (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation KInv KAttest)) (J : KPending),
    Kav.Reachable ksystem s → s.pending inv = some J → J.quarantined →
    (settle_invocation inv a dispo outcome clvl ilvl att).guard s →
    (settle_invocation inv a dispo outcome clvl ilvl att).next s s' →
      ∃ r, att = some r
        ∧ r.inv = inv
        ∧ r.outcome = outcome
        ∧ ¬ s.consumed_attestations r.id
        ∧ ∀ X, s'.consumed_attestations X ↔
            s.consumed_attestations X ∨ X = r.id

/-- Kernel conservation and bounded-decrement claim for an endorsed crossing event. -/
def EndorsedEvidenceConserved : Prop :=
  ∀ (s s' : KSt) (q : CrossInput KAgent KAttest KCrossing KAssignment KContentHash)
    (dispo : Disposition),
    Kav.Reachable ksystem s →
    (cross_output q CrossBranch.endorsed dispo).guard s →
    (cross_output q CrossBranch.endorsed dispo).next s s' →
      ∃ e g, q.evidence = some e
        ∧ e.positive
        ∧ ¬ s.consumed_attestations e.id
        ∧ e.output = q.output_hash
        ∧ e.src = q.src
        ∧ e.rcv = q.rcv
        ∧ e.descriptor = q.descriptor
        ∧ e.assignment = q.assignment
        ∧ s.crossing_grants q.rcv q.assignment = some g
        ∧ 0 < g.remaining
        ∧ g.remaining ≤ g.provisioned
        ∧ (∀ X, s'.consumed_attestations X ↔
            s.consumed_attestations X ∨ X = e.id)
        ∧ s'.consumed_crossings q.crossing
        ∧ s'.crossing_grants q.rcv q.assignment =
            some { g with remaining := g.remaining - 1 }

theorem audit_inspected_evidence : InspectionEvidenceConserved := by
  intro s s' inv sc att admit _hreach hadmit hg hn
  have hguard := hg
  obtain ⟨-, hinv, hchallenge, hargs, hpolicy, hfresh, -, hadmits, -⟩ := hguard
  obtain ⟨-, -, -, -, -, hpending, -, -, hconsumed, -, -, -, -, -, -, -⟩ := hn
  refine ⟨(hadmits hadmit).1, hinv, hchallenge, hargs, hpolicy, hfresh, ?_, ?_⟩
  · intro X
    rw [hconsumed]
  · let J : KPending :=
      { agent := sc.agent
        policy := sc.policy
        egress := sc.egress
        admission := Admission.inspected att.id
        disposition := Disposition.permitted
        authorized := sc.authorized
        quarantined := False }
    refine ⟨J, ?_, rfl⟩
    rw [hpending]
    simp [hadmit, J]

#print axioms audit_inspected_evidence

theorem audit_resolution_evidence : ResolutionEvidenceConserved := by
  intro s s' inv a dispo outcome clvl ilvl att J _hreach hJ hquarantined hg hn
  obtain ⟨-, r, hatt, hinv, houtcome, hfresh, hconsumed⟩ :=
    quarantine_resolution_safety inv a dispo outcome clvl ilvl att s s' J hg hn hJ
      hquarantined
  exact ⟨r, hatt, hinv, houtcome, hfresh, hconsumed⟩

#print axioms audit_resolution_evidence

theorem audit_endorsed_evidence : EndorsedEvidenceConserved := by
  intro s s' q dispo hreach hg hn
  have hguard := hg
  have hnext := hn
  obtain ⟨-, -, -, -, hendorsed, -, -, -, -, -, -, -, -⟩ := hguard
  obtain ⟨⟨e, hevidence, hpositive, hfresh, houtput, hsrc, hrcv, hdescriptor, hassignment⟩,
    g, hgrant, hremaining⟩ := hendorsed rfl
  obtain ⟨-, -, -, -, ⟨hbounded, -, -⟩⟩ := kav_sound s hreach
  obtain ⟨-, -, -, -, -, -, -, -, hconsumed, hcrossing, hgrants, -, -, -, -, -⟩ := hnext
  refine ⟨e, g, hevidence, hpositive, hfresh, houtput, hsrc, hrcv, hdescriptor,
    hassignment, hgrant, hremaining, hbounded q.rcv q.assignment g hgrant, ?_, ?_, ?_⟩
  · intro X
    rw [hconsumed]
    simp [hevidence]
  · rw [hcrossing]
    exact Or.inr rfl
  · rw [hgrants, if_pos rfl]
    exact decrementGrantAt_self s.crossing_grants q.rcv q.assignment g hgrant

#print axioms audit_endorsed_evidence

/-- Every evidence-bearing reachable step consumes one fresh, scope-matching attestation.
An endorsed crossing also consumes its crossing identifier and decrements its grant once. -/
theorem audit_evidence_conservation :
    InspectionEvidenceConserved
    ∧ ResolutionEvidenceConserved
    ∧ EndorsedEvidenceConserved :=
  ⟨audit_inspected_evidence, audit_resolution_evidence, audit_endorsed_evidence⟩

#print axioms audit_evidence_conservation

/-! ## Fresh compartment -/

/-- Delegation clears the grantee's labels, pending records, and grants, making its held-label
gate obligations vacuous immediately after delegation. -/
theorem audit_fresh_compartment (grantor grantee : KAgent) (s s' : KSt)
    (hn : (delegate grantor grantee).next s s') :
    (∀ L, ¬ s'.taint_levels grantee L)
    ∧ (∀ L, ¬ s'.integ_levels grantee L)
    ∧ (∀ I J, s'.pending I = some J → J.agent ≠ grantee)
    ∧ (∀ D, s'.crossing_grants grantee D = none)
    ∧ (∀ L, ¬ speculative_taint s' grantee L)
    ∧ (∀ L, ¬ speculative_integ s' grantee L)
    ∧ ∀ snap : KSnapshot,
        (∀ L, speculative_taint s' grantee L → clearance_admits L snap)
        ∧ (∀ L, speculative_integ s' grantee L → integ_allows L snap) := by
  obtain ⟨-, -, -, ht, hi, hpending, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  have htaint : ∀ L, ¬ s'.taint_levels grantee L := by
    intro L hL
    rw [ht] at hL
    exact hL.2 rfl
  have hinteg : ∀ L, ¬ s'.integ_levels grantee L := by
    intro L hL
    rw [hi] at hL
    exact hL.2 rfl
  have hpendingOwner : ∀ I J, s'.pending I = some J → J.agent ≠ grantee := by
    intro I J hJ
    rw [hpending] at hJ
    exact (dropPendingOf_eq_some s.pending grantee I J).mp hJ |>.2
  have hspecTaint : ∀ L, ¬ speculative_taint s' grantee L := by
    intro L hL
    rcases hL with hL | ⟨I, J, hJ, hagent, -⟩
    · exact htaint L hL
    · exact hpendingOwner I J hJ hagent
  have hspecInteg : ∀ L, ¬ speculative_integ s' grantee L := by
    intro L hL
    rcases hL with hL | ⟨I, J, hJ, hagent, -⟩
    · exact hinteg L hL
    · exact hpendingOwner I J hJ hagent
  refine ⟨htaint, hinteg, hpendingOwner, ?_, hspecTaint, hspecInteg, ?_⟩
  · intro D
    rw [hgrants]
    exact dropGrantsOf_self s.crossing_grants grantee D
  · intro snap
    exact ⟨fun L hL => (hspecTaint L hL).elim,
      fun L hL => (hspecInteg L hL).elim⟩

#print axioms audit_fresh_compartment

/-! ## Replay-equivalence statement

`Replays` records a fixed sequence of registered closed actions. The statement below expresses
determinism for one such sequence from one starting state. -/

/-- Replay a fixed list of registered closed actions from a fixed starting state. -/
inductive Replays {σ : Type} (ts : Kav.TransitionSystem σ) :
    List (String × Kav.Action σ) → σ → σ → Prop where
  | nil (s : σ) : Replays ts [] s s
  | cons {na : String × Kav.Action σ} {rest : List (String × Kav.Action σ)} {s s₁ s₂ : σ}
      (hmem : na ∈ ts.actions) (hguard : na.2.guard s) (hnext : na.2.next s s₁)
      (htail : Replays ts rest s₁ s₂) : Replays ts (na :: rest) s s₂

/-- The same registered transition sequence from the same state reaches one state.
Closed action parameters are existential, so this is stated as a property rather than proved here. -/
def replay_equivalence_statement : Prop :=
  ∀ (start out₁ out₂ : KSt) (trace : List (String × Kav.Action KSt)),
    Replays ksystem trace start out₁ → Replays ksystem trace start out₂ → out₁ = out₂

end Tzimtzum
