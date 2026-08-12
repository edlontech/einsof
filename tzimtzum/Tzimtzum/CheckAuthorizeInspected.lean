import Tzimtzum.Soundness.Common

/-! # `authorize_inspected` preserves the invariant bundle

One `Preserves` theorem per sub-bundle. `invS`, `invE`, and `invC` discharge fully
automatically. `invP`'s five confinement conjuncts and both `invPP` conjuncts are manual:
each routes the guard's re-checked `beginAdmissible` gate through a case split on whether a
pending record is the newly admitted one, which the discharge cascades do not find. The case
split and the guard payload are factored into the private inversion lemmas below, so the
manual proofs read off named gate arms and pre-state invariants instead of positional
conjunction patterns. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- The state at this file's sort tuple. The ascription in each `Preserves` statement pins
the two sorts (`CrossingId`, `AssignmentDigest`) that the action's arguments do not
determine. -/
local notation "St!" => St AgentId ToolId InvocationId CapKind EgressKind ChallengeId
  AttestationId CrossingId AssignmentDigest PolicyDigest ContentHash

/-! ## Inversion helpers

Built on the `kav_action`-generated projections (`next_taint_levels`, `next_pending`,
`guard_admit_pos`, …): nothing in this file destructures the action's `guard`/`next`
conjunctions positionally. -/

section Inversion

open authorize_inspected

variable {inv : InvocationId}
  {sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash}
  {att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash}
  {admit : Bool}
  {s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash}

/-- The pending record installed by an admitting `authorize_inspected`. -/
private def admittedRecord
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest
      ContentHash) :
    PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest :=
  { agent := sc.agent, policy := sc.policy, egress := sc.egress,
    admission := Admission.inspected att.id,
    disposition := Disposition.permitted, authorized := sc.authorized,
    quarantined := False }

/-- Taint labels are framed. -/
private theorem next_taint (hn : (authorize_inspected inv sc att admit).next s s') :
    s'.taint_levels = s.taint_levels :=
  next_taint_levels hn

/-- Integrity labels are framed. -/
private theorem next_integ (hn : (authorize_inspected inv sc att admit).next s s') :
    s'.integ_levels = s.integ_levels :=
  next_integ_levels hn

/-- The flow-ALLOW relation is framed (the allow ceiling is immutable background). -/
private theorem next_flow_allows (hn : (authorize_inspected inv sc att admit).next s s') :
    s'.flow_allows = s.flow_allows := by
  funext L E
  simp only [St.flow_allows, next_egress_allow_ceiling hn]

/-- The flow-INSPECT relation is framed (the inspect ceiling is immutable background). -/
private theorem next_flow_inspects (hn : (authorize_inspected inv sc att admit).next s s') :
    s'.flow_inspects = s.flow_inspects := by
  funext L E
  simp only [St.flow_inspects, next_egress_inspect_ceiling hn]

/-- A record pending after `authorize_inspected` is the newly admitted one at the resolved
key, or a pre-existing record at an untouched key. -/
private theorem pending_cases {I : InvocationId}
    {J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest}
    (hn : (authorize_inspected inv sc att admit).next s s')
    (hJ : s'.pending I = some J) :
    (I = inv ∧ admit = true ∧ J = admittedRecord sc att)
    ∨ (¬(I = inv ∧ admit = true) ∧ s.pending I = some J) := by
  rw [next_pending hn] at hJ
  by_cases h : I = inv ∧ admit = true
  · simp only [if_pos h] at hJ
    exact Or.inl ⟨h.1, h.2, (Option.some.inj hJ).symm⟩
  · simp only [if_neg h] at hJ
    exact Or.inr ⟨h, hJ⟩

/-- An admitting guard re-checked the full begin-time admission gate at the current state. -/
private theorem admitted_gate (hg : (authorize_inspected inv sc att admit).guard s)
    (hadm : admit = true) :
    beginAdmissible s sc.agent sc.policy sc.egress sc.authorized :=
  (guard_admit_pos hg hadm).2.toBeginAdmissible

end Inversion

/-! ## Preservation, one theorem per sub-bundle -/

/-- `invS` (9 structural conjuncts): fully automated. -/
theorem presS_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool) :
    Preserves (authorize_inspected inv sc att admit : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  kav_discharge authorize_inspected

/-- `invP` (12 pending/gate conjuncts). The first seven discharge automatically. The five
confinement conjuncts are manual: labels and ceilings are framed, so a pre-existing record
defers to the pre-state invariant, while the newly admitted record is covered by the
corresponding arm of the guard's re-checked admission gate. -/
theorem presP_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool) :
    Preserves (authorize_inspected inv sc att admit : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  refine ⟨?pending_unique, ?pending_registered, ?root_no_pending, ?pending_ids_consumed,
    ?pending_egress_attested, ?pending_snapshot_coherent, ?default_deny, ?flow_confinement,
    ?flow_confinement_weak, ?integrity_confinement, ?integrity_confinement_weak,
    ?clearance_confinement⟩
  case pending_unique => kav_discharge authorize_inspected
  case pending_registered => kav_discharge authorize_inspected
  case root_no_pending => kav_discharge authorize_inspected
  case pending_ids_consumed => kav_discharge authorize_inspected
  case pending_egress_attested => kav_discharge authorize_inspected
  case pending_snapshot_coherent => kav_discharge authorize_inspected
  case default_deny => kav_discharge authorize_inspected
  case flow_confinement =>
    intro L I J E hL hJ hcontained hE
    rw [next_taint hn] at hL
    rw [next_flow_allows hn, next_flow_inspects hn]
    rcases pending_cases hn hJ with ⟨rfl, hadm, rfl⟩ | ⟨-, hold⟩
    · -- The admitted record: its owner's held taint passed the re-checked flow gate.
      rcases (admitted_gate hg hadm).flow.speculative L E (Or.inl hL) hE with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
    · -- A pre-existing record at an untouched key: the pre-state invariant applies.
      exact hinv.flow_confinement L I J E hL hold hcontained hE
  case flow_confinement_weak =>
    intro L I J E hL hJ hcontained hE
    rw [next_taint hn] at hL
    rw [next_flow_allows hn, next_flow_inspects hn]
    rcases pending_cases hn hJ with ⟨rfl, hadm, rfl⟩ | ⟨-, hold⟩
    · exact (admitted_gate hg hadm).flow.speculative L E (Or.inl hL) hE
    · exact hinv.flow_confinement_weak L I J E hL hold hcontained hE
  case integrity_confinement =>
    intro L I J hL hJ hcontained
    rw [next_integ hn] at hL
    rcases pending_cases hn hJ with ⟨rfl, hadm, rfl⟩ | ⟨-, hold⟩
    · -- The admitted record: its owner's held integrity passed the re-checked gate.
      rcases (admitted_gate hg hadm).integ.speculative L (Or.inl hL) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
    · exact hinv.integrity_confinement L I J hL hold hcontained
  case integrity_confinement_weak =>
    intro L I J hL hJ hcontained
    rw [next_integ hn] at hL
    rcases pending_cases hn hJ with ⟨rfl, hadm, rfl⟩ | ⟨-, hold⟩
    · exact (admitted_gate hg hadm).integ.speculative L (Or.inl hL)
    · exact hinv.integrity_confinement_weak L I J hL hold hcontained
  case clearance_confinement =>
    intro L I J hJ hcontained hspec
    unfold speculative_taint_contained at hspec
    rcases pending_cases hn hJ with ⟨rfl, hadm, rfl⟩ | ⟨-, holdJ⟩
    · -- The admitted record: the re-checked clearance gate covers held taint, every
      -- pre-existing record's output, and (via its own snapshot ceiling) itself.
      have hclr := (admitted_gate hg hadm).clearance
      rcases hspec with hL | ⟨I2, K, hK, hKagent, -, hKlevel⟩
      · rw [next_taint hn] at hL
        exact hclr.speculative L (Or.inl hL)
      · rcases pending_cases hn hK with ⟨-, -, rfl⟩ | ⟨-, holdK⟩
        · rw [← hKlevel]
          exact hclr.self
        · exact hclr.speculative L (Or.inr ⟨I2, K, holdK, hKagent, hKlevel⟩)
    · -- A pre-existing record: held-taint and old-record sources defer to the pre-state
      -- invariant; the admitted record's output clears J's ceiling by the gate's pending arm.
      rcases hspec with hL | ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩
      · rw [next_taint hn] at hL
        exact hinv.clearance_confinement L I J holdJ hcontained (Or.inl hL)
      · rcases pending_cases hn hK with ⟨-, hadm, rfl⟩ | ⟨-, holdK⟩
        · rw [← hKlevel]
          exact (admitted_gate hg hadm).clearance.pending I J holdJ hKagent.symm
        · exact hinv.clearance_confinement L I J holdJ hcontained
            (Or.inr ⟨I2, K, holdK, hKagent, hKcontained, hKlevel⟩)

/-- `invPP` (2 pairwise conjuncts), both manual: the admitted record must be pairwise
compatible with itself (the gate's newcomer arm), with every pre-existing record of the same
agent (the gate's pending arm), and in the reverse direction the pre-existing record's output
is part of the agent's speculative label set (the gate's speculative arm). -/
theorem presPP_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool) :
    Preserves (authorize_inspected inv sc att admit : Kav.Action St!) invPP := by
  intro s s' hinv hg hn
  refine ⟨?pending_flow_compat, ?pending_integ_compat⟩
  case pending_flow_compat =>
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hc1 hc2 hE
    rw [next_flow_allows hn, next_flow_inspects hn]
    rcases pending_cases hn hJ1 with ⟨-, hadm, rfl⟩ | ⟨-, hold1⟩
    · rcases pending_cases hn hJ2 with ⟨-, -, rfl⟩ | ⟨-, hold2⟩
      · -- Self-pair of the admitted record.
        rcases (admitted_gate hg hadm).flow.newcomer E hE with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · -- Admitted output against a pre-existing record's egress.
        exact (admitted_gate hg hadm).flow.pending_pairs I2 J2 E hold2 hagent.symm hE
    · rcases pending_cases hn hJ2 with ⟨-, hadm, rfl⟩ | ⟨-, hold2⟩
      · -- Pre-existing output against the admitted record's egress: the pre-existing
        -- record's output is a speculative taint source checked by the gate.
        rcases (admitted_gate hg hadm).flow.speculative J1.policy.output_conf E
            (Or.inr ⟨I1, J1, hold1, hagent, rfl⟩) hE with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · exact hinv.pending_flow_compat I1 I2 J1 J2 E hold1 hold2 hagent hc1 hc2 hE
  case pending_integ_compat =>
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hc1 hc2
    rcases pending_cases hn hJ1 with ⟨-, hadm, rfl⟩ | ⟨-, hold1⟩
    · rcases pending_cases hn hJ2 with ⟨-, -, rfl⟩ | ⟨-, hold2⟩
      · rcases (admitted_gate hg hadm).integ.newcomer with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · exact (admitted_gate hg hadm).integ.pending_pairs I2 J2 hold2 hagent.symm
    · rcases pending_cases hn hJ2 with ⟨-, hadm, rfl⟩ | ⟨-, hold2⟩
      · rcases (admitted_gate hg hadm).integ.speculative J1.policy.output_integ
            (Or.inr ⟨I1, J1, hold1, hagent, rfl⟩) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · exact hinv.pending_integ_compat I1 I2 J1 J2 hold1 hold2 hagent hc1 hc2

/-- `invE` (6 evidence conjuncts): fully automated (lite cascade; gates stay atomic). -/
theorem presE_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool) :
    Preserves (authorize_inspected inv sc att admit : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  kav_discharge_lite authorize_inspected

/-- `invC` (3 crossing conjuncts): fully automated frame preservation. -/
theorem presC_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool) :
    Preserves (authorize_inspected inv sc att admit : Kav.Action St!) invC := by
  intro s s' hinv _hg hn
  kav_discharge_lite authorize_inspected

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool) :
    Preserves (authorize_inspected inv sc att admit : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_authorize_inspected inv sc att admit s s' hinv hg hn,
     presP_authorize_inspected inv sc att admit s s' hinv hg hn,
     presPP_authorize_inspected inv sc att admit s s' hinv hg hn,
     presE_authorize_inspected inv sc att admit s s' hinv hg hn,
     presC_authorize_inspected inv sc att admit s s' hinv hg hn⟩

#print axioms pres_authorize_inspected

end Tzimtzum
