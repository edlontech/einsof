import Tzimtzum.Soundness.Common

/-! `begin_invocation` preserves the bundle (one theorem per sub-bundle).

Admission classifies the verdict against the strict/admissible gates. The manual bullets
all follow one argument: a *contained* post-state record is an old record (the pre-state
invariant applies) or the strict-ALLOW newcomer (`contained_pending_cases` — the monitor
branches insert `monitor_bypassed` records and the enforce inspection branch inserts no
record), and the newcomer is covered arm-by-arm by the guard's `verdict_allow` payload,
the `beginAllow` gate. Everything else is automated. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- The state at this file's sort tuple. The ascription in each `Preserves` statement pins
the sorts the action's arguments do not determine. -/
local notation "St!" => St AgentId ToolId InvocationId CapKind EgressKind ChallengeId
  AttestationId CrossingId AssignmentDigest PolicyDigest ContentHash

/-! ## Inversion helpers

Built on the `kav_action`-generated projections (`next_pending`, `guard_verdict_allow`, …):
nothing in this file destructures the action's `guard`/`next` conjunctions positionally. -/

section Inversion

variable {a : AgentId} {inv : InvocationId} {chal : ChallengeId}
  {snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest}
  {egr : EgressKind → Prop} {ah : ContentHash} {authorized : Prop} {v : Verdict}
  {s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash}
  {I : InvocationId}
  {J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest}

/-- A contained post-begin record is either an old record or the strict-ALLOW newcomer.
The monitor branches insert `monitor_bypassed` records and the enforce inspection branch
inserts no pending record, so neither can inhabit the second arm. -/
private theorem contained_pending_cases
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s')
    (hJ : s'.pending I = some J) (hcontained : contained J) :
    s.pending I = some J ∨
      (I = inv ∧ v = Verdict.allow ∧ J.agent = a ∧ J.policy = snap ∧ J.egress = egr
        ∧ J.admission = Admission.plain ∧ J.authorized = authorized ∧ ¬ J.quarantined) := by
  rw [begin_invocation.next_pending hn] at hJ
  by_cases hI : I = inv
  · subst I
    right
    cases v <;> cases hmode : s.mode <;>
      simp [hmode] at hJ <;> cases hJ <;> simp [contained] at hcontained ⊢
  · left
    simpa only [if_neg hI] using hJ

end Inversion

/-! ## Preservation, one theorem per sub-bundle -/

/-- `invS` (9 structural conjuncts): fully automated. -/
theorem presS_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict) :
    Preserves (begin_invocation a inv chal snap egr ah authorized v : Kav.Action St!)
      invS := by
  intro s s' hinv hg hn
  kav_discharge begin_invocation

/-- `invP` (12 pending/gate conjuncts). The first seven discharge automatically. The five
confinement conjuncts are manual: labels and ceilings are framed, so a pre-existing record
defers to the pre-state invariant, while the strict-ALLOW newcomer is covered by the
corresponding arm of the guard's `beginAllow` payload. -/
theorem presP_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict) :
    Preserves (begin_invocation a inv chal snap egr ah authorized v : Kav.Action St!)
      invP := by
  intro s s' hinv hg hn
  refine ⟨?pending_unique, ?pending_registered, ?root_no_pending, ?pending_ids_consumed,
    ?pending_egress_attested, ?pending_snapshot_coherent, ?default_deny, ?flow_confinement,
    ?flow_confinement_weak, ?integrity_confinement, ?integrity_confinement_weak,
    ?clearance_confinement⟩
  case pending_unique => kav_discharge begin_invocation
  case pending_registered => kav_discharge begin_invocation
  case root_no_pending => kav_discharge begin_invocation
  case pending_ids_consumed => kav_discharge begin_invocation
  case pending_egress_attested => kav_discharge begin_invocation
  case pending_snapshot_coherent => kav_discharge begin_invocation
  case default_deny => kav_discharge begin_invocation
  case flow_confinement =>
    have hallowGate := begin_invocation.guard_verdict_allow hg
    have ht := begin_invocation.next_taint_levels hn
    have hallowField := begin_invocation.next_egress_allow_ceiling hn
    have hinspectField := begin_invocation.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallowField, hinspectField]
    rw [ht] at hL
    rcases contained_pending_cases hn hJ hcontained with
      hOld | ⟨-, hv, hagent, -, hegress, -, -, -⟩
    · exact hinv.flow_confinement L I J E hL hOld hcontained hE
    · rw [hagent] at hL
      rw [hegress] at hE
      exact Or.inl ((hallowGate hv).flow.speculative L E (Or.inl hL) hE)
  case flow_confinement_weak =>
    have hallowGate := begin_invocation.guard_verdict_allow hg
    have ht := begin_invocation.next_taint_levels hn
    have hallowField := begin_invocation.next_egress_allow_ceiling hn
    have hinspectField := begin_invocation.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallowField, hinspectField]
    rw [ht] at hL
    rcases contained_pending_cases hn hJ hcontained with
      hOld | ⟨-, hv, hagent, -, hegress, -, -, -⟩
    · exact hinv.flow_confinement_weak L I J E hL hOld hcontained hE
    · rw [hagent] at hL
      rw [hegress] at hE
      exact Or.inl ((hallowGate hv).flow.speculative L E (Or.inl hL) hE)
  case integrity_confinement =>
    have hallowGate := begin_invocation.guard_verdict_allow hg
    have hi := begin_invocation.next_integ_levels hn
    intro L I J hL hJ hcontained
    rw [hi] at hL
    rcases contained_pending_cases hn hJ hcontained with
      hOld | ⟨-, hv, hagent, hpolicy, -, -, -, -⟩
    · exact hinv.integrity_confinement L I J hL hOld hcontained
    · rw [hagent] at hL
      rw [hpolicy]
      exact Or.inl ((hallowGate hv).integ.speculative L (Or.inl hL))
  case integrity_confinement_weak =>
    have hallowGate := begin_invocation.guard_verdict_allow hg
    have hi := begin_invocation.next_integ_levels hn
    intro L I J hL hJ hcontained
    rw [hi] at hL
    rcases contained_pending_cases hn hJ hcontained with
      hOld | ⟨-, hv, hagent, hpolicy, -, -, -, -⟩
    · exact hinv.integrity_confinement_weak L I J hL hOld hcontained
    · rw [hagent] at hL
      rw [hpolicy]
      exact Or.inl ((hallowGate hv).integ.speculative L (Or.inl hL))
  case clearance_confinement =>
    have hallowGate := begin_invocation.guard_verdict_allow hg
    have ht := begin_invocation.next_taint_levels hn
    intro L I J hJ hcontained hspec
    unfold speculative_taint_contained at hspec
    rcases contained_pending_cases hn hJ hcontained with
      hOldJ | ⟨-, hvJ, hJagent, hJpolicy, -, -, -, -⟩
    · rcases hspec with hL | ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩
      · rw [ht] at hL
        exact hinv.clearance_confinement L I J hOldJ hcontained (Or.inl hL)
      · rcases contained_pending_cases hn hK hKcontained with
          hOldK | ⟨-, hvK, hKagentNew, hKpolicy, -, -, -, -⟩
        · exact hinv.clearance_confinement L I J hOldJ hcontained
            (Or.inr ⟨I2, K, hOldK, hKagent, hKcontained, hKlevel⟩)
        · have hJagentA : J.agent = a := hKagent.symm.trans hKagentNew
          rw [hKpolicy] at hKlevel
          rw [← hKlevel]
          exact (hallowGate hvK).clearance.pending I J hOldJ hJagentA
    · rw [hJpolicy]
      rcases hspec with hL | ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩
      · rw [ht] at hL
        rw [hJagent] at hL
        exact (hallowGate hvJ).clearance.speculative L (Or.inl hL)
      · rcases contained_pending_cases hn hK hKcontained with
          hOldK | ⟨-, -, hKagentNew, hKpolicy, -, -, -, -⟩
        · have hKagentA : K.agent = a := hKagent.trans hJagent
          exact (hallowGate hvJ).clearance.speculative L (Or.inr ⟨I2, K, hOldK, hKagentA, hKlevel⟩)
        · rw [hKpolicy] at hKlevel
          rw [← hKlevel]
          exact (hallowGate hvJ).clearance.self

/-- `invPP` (2 pairwise conjuncts), both manual: two contained records are old/old (the
pre-state invariant), old/newcomer (the gate's speculative arm covers the old record's
output), newcomer/old (the gate's pending arm), or the newcomer's self-pair (the gate's
newcomer arm). -/
theorem presPP_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict) :
    Preserves (begin_invocation a inv chal snap egr ah authorized v : Kav.Action St!)
      invPP := by
  intro s s' hinv hg hn
  refine ⟨?pending_flow_compat, ?pending_integ_compat⟩
  case pending_flow_compat =>
    have hallowGate := begin_invocation.guard_verdict_allow hg
    have hallowField := begin_invocation.next_egress_allow_ceiling hn
    have hinspectField := begin_invocation.next_egress_inspect_ceiling hn
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects
    rw [hallowField, hinspectField]
    rcases contained_pending_cases hn hJ1 hcontained1 with
      hOld1 | ⟨-, hv1, hagent1, hpolicy1, hegress1, -, -, -⟩
    · rcases contained_pending_cases hn hJ2 hcontained2 with
        hOld2 | ⟨-, hv2, hagent2, hpolicy2, hegress2, -, -, -⟩
      · exact hinv.pending_flow_compat I1 I2 J1 J2 E hOld1 hOld2 hagent hcontained1
          hcontained2 hE
      · have hJ1agent : J1.agent = a := hagent.trans hagent2
        rw [hegress2] at hE
        exact Or.inl ((hallowGate hv2).flow.speculative J1.policy.output_conf E
          (Or.inr ⟨I1, J1, hOld1, hJ1agent, rfl⟩) hE)
    · rcases contained_pending_cases hn hJ2 hcontained2 with
        hOld2 | ⟨-, hv2, hagent2, hpolicy2, hegress2, -, -, -⟩
      · have hJ2agent : J2.agent = a := hagent.symm.trans hagent1
        rw [hpolicy1]
        exact Or.inl ((hallowGate hv1).flow.pending_pairs I2 J2 E hOld2 hJ2agent hE)
      · rw [hegress2] at hE
        rw [hpolicy1]
        exact Or.inl ((hallowGate hv1).flow.newcomer E hE)
  case pending_integ_compat =>
    have hallowGate := begin_invocation.guard_verdict_allow hg
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    rcases contained_pending_cases hn hJ1 hcontained1 with
      hOld1 | ⟨-, hv1, hagent1, hpolicy1, -, -, -, -⟩
    · rcases contained_pending_cases hn hJ2 hcontained2 with
        hOld2 | ⟨-, hv2, hagent2, hpolicy2, -, -, -, -⟩
      · exact hinv.pending_integ_compat I1 I2 J1 J2 hOld1 hOld2 hagent hcontained1
          hcontained2
      · have hJ1agent : J1.agent = a := hagent.trans hagent2
        rw [hpolicy2]
        exact Or.inl ((hallowGate hv2).integ.speculative J1.policy.output_integ
          (Or.inr ⟨I1, J1, hOld1, hJ1agent, rfl⟩))
    · rcases contained_pending_cases hn hJ2 hcontained2 with
        hOld2 | ⟨-, hv2, hagent2, hpolicy2, -, -, -, -⟩
      · have hJ2agent : J2.agent = a := hagent.symm.trans hagent1
        rw [hpolicy1]
        exact Or.inl ((hallowGate hv1).integ.pending_pairs I2 J2 hOld2 hJ2agent)
      · rw [hpolicy1, hpolicy2]
        exact Or.inl (hallowGate hv1).integ.newcomer

/-- `invE` (6 evidence conjuncts): fully automated. -/
theorem presE_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict) :
    Preserves (begin_invocation a inv chal snap egr ah authorized v : Kav.Action St!)
      invE := by
  intro s s' hinv hg hn
  kav_discharge begin_invocation

/-- `invC` (3 crossing conjuncts): fully automated frame preservation. -/
theorem presC_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict) :
    Preserves (begin_invocation a inv chal snap egr ah authorized v : Kav.Action St!)
      invC := by
  intro s s' hinv _hg hn
  kav_discharge_lite begin_invocation

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict) :
    Preserves (begin_invocation a inv chal snap egr ah authorized v : Kav.Action St!)
      allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
     presP_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
     presPP_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
     presE_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
     presC_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn⟩

#print axioms pres_begin_invocation

end Tzimtzum
