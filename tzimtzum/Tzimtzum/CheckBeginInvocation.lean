import Tzimtzum.Soundness.Common

/-! # Task 9 — `begin_invocation` preserves the bundle (one theorem per sub-bundle).

The constructor-match dispatch mandated by E26 keeps the update elaborable. The remaining
manual proofs below are per-conjunct saturation workarounds, not weakened statements.
-/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- A contained post-begin record is either an old record or the strict-ALLOW newcomer.
The monitor branches insert `monitor_bypassed` records and the enforce inspection branch
inserts no pending record, so neither can inhabit the second arm. -/
theorem begin_contained_pending_cases (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s')
    (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) (hcontained : contained J) :
    s.pending I = some J ∨
      (I = inv ∧ v = Verdict.allow ∧ J.agent = a ∧ J.policy = snap ∧ J.egress = egr
        ∧ J.admission = Admission.plain ∧ J.authorized = authorized ∧ ¬ J.quarantined) := by
  obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
  rw [hpen] at hJ
  by_cases hI : I = inv
  · subst I
    right
    cases v <;> cases hmode : s.mode <;>
      simp [hmode] at hJ <;> cases hJ <;> simp [contained] at hcontained ⊢
  · left
    simpa only [if_neg hI] using hJ

theorem presS_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') : invS s' := by
  kav_discharge begin_invocation

theorem presP_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') : invP s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kav_discharge begin_invocation
  · kav_discharge begin_invocation
  · kav_discharge begin_invocation
  · kav_discharge begin_invocation
  · kav_discharge begin_invocation
  · kav_discharge begin_invocation
  · kav_discharge begin_invocation
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallowField, hinspectField, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, -, -, hallowGate, -, -, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, hflow, -, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallowField, hinspectField]
    rw [ht] at hL
    rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I J hJ
        hcontained with hOld | ⟨-, hv, hagent, -, hegress, -, -, -⟩
    · exact hflow L I J E hL hOld hcontained hE
    · rw [hagent] at hL
      rw [hegress] at hE
      obtain ⟨-, -, -, ⟨hcheck, -, -⟩, -⟩ := hallowGate hv
      exact Or.inl (hcheck L E (Or.inl hL) hE)
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallowField, hinspectField, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, -, -, hallowGate, -, -, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, hflow, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallowField, hinspectField]
    rw [ht] at hL
    rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I J hJ
        hcontained with hOld | ⟨-, hv, hagent, -, hegress, -, -, -⟩
    · exact hflow L I J E hL hOld hcontained hE
    · rw [hagent] at hL
      rw [hegress] at hE
      obtain ⟨-, -, -, ⟨hcheck, -, -⟩, -⟩ := hallowGate hv
      exact Or.inl (hcheck L E (Or.inl hL) hE)
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, -, -, hallowGate, -, -, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, hinteg, -, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    rw [hi] at hL
    rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I J hJ
        hcontained with hOld | ⟨-, hv, hagent, hpolicy, -, -, -, -⟩
    · exact hinteg L I J hL hOld hcontained
    · rw [hagent] at hL
      rw [hpolicy]
      obtain ⟨-, -, -, -, ⟨hcheck, -, -⟩⟩ := hallowGate hv
      exact Or.inl (hcheck L (Or.inl hL))
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, -, -, hallowGate, -, -, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hinteg, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    rw [hi] at hL
    rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I J hJ
        hcontained with hOld | ⟨-, hv, hagent, hpolicy, -, -, -, -⟩
    · exact hinteg L I J hL hOld hcontained
    · rw [hagent] at hL
      rw [hpolicy]
      obtain ⟨-, -, -, -, ⟨hcheck, -, -⟩⟩ := hallowGate hv
      exact Or.inl (hcheck L (Or.inl hL))
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, -, -, hallowGate, -, -, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hclear⟩, -, -, -⟩ := hinv
    intro L I J hJ hcontained hspec
    unfold speculative_taint_contained at hspec
    rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I J hJ
        hcontained with hOldJ | ⟨-, hvJ, hJagent, hJpolicy, -, -, -, -⟩
    · rcases hspec with hL | ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩
      · rw [ht] at hL
        exact hclear L I J hOldJ hcontained (Or.inl hL)
      · rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn
            I2 K hK hKcontained with hOldK | ⟨-, hvK, hKagentNew, hKpolicy, -, -, -, -⟩
        · exact hclear L I J hOldJ hcontained
            (Or.inr ⟨I2, K, hOldK, hKagent, hKcontained, hKlevel⟩)
        · obtain ⟨-, -, ⟨-, h2b, -⟩, -, -⟩ := hallowGate hvK
          have hJagentA : J.agent = a := hKagent.symm.trans hKagentNew
          rw [hKpolicy] at hKlevel
          rw [← hKlevel]
          exact h2b I J hOldJ hJagentA
    · rw [hJpolicy]
      obtain ⟨-, -, ⟨h2a, -, h2c⟩, -, -⟩ := hallowGate hvJ
      rcases hspec with hL | ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩
      · rw [ht] at hL
        rw [hJagent] at hL
        exact h2a L (Or.inl hL)
      · rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn
            I2 K hK hKcontained with hOldK | ⟨-, -, hKagentNew, hKpolicy, -, -, -, -⟩
        · have hKagentA : K.agent = a := hKagent.trans hJagent
          exact h2a L (Or.inr ⟨I2, K, hOldK, hKagentA, hKlevel⟩)
        · rw [hKpolicy] at hKlevel
          rw [← hKlevel]
          exact h2c

theorem presPP_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') : invPP s' := by
  refine ⟨?_, ?_⟩
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hallowField, hinspectField, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, -, -, hallowGate, -, -, -⟩ := hguard
    obtain ⟨-, -, ⟨hpair, -⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects
    rw [hallowField, hinspectField]
    rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I1 J1
        hJ1 hcontained1 with hOld1 | ⟨-, hv1, hagent1, hpolicy1, hegress1, -, -, -⟩
    · rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I2 J2
          hJ2 hcontained2 with hOld2 | ⟨-, hv2, hagent2, hpolicy2, hegress2, -, -, -⟩
      · exact hpair I1 I2 J1 J2 E hOld1 hOld2 hagent hcontained1 hcontained2 hE
      · obtain ⟨-, -, -, ⟨h3a, -, -⟩, -⟩ := hallowGate hv2
        have hJ1agent : J1.agent = a := hagent.trans hagent2
        rw [hegress2] at hE
        exact Or.inl (h3a J1.policy.output_conf E
          (Or.inr ⟨I1, J1, hOld1, hJ1agent, rfl⟩) hE)
    · rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I2 J2
          hJ2 hcontained2 with hOld2 | ⟨-, hv2, hagent2, hpolicy2, hegress2, -, -, -⟩
      · obtain ⟨-, -, -, ⟨-, h3b, -⟩, -⟩ := hallowGate hv1
        have hJ2agent : J2.agent = a := hagent.symm.trans hagent1
        rw [hpolicy1]
        exact Or.inl (h3b I2 J2 E hOld2 hJ2agent hE)
      · obtain ⟨-, -, -, ⟨-, -, h3c⟩, -⟩ := hallowGate hv1
        rw [hegress2] at hE
        rw [hpolicy1]
        exact Or.inl (h3c E hE)
  · have hguard := hg
    obtain ⟨-, -, -, -, -, -, -, -, -, hallowGate, -, -, -⟩ := hguard
    obtain ⟨-, -, ⟨-, hpair⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I1 J1
        hJ1 hcontained1 with hOld1 | ⟨-, hv1, hagent1, hpolicy1, -, -, -, -⟩
    · rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I2 J2
          hJ2 hcontained2 with hOld2 | ⟨-, hv2, hagent2, hpolicy2, -, -, -, -⟩
      · exact hpair I1 I2 J1 J2 hOld1 hOld2 hagent hcontained1 hcontained2
      · obtain ⟨-, -, -, -, ⟨h5a, -, -⟩⟩ := hallowGate hv2
        have hJ1agent : J1.agent = a := hagent.trans hagent2
        rw [hpolicy2]
        exact Or.inl (h5a J1.policy.output_integ
          (Or.inr ⟨I1, J1, hOld1, hJ1agent, rfl⟩))
    · rcases begin_contained_pending_cases a inv chal snap egr ah authorized v s s' hn I2 J2
          hJ2 hcontained2 with hOld2 | ⟨-, hv2, hagent2, hpolicy2, -, -, -, -⟩
      · obtain ⟨-, -, -, -, ⟨-, h5b, -⟩⟩ := hallowGate hv1
        have hJ2agent : J2.agent = a := hagent.symm.trans hagent1
        rw [hpolicy1]
        exact Or.inl (h5b I2 J2 hOld2 hJ2agent)
      · obtain ⟨-, -, -, -, ⟨-, -, h5c⟩⟩ := hallowGate hv1
        rw [hpolicy1, hpolicy2]
        exact Or.inl h5c

theorem presE_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') : invE s' := by
  kav_discharge begin_invocation

theorem presC_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (_hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') : invC s' := by
  kav_discharge_lite begin_invocation

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (begin_invocation a inv chal snap egr ah authorized v).guard s)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') : allInv s' :=
  ⟨presS_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
   presP_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
   presPP_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
   presE_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn,
   presC_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn⟩

#print axioms pres_begin_invocation

end Tzimtzum
