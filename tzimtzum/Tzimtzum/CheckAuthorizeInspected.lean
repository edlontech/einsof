import Tzimtzum.Soundness.Common

/-! # Task 8 — `authorize_inspected` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

theorem presS_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (authorize_inspected inv sc att admit).guard s)
    (hn : (authorize_inspected inv sc att admit).next s s') : invS s' := by
  kav_discharge authorize_inspected

theorem presP_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (authorize_inspected inv sc att admit).guard s)
    (hn : (authorize_inspected inv sc att admit).next s s') : invP s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kav_discharge authorize_inspected
  · kav_discharge authorize_inspected
  · kav_discharge authorize_inspected
  · kav_discharge authorize_inspected
  · kav_discharge authorize_inspected
  · kav_discharge authorize_inspected
  · kav_discharge authorize_inspected
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, ht, -, hpen, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, hadmit, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, hflow, -, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    rw [ht] at hL
    rw [hpen] at hJ
    by_cases hnew : I = inv ∧ admit = true
    · simp only [if_pos hnew] at hJ
      have hEq := Option.some.inj hJ
      subst J
      obtain ⟨-, hadmits⟩ := hadmit hnew.2
      obtain ⟨-, -, -, -, -, -, -, hbegin⟩ := hadmits
      obtain ⟨-, -, -, ⟨hcheck, -, -⟩, -⟩ := hbegin
      rcases hcheck L E (Or.inl hL) hE with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
    · simp only [if_neg hnew] at hJ
      exact hflow L I J E hL hJ hcontained hE
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, ht, -, hpen, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, hadmit, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, hflow, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    rw [ht] at hL
    rw [hpen] at hJ
    by_cases hnew : I = inv ∧ admit = true
    · simp only [if_pos hnew] at hJ
      have hEq := Option.some.inj hJ
      subst J
      obtain ⟨-, hadmits⟩ := hadmit hnew.2
      obtain ⟨-, -, -, -, -, -, -, hbegin⟩ := hadmits
      obtain ⟨-, -, -, ⟨hcheck, -, -⟩, -⟩ := hbegin
      exact hcheck L E (Or.inl hL) hE
    · simp only [if_neg hnew] at hJ
      exact hflow L I J E hL hJ hcontained hE
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, hi, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, hadmit, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, hinteg, -, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    rw [hi] at hL
    rw [hpen] at hJ
    by_cases hnew : I = inv ∧ admit = true
    · simp only [if_pos hnew] at hJ
      have hEq := Option.some.inj hJ
      subst J
      obtain ⟨-, hadmits⟩ := hadmit hnew.2
      obtain ⟨-, -, -, -, -, -, -, hbegin⟩ := hadmits
      obtain ⟨-, -, -, -, ⟨hcheck, -, -⟩⟩ := hbegin
      rcases hcheck L (Or.inl hL) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
    · simp only [if_neg hnew] at hJ
      exact hinteg L I J hL hJ hcontained
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, hi, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, hadmit, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hinteg, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    rw [hi] at hL
    rw [hpen] at hJ
    by_cases hnew : I = inv ∧ admit = true
    · simp only [if_pos hnew] at hJ
      have hEq := Option.some.inj hJ
      subst J
      obtain ⟨-, hadmits⟩ := hadmit hnew.2
      obtain ⟨-, -, -, -, -, -, -, hbegin⟩ := hadmits
      obtain ⟨-, -, -, -, ⟨hcheck, -, -⟩⟩ := hbegin
      exact hcheck L (Or.inl hL)
    · simp only [if_neg hnew] at hJ
      exact hinteg L I J hL hJ hcontained
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, ht, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, hadmit, -⟩ := hguard
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hclear⟩, -, -, -⟩ := hinv
    have hchecks : admit = true → checkClearance s sc.agent sc.policy := by
      intro hadmitTrue
      obtain ⟨-, hadmits⟩ := hadmit hadmitTrue
      obtain ⟨-, -, -, -, -, -, -, hbegin⟩ := hadmits
      exact hbegin.2.2.1
    intro L I J hJ hcontained hspec
    unfold speculative_taint_contained at hspec
    rw [hpen] at hJ
    by_cases hnewJ : I = inv ∧ admit = true
    · simp only [if_pos hnewJ] at hJ
      have hEq := Option.some.inj hJ
      subst J
      obtain ⟨h2a, -, h2c⟩ := hchecks hnewJ.2
      rcases hspec with hL | ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩
      · rw [ht] at hL
        exact h2a L (Or.inl hL)
      · rw [hpen] at hK
        by_cases hnewK : I2 = inv ∧ admit = true
        · simp only [if_pos hnewK] at hK
          have hEqK := Option.some.inj hK
          subst K
          rw [← hKlevel]
          exact h2c
        · simp only [if_neg hnewK] at hK
          exact h2a L (Or.inr ⟨I2, K, hK, hKagent, hKlevel⟩)
    · simp only [if_neg hnewJ] at hJ
      rcases hspec with hL | ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩
      · rw [ht] at hL
        exact hclear L I J hJ hcontained (Or.inl hL)
      · rw [hpen] at hK
        by_cases hnewK : I2 = inv ∧ admit = true
        · simp only [if_pos hnewK] at hK
          have hEqK := Option.some.inj hK
          subst K
          obtain ⟨-, h2b, -⟩ := hchecks hnewK.2
          rw [← hKlevel]
          exact h2b I J hJ hKagent.symm
        · simp only [if_neg hnewK] at hK
          exact hclear L I J hJ hcontained
            (Or.inr ⟨I2, K, hK, hKagent, hKcontained, hKlevel⟩)

theorem presPP_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (authorize_inspected inv sc att admit).guard s)
    (hn : (authorize_inspected inv sc att admit).next s s') : invPP s' := by
  refine ⟨?_, ?_⟩
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, hadmit, -⟩ := hguard
    obtain ⟨-, -, ⟨hpair, -⟩, -, -⟩ := hinv
    have hchecks : admit = true → checkFlowAdmissible s sc.agent sc.policy sc.egress := by
      intro hadmitTrue
      obtain ⟨-, hadmits⟩ := hadmit hadmitTrue
      obtain ⟨-, -, -, -, -, -, -, hbegin⟩ := hadmits
      exact hbegin.2.2.2.1
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects vouched
    rw [hallow, hinspect]
    rw [hpen] at hJ1 hJ2
    by_cases hnew1 : I1 = inv ∧ admit = true
    · simp only [if_pos hnew1] at hJ1
      have hEq1 := Option.some.inj hJ1
      subst J1
      by_cases hnew2 : I2 = inv ∧ admit = true
      · simp only [if_pos hnew2] at hJ2
        have hEq2 := Option.some.inj hJ2
        subst J2
        rcases (hchecks hnew1.2).2.2 E hE with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · simp only [if_neg hnew2] at hJ2
        exact (hchecks hnew1.2).2.1 I2 J2 E hJ2 hagent.symm hE
    · simp only [if_neg hnew1] at hJ1
      by_cases hnew2 : I2 = inv ∧ admit = true
      · simp only [if_pos hnew2] at hJ2
        have hEq2 := Option.some.inj hJ2
        subst J2
        rcases (hchecks hnew2.2).1 J1.policy.output_conf E
            (Or.inr ⟨I1, J1, hJ1, hagent, rfl⟩) hE with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · simp only [if_neg hnew2] at hJ2
        exact hpair I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, -, -, -, -, hadmit, -⟩ := hguard
    obtain ⟨-, -, ⟨-, hpair⟩, -, -⟩ := hinv
    have hchecks : admit = true → checkIntegAdmissible s sc.agent sc.policy := by
      intro hadmitTrue
      obtain ⟨-, hadmits⟩ := hadmit hadmitTrue
      obtain ⟨-, -, -, -, -, -, -, hbegin⟩ := hadmits
      exact hbegin.2.2.2.2
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    unfold vouched
    rw [hpen] at hJ1 hJ2
    by_cases hnew1 : I1 = inv ∧ admit = true
    · simp only [if_pos hnew1] at hJ1
      have hEq1 := Option.some.inj hJ1
      subst J1
      by_cases hnew2 : I2 = inv ∧ admit = true
      · simp only [if_pos hnew2] at hJ2
        have hEq2 := Option.some.inj hJ2
        subst J2
        rcases (hchecks hnew1.2).2.2 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · simp only [if_neg hnew2] at hJ2
        exact (hchecks hnew1.2).2.1 I2 J2 hJ2 hagent.symm
    · simp only [if_neg hnew1] at hJ1
      by_cases hnew2 : I2 = inv ∧ admit = true
      · simp only [if_pos hnew2] at hJ2
        have hEq2 := Option.some.inj hJ2
        subst J2
        rcases (hchecks hnew2.2).1 J1.policy.output_integ
            (Or.inr ⟨I1, J1, hJ1, hagent, rfl⟩) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, ⟨att.id, rfl⟩⟩
      · simp only [if_neg hnew2] at hJ2
        exact hpair I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2

theorem presE_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (authorize_inspected inv sc att admit).guard s)
    (hn : (authorize_inspected inv sc att admit).next s s') : invE s' := by
  kav_discharge_lite authorize_inspected

theorem presC_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (_hg : (authorize_inspected inv sc att admit).guard s)
    (hn : (authorize_inspected inv sc att admit).next s s') : invC s' := by
  kav_discharge_lite authorize_inspected

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest ContentHash)
    (admit : Bool)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (authorize_inspected inv sc att admit).guard s)
    (hn : (authorize_inspected inv sc att admit).next s s') : allInv s' :=
  ⟨presS_authorize_inspected inv sc att admit s s' hinv hg hn,
   presP_authorize_inspected inv sc att admit s s' hinv hg hn,
   presPP_authorize_inspected inv sc att admit s s' hinv hg hn,
   presE_authorize_inspected inv sc att admit s s' hinv hg hn,
   presC_authorize_inspected inv sc att admit s s' hinv hg hn⟩

#print axioms pres_authorize_inspected

end Tzimtzum
