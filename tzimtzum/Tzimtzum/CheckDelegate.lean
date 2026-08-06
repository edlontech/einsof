import Tzimtzum.Soundness.Common

/-! `delegate` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

theorem presS_delegate (grantor grantee : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') : invS s' := by
  kav_discharge_lite delegate

theorem presP_delegate (grantor grantee : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') : invP s' := by
  kav_discharge_lite delegate

theorem presPP_delegate (grantor grantee : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') : invPP s' := by
  kav_discharge_lite delegate

theorem presE_delegate (grantor grantee : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') : invE s' := by
  kav_discharge_lite delegate

-- This proof splits the conditional update of `dropGrantsOf` explicitly because the
-- simplifier needs the equality case before it can use the characterization lemma.
theorem presC_delegate (grantor grantee : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') : invC s' := by
  obtain ⟨hact, -, -, -, -, -, -, -, -, -, hgx, -, -, -, -, -⟩ := hn
  obtain ⟨-, -, -, -, hgb, hga, hgp⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro A D g h
    rw [hgx] at h
    by_cases hx : A = grantee
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h; exact hgb A D g h
  · intro A D g h
    rw [hgx] at h
    by_cases hx : A = grantee
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h
      rw [hact]
      exact Or.inl (hga A D g h)
  · intro A D g1 g2 h1 h2
    rw [hgx] at h1 h2
    by_cases hx : A = grantee
    · subst hx; rw [dropGrantsOf_self] at h1; exact absurd h1 (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h1 h2; exact hgp A D g1 g2 h1 h2

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_delegate (grantor grantee : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') : allInv s' :=
  ⟨presS_delegate grantor grantee s s' hinv hg hn,
   presP_delegate grantor grantee s s' hinv hg hn,
   presPP_delegate grantor grantee s s' hinv hg hn,
   presE_delegate grantor grantee s s' hinv hg hn,
   presC_delegate grantor grantee s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_delegate

end Tzimtzum
