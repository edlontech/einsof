import Tzimtzum.Soundness.Common

/-! # Task 7 — `delegate` preserves the bundle (one theorem per sub-bundle). -/

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

-- Manual VC (the V3 `revocation_clean` frame-extraction pattern): the cascade stalls on
-- the `Classical.propDecidable` instance inside `dropGrantsOf` — its `_other` lemma is
-- hypothesis-conditional, and neither `grind` nor `duper` performs the case split that
-- makes it applicable. The 16-component `obtain` is positional; `crossing_grants`' type is
-- unique among the fields, so a reorder breaks this at elaboration rather than silently.
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

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_delegate (grantor grantee : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (delegate grantor grantee).guard s) (hn : (delegate grantor grantee).next s s') : allInv s' :=
  ⟨presS_delegate grantor grantee s s' hinv hg hn,
   presP_delegate grantor grantee s s' hinv hg hn,
   presPP_delegate grantor grantee s s' hinv hg hn,
   presE_delegate grantor grantee s s' hinv hg hn,
   presC_delegate grantor grantee s s' hinv hg hn⟩

-- Axiom audit (in place, per the V3 manual-VC pattern): the cascades end in `auto`/`duper`
-- under `auto.native true`, so a natively-compiled closure would add `Lean.ofReduceBool`
-- to the trust base silently. These must print only `propext`, `Classical.choice`,
-- `Quot.sound`.
#print axioms pres_delegate

end Tzimtzum
