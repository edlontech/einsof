import Tzimtzum.Soundness.Common

/-! # Task 7 — `revoke` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

-- Manual VC, same family as `presC_revoke`: `revocation_clean` needs the newly-inactive
-- agent's residue proved absent through all three drop helpers.
theorem revocation_clean_revoke (prnt target : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (revoke prnt target).guard s) (hn : (revoke prnt target).next s s') :
    revocation_clean s' := by
  obtain ⟨hact, -, -, ht, hi, hpen, hch, -, -, -, hgx, -, -, -, -, -⟩ := hn
  obtain ⟨⟨-, -, -, -, -, -, -, hrc, -⟩, -, -, -, -⟩ := hinv
  intro A hA
  rw [hact] at hA
  by_cases hx : A = target
  · subst hx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro L hL; rw [ht] at hL; exact hL.2 rfl
    · intro Li hLi; rw [hi] at hLi; exact hLi.2 rfl
    · intro I J h; rw [hpen] at h; exact (dropPendingOf_eq_some _ _ _ _ |>.mp h).2
    · intro I sc h; rw [hch] at h; exact (dropChallengesOf_eq_some _ _ _ _ |>.mp h).2
    · intro D; rw [hgx]; exact dropGrantsOf_self _ _ _
  · have hAin : ¬ s.agent_active A := by
      intro hA'
      exact hA (by simp [hA', hx])
    obtain ⟨hrt, hri, hrp, hrch, hrg⟩ := hrc A hAin
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro L hL; rw [ht] at hL; exact hrt L hL.1
    · intro Li hLi; rw [hi] at hLi; exact hri Li hLi.1
    · intro I J h; rw [hpen] at h; exact hrp I J (dropPendingOf_eq_some _ _ _ _ |>.mp h).1
    · intro I sc h; rw [hch] at h
      exact hrch I sc (dropChallengesOf_eq_some _ _ _ _ |>.mp h).1
    · intro D; rw [hgx]; rw [dropGrantsOf_other _ _ _ _ hx]; exact hrg D

theorem presS_revoke (prnt target : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (revoke prnt target).guard s) (hn : (revoke prnt target).next s s') : invS s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    revocation_clean_revoke prnt target s s' hinv hg hn, ?_⟩
  all_goals kav_discharge_lite revoke

theorem presP_revoke (prnt target : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (revoke prnt target).guard s) (hn : (revoke prnt target).next s s') : invP s' := by
  kav_discharge_lite revoke

theorem presPP_revoke (prnt target : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (revoke prnt target).guard s) (hn : (revoke prnt target).next s s') : invPP s' := by
  kav_discharge_lite revoke

theorem presE_revoke (prnt target : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (revoke prnt target).guard s) (hn : (revoke prnt target).next s s') : invE s' := by
  kav_discharge_lite revoke

-- Manual VC (the V3 `revocation_clean` frame-extraction pattern): the cascade stalls on
-- the `Classical.propDecidable` instance inside `dropGrantsOf` — its `_other` lemma is
-- hypothesis-conditional, and neither `grind` nor `duper` performs the case split that
-- makes it applicable. The 16-component `obtain` is positional; `crossing_grants`' type is
-- unique among the fields, so a reorder breaks this at elaboration rather than silently.
theorem presC_revoke (prnt target : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (revoke prnt target).guard s) (hn : (revoke prnt target).next s s') : invC s' := by
  obtain ⟨hact, -, -, -, -, -, -, -, -, -, hgx, -, -, -, -, -⟩ := hn
  obtain ⟨-, -, -, -, hgb, hga, hgp⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro A D g h
    rw [hgx] at h
    by_cases hx : A = target
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h; exact hgb A D g h
  · intro A D g h
    rw [hgx] at h
    by_cases hx : A = target
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h
      rw [hact]
      exact ⟨hga A D g h, hx⟩
  · intro A D g1 g2 h1 h2
    rw [hgx] at h1 h2
    by_cases hx : A = target
    · subst hx; rw [dropGrantsOf_self] at h1; exact absurd h1 (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h1 h2; exact hgp A D g1 g2 h1 h2

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_revoke (prnt target : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (revoke prnt target).guard s) (hn : (revoke prnt target).next s s') : allInv s' :=
  ⟨presS_revoke prnt target s s' hinv hg hn,
   presP_revoke prnt target s s' hinv hg hn,
   presPP_revoke prnt target s s' hinv hg hn,
   presE_revoke prnt target s s' hinv hg hn,
   presC_revoke prnt target s s' hinv hg hn⟩

-- Axiom audit (in place, per the V3 manual-VC pattern): the cascades end in `auto`/`duper`
-- under `auto.native true`, so a natively-compiled closure would add `Lean.ofReduceBool`
-- to the trust base silently. These must print only `propext`, `Classical.choice`,
-- `Quot.sound`.
#print axioms revocation_clean_revoke
#print axioms pres_revoke

end Tzimtzum
