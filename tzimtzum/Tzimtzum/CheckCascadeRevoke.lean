import Tzimtzum.Soundness.Common

/-! `cascade_revoke` preserves the bundle (one theorem per sub-bundle). Cascading removal
of an orphaned child drops the same agent-owned state as `revoke`; `revocation_clean` and
the `invC` grant conjuncts are manual because the simplifier needs the drop-helper key
case split first. Everything else is automated. -/

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

/-- `revocation_clean`, manual: the drop helpers empty the removed child's state, and any
other inactive agent's cleanliness is inherited from the pre-state. -/
theorem revocation_clean_cascade_revoke (child prnt : AgentId) :
    Preserves (cascade_revoke child prnt : Kav.Action St!) revocation_clean := by
  intro s s' hinv hg hn
  have hact := cascade_revoke.next_agent_active hn
  have ht := cascade_revoke.next_taint_levels hn
  have hi := cascade_revoke.next_integ_levels hn
  have hpen := cascade_revoke.next_pending hn
  have hch := cascade_revoke.next_challenges hn
  have hgx := cascade_revoke.next_crossing_grants hn
  intro A hA
  rw [hact] at hA
  by_cases hx : A = child
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
    obtain ⟨hrt, hri, hrp, hrch, hrg⟩ := hinv.revocation_clean A hAin
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro L hL; rw [ht] at hL; exact hrt L hL.1
    · intro Li hLi; rw [hi] at hLi; exact hri Li hLi.1
    · intro I J h; rw [hpen] at h; exact hrp I J (dropPendingOf_eq_some _ _ _ _ |>.mp h).1
    · intro I sc h; rw [hch] at h
      exact hrch I sc (dropChallengesOf_eq_some _ _ _ _ |>.mp h).1
    · intro D; rw [hgx]; rw [dropGrantsOf_other _ _ _ _ hx]; exact hrg D

/-- `invS` (9 structural conjuncts): automated except `revocation_clean` above. -/
theorem presS_cascade_revoke (child prnt : AgentId) :
    Preserves (cascade_revoke child prnt : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    revocation_clean_cascade_revoke child prnt s s' hinv hg hn, ?_⟩
  all_goals kav_discharge_lite cascade_revoke

/-- `invP` (12 pending/gate conjuncts): fully automated. -/
theorem presP_cascade_revoke (child prnt : AgentId) :
    Preserves (cascade_revoke child prnt : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  kav_discharge_lite cascade_revoke

/-- `invPP` (2 pairwise conjuncts): fully automated. -/
theorem presPP_cascade_revoke (child prnt : AgentId) :
    Preserves (cascade_revoke child prnt : Kav.Action St!) invPP := by
  intro s s' hinv hg hn
  kav_discharge_lite cascade_revoke

/-- `invE` (6 evidence conjuncts): fully automated. -/
theorem presE_cascade_revoke (child prnt : AgentId) :
    Preserves (cascade_revoke child prnt : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  kav_discharge_lite cascade_revoke

/-- `invC` (3 crossing conjuncts), manual: `dropGrantsOf` needs the child/other key case
split before the characterization lemmas apply. A child-keyed grant is dropped outright;
any other key defers to the pre-state invariant. -/
theorem presC_cascade_revoke (child prnt : AgentId) :
    Preserves (cascade_revoke child prnt : Kav.Action St!) invC := by
  intro s s' hinv hg hn
  have hact := cascade_revoke.next_agent_active hn
  have hgx := cascade_revoke.next_crossing_grants hn
  refine ⟨?grant_bounded, ?grant_active, ?grant_pinned⟩
  case grant_bounded =>
    intro A D g h
    rw [hgx] at h
    by_cases hx : A = child
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h; exact hinv.grant_bounded A D g h
  case grant_active =>
    intro A D g h
    rw [hgx] at h
    by_cases hx : A = child
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h
      rw [hact]
      exact ⟨hinv.grant_active A D g h, hx⟩
  case grant_pinned =>
    intro A D g1 g2 h1 h2
    rw [hgx] at h1 h2
    by_cases hx : A = child
    · subst hx; rw [dropGrantsOf_self] at h1; exact absurd h1 (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h1 h2; exact hinv.grant_pinned A D g1 g2 h1 h2

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_cascade_revoke (child prnt : AgentId) :
    Preserves (cascade_revoke child prnt : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_cascade_revoke child prnt s s' hinv hg hn,
     presP_cascade_revoke child prnt s s' hinv hg hn,
     presPP_cascade_revoke child prnt s s' hinv hg hn,
     presE_cascade_revoke child prnt s s' hinv hg hn,
     presC_cascade_revoke child prnt s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms revocation_clean_cascade_revoke
#print axioms pres_cascade_revoke

end Tzimtzum
