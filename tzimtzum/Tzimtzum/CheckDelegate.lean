import Tzimtzum.Soundness.Common

/-! `delegate` preserves the bundle (one theorem per sub-bundle). The grantee starts with
no capabilities, labels, pending records, challenges, or grants, so four sub-bundles are
fully automated; only `invC` is manual, because the simplifier needs the `dropGrantsOf`
key case split before it can use the characterization lemmas. -/

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

/-- `invS` (9 structural conjuncts): fully automated. -/
theorem presS_delegate (grantor grantee : AgentId) :
    Preserves (delegate grantor grantee : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  kav_discharge_lite delegate

/-- `invP` (12 pending/gate conjuncts): fully automated. -/
theorem presP_delegate (grantor grantee : AgentId) :
    Preserves (delegate grantor grantee : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  kav_discharge_lite delegate

/-- `invPP` (2 pairwise conjuncts): fully automated. -/
theorem presPP_delegate (grantor grantee : AgentId) :
    Preserves (delegate grantor grantee : Kav.Action St!) invPP := by
  intro s s' hinv hg hn
  kav_discharge_lite delegate

/-- `invE` (6 evidence conjuncts): fully automated. -/
theorem presE_delegate (grantor grantee : AgentId) :
    Preserves (delegate grantor grantee : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  kav_discharge_lite delegate

/-- `invC` (3 crossing conjuncts), manual: `dropGrantsOf` needs the grantee/other key case
split before the characterization lemmas apply. A grantee-keyed grant is dropped outright;
any other key defers to the pre-state invariant. -/
theorem presC_delegate (grantor grantee : AgentId) :
    Preserves (delegate grantor grantee : Kav.Action St!) invC := by
  intro s s' hinv hg hn
  have hact := delegate.next_agent_active hn
  have hgx := delegate.next_crossing_grants hn
  refine ⟨?grant_bounded, ?grant_active, ?grant_pinned⟩
  case grant_bounded =>
    intro A D g h
    rw [hgx] at h
    by_cases hx : A = grantee
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h; exact hinv.grant_bounded A D g h
  case grant_active =>
    intro A D g h
    rw [hgx] at h
    by_cases hx : A = grantee
    · subst hx; rw [dropGrantsOf_self] at h; exact absurd h (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h
      rw [hact]
      exact Or.inl (hinv.grant_active A D g h)
  case grant_pinned =>
    intro A D g1 g2 h1 h2
    rw [hgx] at h1 h2
    by_cases hx : A = grantee
    · subst hx; rw [dropGrantsOf_self] at h1; exact absurd h1 (by simp)
    · rw [dropGrantsOf_other _ _ _ _ hx] at h1 h2; exact hinv.grant_pinned A D g1 g2 h1 h2

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_delegate (grantor grantee : AgentId) :
    Preserves (delegate grantor grantee : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_delegate grantor grantee s s' hinv hg hn,
     presP_delegate grantor grantee s s' hinv hg hn,
     presPP_delegate grantor grantee s s' hinv hg hn,
     presE_delegate grantor grantee s s' hinv hg hn,
     presC_delegate grantor grantee s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_delegate

end Tzimtzum
