import Tzimtzum.Soundness.Common
import Tzimtzum.CheckInit
import Tzimtzum.CheckRegisterTool
import Tzimtzum.CheckUnregisterTool
import Tzimtzum.CheckDelegate
import Tzimtzum.CheckGrantCapability
import Tzimtzum.CheckGrantCrossing
import Tzimtzum.CheckRevoke
import Tzimtzum.CheckCascadeRevoke
import Tzimtzum.CheckIngest
import Tzimtzum.CheckSettleInvocation
import Tzimtzum.CheckAuthorizeInspected
import Tzimtzum.CheckBeginInvocation
import Tzimtzum.CheckCrossOutput

/-!
# TzimtzumV4 — soundness aggregator (Tasks 7–10)

Init VCs plus full-bundle preservation for all twelve actions, assembled through
`Kav.reachable_sound` as `kav_sound` and its sort-polymorphic counterpart `kav_soundP`.
-/

namespace Tzimtzum

/-- Every opaque-sort initial state establishes the full invariant bundle. -/
theorem hinit_bundle : ∀ s, ksystem.init s → allInv s := by
  intro s hi
  exact init_sound s hi

/-- Every registered opaque-sort action preserves the full invariant bundle. -/
theorem hpres_bundle : ∀ na ∈ ksystem.actions, ∀ s s',
    allInv s → na.2.guard s → na.2.next s s' → allInv s' := by
  intro na hmem s s' hinv _hg hn
  simp only [ksystem, system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Kav.close1] at hn
    obtain ⟨tool, hg, hn⟩ := hn
    exact pres_register_tool tool s s' hinv hg hn
  · simp only [Kav.close1] at hn
    obtain ⟨tool, hg, hn⟩ := hn
    exact pres_unregister_tool tool s s' hinv hg hn
  · simp only [Kav.close2] at hn
    obtain ⟨grantor, grantee, hg, hn⟩ := hn
    exact pres_delegate grantor grantee s s' hinv hg hn
  · simp only [Kav.close3] at hn
    obtain ⟨prnt, child, cap, hg, hn⟩ := hn
    exact pres_grant_capability prnt child cap s s' hinv hg hn
  · simp only [Kav.close4] at hn
    obtain ⟨grantor, agent, d, n, hg, hn⟩ := hn
    exact pres_grant_crossing grantor agent d n s s' hinv hg hn
  · simp only [Kav.close2] at hn
    obtain ⟨prnt, target, hg, hn⟩ := hn
    exact pres_revoke prnt target s s' hinv hg hn
  · simp only [Kav.close2] at hn
    obtain ⟨child, prnt, hg, hn⟩ := hn
    exact pres_cascade_revoke child prnt s s' hinv hg hn
  · simp only [Kav.close5] at hn
    obtain ⟨a, src, pconf, pinteg, dispo, hg, hn⟩ := hn
    exact pres_ingest a src pconf pinteg dispo s s' hinv hg hn
  · simp only [Kav.close8] at hn
    obtain ⟨a, inv, chal, snap, egr, ah, authorized, v, hg, hn⟩ := hn
    exact pres_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn
  · simp only [Kav.close4] at hn
    obtain ⟨inv, sc, att, admit, hg, hn⟩ := hn
    exact pres_authorize_inspected inv sc att admit s s' hinv hg hn
  · simp only [Kav.close7] at hn
    obtain ⟨inv, a, dispo, outcome, clvl, ilvl, att, hg, hn⟩ := hn
    exact pres_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn
  · simp only [Kav.close3] at hn
    obtain ⟨q, branch, dispo, hg, hn⟩ := hn
    exact pres_cross_output q branch dispo s s' hinv hg hn

/-- Every reachable opaque-sort V4 state satisfies all 32 invariants. -/
theorem kav_sound (s : KSt) (h : Kav.Reachable ksystem s) : allInv s :=
  Kav.reachable_sound hinit_bundle hpres_bundle h

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

local notation "PSt" =>
  St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
    AssignmentDigest PolicyDigest ContentHash

/-- Every initial state establishes the bundle at an arbitrary sort instantiation. -/
theorem hinit_bundleP :
    ∀ s : PSt, (system : Kav.TransitionSystem PSt).init s → allInv s := by
  intro s hi
  exact init_sound s hi

/-- Every registered action preserves the bundle at an arbitrary sort instantiation. -/
theorem hpres_bundleP :
    ∀ na ∈ (system : Kav.TransitionSystem PSt).actions, ∀ s s' : PSt,
      allInv s → na.2.guard s → na.2.next s s' → allInv s' := by
  intro na hmem s s' hinv _hg hn
  simp only [system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Kav.close1] at hn
    obtain ⟨tool, hg, hn⟩ := hn
    exact pres_register_tool tool s s' hinv hg hn
  · simp only [Kav.close1] at hn
    obtain ⟨tool, hg, hn⟩ := hn
    exact pres_unregister_tool tool s s' hinv hg hn
  · simp only [Kav.close2] at hn
    obtain ⟨grantor, grantee, hg, hn⟩ := hn
    exact pres_delegate grantor grantee s s' hinv hg hn
  · simp only [Kav.close3] at hn
    obtain ⟨prnt, child, cap, hg, hn⟩ := hn
    exact pres_grant_capability prnt child cap s s' hinv hg hn
  · simp only [Kav.close4] at hn
    obtain ⟨grantor, agent, d, n, hg, hn⟩ := hn
    exact pres_grant_crossing grantor agent d n s s' hinv hg hn
  · simp only [Kav.close2] at hn
    obtain ⟨prnt, target, hg, hn⟩ := hn
    exact pres_revoke prnt target s s' hinv hg hn
  · simp only [Kav.close2] at hn
    obtain ⟨child, prnt, hg, hn⟩ := hn
    exact pres_cascade_revoke child prnt s s' hinv hg hn
  · simp only [Kav.close5] at hn
    obtain ⟨a, src, pconf, pinteg, dispo, hg, hn⟩ := hn
    exact pres_ingest a src pconf pinteg dispo s s' hinv hg hn
  · simp only [Kav.close8] at hn
    obtain ⟨a, inv, chal, snap, egr, ah, authorized, v, hg, hn⟩ := hn
    exact pres_begin_invocation a inv chal snap egr ah authorized v s s' hinv hg hn
  · simp only [Kav.close4] at hn
    obtain ⟨inv, sc, att, admit, hg, hn⟩ := hn
    exact pres_authorize_inspected inv sc att admit s s' hinv hg hn
  · simp only [Kav.close7] at hn
    obtain ⟨inv, a, dispo, outcome, clvl, ilvl, att, hg, hn⟩ := hn
    exact pres_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn
  · simp only [Kav.close3] at hn
    obtain ⟨q, branch, dispo, hg, hn⟩ := hn
    exact pres_cross_output q branch dispo s s' hinv hg hn

/-- Every reachable V4 state satisfies the bundle at an arbitrary sort instantiation. -/
theorem kav_soundP (s : PSt)
    (h : Kav.Reachable (system : Kav.TransitionSystem PSt) s) : allInv s :=
  Kav.reachable_sound hinit_bundleP hpres_bundleP h

#print axioms kav_sound
#print axioms kav_soundP

end Tzimtzum
