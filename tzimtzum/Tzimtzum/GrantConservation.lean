import Tzimtzum.Soundness.Common

/-!
# Crossing-grant conservation

`grant_crossing` is the only registered action that can increase remaining crossing uses. Every
other registered action preserves, deletes, or decrements each grant, so remaining uses are
pointwise non-increasing outside that provisioning action.
-/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- Remaining uses at a key, with an absent grant interpreted as zero. -/
def grantRemaining
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (d : AssignmentDigest) : Nat :=
  match s.crossing_grants a d with
  | some g => g.remaining
  | none => 0

private theorem grant_noninc_of_frame (s s' : KSt)
    (hgrants : s'.crossing_grants = s.crossing_grants) :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  intro A D
  rw [grantRemaining, grantRemaining, hgrants]
  exact Nat.le_refl _

private theorem grant_noninc_of_drop (s s' : KSt) (removed : KAgent)
    (hgrants : s'.crossing_grants = dropGrantsOf s.crossing_grants removed) :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  intro A D
  rw [grantRemaining, grantRemaining, hgrants]
  by_cases hA : A = removed
  · subst A
    simp only [dropGrantsOf_self]
    exact Nat.zero_le _
  · rw [dropGrantsOf_other _ _ _ _ hA]
    exact Nat.le_refl _

private theorem grant_noninc_register_tool (tool : KTool) (s s' : KSt)
    (hn : (register_tool tool).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_frame s s' hgrants

private theorem grant_noninc_unregister_tool (tool : KTool) (s s' : KSt)
    (hn : (unregister_tool tool).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_frame s s' hgrants

private theorem grant_noninc_delegate (grantor grantee : KAgent) (s s' : KSt)
    (hn : (delegate grantor grantee).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_drop s s' grantee hgrants

private theorem grant_noninc_grant_capability (prnt child : KAgent) (cap : KCap)
    (s s' : KSt) (hn : (grant_capability prnt child cap).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_frame s s' hgrants

private theorem grant_noninc_revoke (prnt target : KAgent) (s s' : KSt)
    (hn : (revoke prnt target).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_drop s s' target hgrants

private theorem grant_noninc_cascade_revoke (child prnt : KAgent) (s s' : KSt)
    (hn : (cascade_revoke child prnt).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_drop s s' child hgrants

private theorem grant_noninc_ingest (a : KAgent) (src : Option KAgent) (pconf : ConfLevel)
    (pinteg : IntegLevel) (dispo : Disposition) (s s' : KSt)
    (hn : (ingest a src pconf pinteg dispo).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_frame s s' hgrants

private theorem grant_noninc_begin_invocation (a : KAgent) (inv : KInv) (chal : KChallenge)
    (snap : KSnapshot) (egr : KEgress → Prop) (ah : KContentHash) (authorized : Prop)
    (v : Verdict) (s s' : KSt)
    (hn : (begin_invocation a inv chal snap egr ah authorized v).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_frame s s' hgrants

private theorem grant_noninc_authorize_inspected (inv : KInv) (sc : KChallengeScope)
    (att : InspectionAttestation KInv KChallenge KAttest KPolicy KContentHash) (admit : Bool)
    (s s' : KSt) (hn : (authorize_inspected inv sc att admit).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_frame s s' hgrants

private theorem grant_noninc_settle_invocation (inv : KInv) (a : KAgent)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation KInv KAttest)) (s s' : KSt)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  exact grant_noninc_of_frame s s' hgrants

private theorem grant_noninc_cross_output
    (q : CrossInput KAgent KAttest KCrossing KAssignment KContentHash)
    (branch : CrossBranch) (dispo : Disposition) (s s' : KSt)
    (hn : (cross_output q branch dispo).next s s') :
    ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
  intro A D
  rw [grantRemaining, grantRemaining, hgrants]
  by_cases hb : branch = CrossBranch.endorsed
  · simp only [if_pos hb]
    unfold decrementGrantAt
    by_cases hkey : A = q.rcv ∧ D = q.assignment
    · simp only [if_pos hkey]
      cases hOld : s.crossing_grants A D with
      | none => simp
      | some old =>
          simp only
          exact Nat.sub_le old.remaining 1
    · simp only [if_neg hkey]
      exact Nat.le_refl _
  · simp only [if_neg hb]
    exact Nat.le_refl _

/-- **grant non-increase.** Every registered action except the root-only
`grant_crossing` faucet is pointwise non-increasing in remaining uses. -/
theorem grant_conservation :
    ∀ na ∈ ksystem.actions, na.1 ≠ "grant_crossing" →
      ∀ s s' : KSt, na.2.guard s → na.2.next s s' →
        ∀ A D, grantRemaining s' A D ≤ grantRemaining s A D := by
  intro na hmem hne s s' _hg hn
  simp only [ksystem, system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Kav.close1] at hn
    obtain ⟨tool, -, hn'⟩ := hn
    exact grant_noninc_register_tool tool s s' hn'
  · simp only [Kav.close1] at hn
    obtain ⟨tool, -, hn'⟩ := hn
    exact grant_noninc_unregister_tool tool s s' hn'
  · simp only [Kav.close2] at hn
    obtain ⟨grantor, grantee, -, hn'⟩ := hn
    exact grant_noninc_delegate grantor grantee s s' hn'
  · simp only [Kav.close3] at hn
    obtain ⟨prnt, child, cap, -, hn'⟩ := hn
    exact grant_noninc_grant_capability prnt child cap s s' hn'
  · exact absurd rfl hne
  · simp only [Kav.close2] at hn
    obtain ⟨prnt, target, -, hn'⟩ := hn
    exact grant_noninc_revoke prnt target s s' hn'
  · simp only [Kav.close2] at hn
    obtain ⟨child, prnt, -, hn'⟩ := hn
    exact grant_noninc_cascade_revoke child prnt s s' hn'
  · simp only [Kav.close5] at hn
    obtain ⟨a, src, pconf, pinteg, dispo, -, hn'⟩ := hn
    exact grant_noninc_ingest a src pconf pinteg dispo s s' hn'
  · simp only [Kav.close8] at hn
    obtain ⟨a, inv, chal, snap, egr, ah, authorized, v, -, hn'⟩ := hn
    exact grant_noninc_begin_invocation a inv chal snap egr ah authorized v s s' hn'
  · simp only [Kav.close4] at hn
    obtain ⟨inv, sc, att, admit, -, hn'⟩ := hn
    exact grant_noninc_authorize_inspected inv sc att admit s s' hn'
  · simp only [Kav.close7] at hn
    obtain ⟨inv, a, dispo, outcome, clvl, ilvl, att, -, hn'⟩ := hn
    exact grant_noninc_settle_invocation inv a dispo outcome clvl ilvl att s s' hn'
  · simp only [Kav.close3] at hn
    obtain ⟨q, branch, dispo, -, hn'⟩ := hn
    exact grant_noninc_cross_output q branch dispo s s' hn'

#print axioms grant_conservation

end Tzimtzum
