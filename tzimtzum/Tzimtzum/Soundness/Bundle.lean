import Tzimtzum.Invariants
import Kav.Core

/-!
# TzimtzumV4 — the destructured invariant bundle

The five named sub-bundles of [[2026-07-24-tzimtzum-v4/architecture|architecture]] §8,
joined by a *definitional* conjunction lemma (`allInv_iff` is `Iff.rfl`), exactly as the
Task 0 spike recorded: per-action checks discharge sub-bundles (and, for the expensive
ones, single conjuncts) independently and reassemble for free. The monolithic V3 26-conjunct
`allInv` was already at the cascade's saturation edge; destructuring is designed in from
day one.

Count: S 9 + P 12 + P′ 2 + E 6 + C 3 = **32 conjuncts**. The §8 candidate list said ~31;
the delta is `challenges_enforce_only`, added by E23 (challenges are enforce-only, which is
what makes `authorize_inspected`'s monitor arm dead code rather than missing code). Every
other deviation from the candidate list is a *statement* amendment recorded in §14
(E10 clearance reads the contained speculative set, E11 `bypass_mode_sound` over
`¬ contained`, E14 `challenge_unique` restated as map functionality under invocation
keying, E15 `grant_bounded` against the per-grant provisioned bound, E22 pairwise vouch on
the constrained party), not an addition or deletion.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- S — structural (9). -/
def invS
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  root_always_active s ∧ parent_implies_active s ∧ single_parent s ∧ no_self_parent s
  ∧ root_no_parent s ∧ capability_subsumption s ∧ root_all_caps s ∧ revocation_clean s
  ∧ pending_active s

/-- P — pending / gates (12). -/
def invP
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  pending_unique s ∧ pending_registered s ∧ root_no_pending s ∧ pending_ids_consumed s
  ∧ pending_egress_attested s ∧ pending_snapshot_coherent s ∧ default_deny s
  ∧ flow_confinement s ∧ flow_confinement_weak s
  ∧ integrity_confinement s ∧ integrity_confinement_weak s ∧ clearance_confinement s

/-- P′ — pairwise (2). -/
def invPP
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  pending_flow_compat s ∧ pending_integ_compat s

/-- E — evidence (6). -/
def invE
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  challenge_scoped s ∧ challenges_enforce_only s ∧ challenge_unique s
  ∧ inspected_evidence_consumed s ∧ bypass_mode_sound s ∧ quarantine_pending s

/-- C — crossing (3). -/
def invC
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  grant_bounded s ∧ grant_active s ∧ grant_pinned s

/-- The full TzimtzumV4 bundle. -/
def allInv
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  invS s ∧ invP s ∧ invPP s ∧ invE s ∧ invC s

/-- The conjunction lemma composing the sub-bundles — definitional, so per-action checks
reassemble without glue. -/
theorem allInv_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) :
    allInv s ↔ (invS s ∧ invP s ∧ invPP s ∧ invE s ∧ invC s) :=
  Iff.rfl

/-! ## Named lists, one per sub-bundle

For `#kav_check_action` triage during Tasks 7–10 (small groups only — the command shares
one heartbeat budget across a whole invocation, so grouped VCs starve; the per-conjunct
`all_goals_fresh` theorems are what carries the record). -/

def invariantsS :
    List (Kav.Invariant
      (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
        CrossingId AssignmentDigest PolicyDigest ContentHash)) :=
  [ ("root_always_active", root_always_active)
  , ("parent_implies_active", parent_implies_active)
  , ("single_parent", single_parent)
  , ("no_self_parent", no_self_parent)
  , ("root_no_parent", root_no_parent)
  , ("capability_subsumption", capability_subsumption)
  , ("root_all_caps", root_all_caps)
  , ("revocation_clean", revocation_clean)
  , ("pending_active", pending_active) ]

def invariantsP :
    List (Kav.Invariant
      (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
        CrossingId AssignmentDigest PolicyDigest ContentHash)) :=
  [ ("pending_unique", pending_unique)
  , ("pending_registered", pending_registered)
  , ("root_no_pending", root_no_pending)
  , ("pending_ids_consumed", pending_ids_consumed)
  , ("pending_egress_attested", pending_egress_attested)
  , ("pending_snapshot_coherent", pending_snapshot_coherent)
  , ("default_deny", default_deny)
  , ("flow_confinement", flow_confinement)
  , ("flow_confinement_weak", flow_confinement_weak)
  , ("integrity_confinement", integrity_confinement)
  , ("integrity_confinement_weak", integrity_confinement_weak)
  , ("clearance_confinement", clearance_confinement) ]

def invariantsPP :
    List (Kav.Invariant
      (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
        CrossingId AssignmentDigest PolicyDigest ContentHash)) :=
  [ ("pending_flow_compat", pending_flow_compat)
  , ("pending_integ_compat", pending_integ_compat) ]

def invariantsE :
    List (Kav.Invariant
      (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
        CrossingId AssignmentDigest PolicyDigest ContentHash)) :=
  [ ("challenge_scoped", challenge_scoped)
  , ("challenges_enforce_only", challenges_enforce_only)
  , ("challenge_unique", challenge_unique)
  , ("inspected_evidence_consumed", inspected_evidence_consumed)
  , ("bypass_mode_sound", bypass_mode_sound)
  , ("quarantine_pending", quarantine_pending) ]

def invariantsC :
    List (Kav.Invariant
      (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
        CrossingId AssignmentDigest PolicyDigest ContentHash)) :=
  [ ("grant_bounded", grant_bounded)
  , ("grant_active", grant_active)
  , ("grant_pinned", grant_pinned) ]

def allInvariants :
    List (Kav.Invariant
      (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
        CrossingId AssignmentDigest PolicyDigest ContentHash)) :=
  invariantsS ++ invariantsP ++ invariantsPP ++ invariantsE ++ invariantsC

end Tzimtzum
