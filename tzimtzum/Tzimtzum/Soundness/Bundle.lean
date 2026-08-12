import Tzimtzum.Invariants
import Kav.Core

/-!
# TzimtzumV4 invariant bundle

`allInv` is the conjunction of structural, pending, pairwise, evidence, and crossing invariant
sub-bundles. The named lists expose the same predicates to action-preservation checks.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- Structural invariants. -/
def invS
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  root_always_active s ∧ parent_implies_active s ∧ single_parent s ∧ no_self_parent s
  ∧ root_no_parent s ∧ capability_subsumption s ∧ root_all_caps s ∧ revocation_clean s
  ∧ pending_active s

/-- Pending and gate invariants. -/
def invP
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  pending_unique s ∧ pending_registered s ∧ root_no_pending s ∧ pending_ids_consumed s
  ∧ pending_egress_attested s ∧ pending_snapshot_coherent s ∧ default_deny s
  ∧ flow_confinement s ∧ flow_confinement_weak s
  ∧ integrity_confinement s ∧ integrity_confinement_weak s ∧ clearance_confinement s

/-- Pairwise invariants. -/
def invPP
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  pending_flow_compat s ∧ pending_integ_compat s

/-- Evidence invariants. -/
def invE
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  challenge_scoped s ∧ challenges_enforce_only s ∧ challenge_unique s
  ∧ inspected_evidence_consumed s ∧ bypass_mode_sound s ∧ quarantine_pending s

/-- Crossing invariants. -/
def invC
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  grant_bounded s ∧ grant_active s ∧ grant_pinned s

/-- The full TzimtzumV4 bundle. -/
def allInv
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  invS s ∧ invP s ∧ invPP s ∧ invE s ∧ invC s

/-- The conjunction lemma composing the sub-bundles; definitional, so per-action checks
reassemble without glue. -/
theorem allInv_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) :
    allInv s ↔ (invS s ∧ invP s ∧ invPP s ∧ invE s ∧ invC s) :=
  Iff.rfl

/-! ## Named accessors

`hinv.flow_confinement`-style dot access replaces positional `obtain` patterns in manual
preservation proofs. The projection spelling of every invariant lives here, once; proofs
never count conjuncts. -/

section Accessors

variable {s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash}

theorem allInv.toInvS (h : allInv s) : invS s := h.1
theorem allInv.toInvP (h : allInv s) : invP s := h.2.1
theorem allInv.toInvPP (h : allInv s) : invPP s := h.2.2.1
theorem allInv.toInvE (h : allInv s) : invE s := h.2.2.2.1
theorem allInv.toInvC (h : allInv s) : invC s := h.2.2.2.2

-- Structural (S).
theorem allInv.root_always_active (h : allInv s) : root_always_active s := h.toInvS.1
theorem allInv.parent_implies_active (h : allInv s) : parent_implies_active s := h.toInvS.2.1
theorem allInv.single_parent (h : allInv s) : single_parent s := h.toInvS.2.2.1
theorem allInv.no_self_parent (h : allInv s) : no_self_parent s := h.toInvS.2.2.2.1
theorem allInv.root_no_parent (h : allInv s) : root_no_parent s := h.toInvS.2.2.2.2.1
theorem allInv.capability_subsumption (h : allInv s) : capability_subsumption s :=
  h.toInvS.2.2.2.2.2.1
theorem allInv.root_all_caps (h : allInv s) : root_all_caps s := h.toInvS.2.2.2.2.2.2.1
theorem allInv.revocation_clean (h : allInv s) : revocation_clean s := h.toInvS.2.2.2.2.2.2.2.1
theorem allInv.pending_active (h : allInv s) : pending_active s := h.toInvS.2.2.2.2.2.2.2.2

-- Pending and gates (P).
theorem allInv.pending_unique (h : allInv s) : pending_unique s := h.toInvP.1
theorem allInv.pending_registered (h : allInv s) : pending_registered s := h.toInvP.2.1
theorem allInv.root_no_pending (h : allInv s) : root_no_pending s := h.toInvP.2.2.1
theorem allInv.pending_ids_consumed (h : allInv s) : pending_ids_consumed s := h.toInvP.2.2.2.1
theorem allInv.pending_egress_attested (h : allInv s) : pending_egress_attested s :=
  h.toInvP.2.2.2.2.1
theorem allInv.pending_snapshot_coherent (h : allInv s) : pending_snapshot_coherent s :=
  h.toInvP.2.2.2.2.2.1
theorem allInv.default_deny (h : allInv s) : default_deny s := h.toInvP.2.2.2.2.2.2.1
theorem allInv.flow_confinement (h : allInv s) : flow_confinement s := h.toInvP.2.2.2.2.2.2.2.1
theorem allInv.flow_confinement_weak (h : allInv s) : flow_confinement_weak s :=
  h.toInvP.2.2.2.2.2.2.2.2.1
theorem allInv.integrity_confinement (h : allInv s) : integrity_confinement s :=
  h.toInvP.2.2.2.2.2.2.2.2.2.1
theorem allInv.integrity_confinement_weak (h : allInv s) : integrity_confinement_weak s :=
  h.toInvP.2.2.2.2.2.2.2.2.2.2.1
theorem allInv.clearance_confinement (h : allInv s) : clearance_confinement s :=
  h.toInvP.2.2.2.2.2.2.2.2.2.2.2

-- Pairwise (P′).
theorem allInv.pending_flow_compat (h : allInv s) : pending_flow_compat s := h.toInvPP.1
theorem allInv.pending_integ_compat (h : allInv s) : pending_integ_compat s := h.toInvPP.2

-- Evidence (E).
theorem allInv.challenge_scoped (h : allInv s) : challenge_scoped s := h.toInvE.1
theorem allInv.challenges_enforce_only (h : allInv s) : challenges_enforce_only s :=
  h.toInvE.2.1
theorem allInv.challenge_unique (h : allInv s) : challenge_unique s := h.toInvE.2.2.1
theorem allInv.inspected_evidence_consumed (h : allInv s) : inspected_evidence_consumed s :=
  h.toInvE.2.2.2.1
theorem allInv.bypass_mode_sound (h : allInv s) : bypass_mode_sound s := h.toInvE.2.2.2.2.1
theorem allInv.quarantine_pending (h : allInv s) : quarantine_pending s := h.toInvE.2.2.2.2.2

-- Crossing (C).
theorem allInv.grant_bounded (h : allInv s) : grant_bounded s := h.toInvC.1
theorem allInv.grant_active (h : allInv s) : grant_active s := h.toInvC.2.1
theorem allInv.grant_pinned (h : allInv s) : grant_pinned s := h.toInvC.2.2

end Accessors

/-! ## Named lists, one per sub-bundle

The lists expose small invariant groups to action-preservation checks. Each proof goal receives
its own heartbeat budget through `all_goals_fresh`. -/

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
