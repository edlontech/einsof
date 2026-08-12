import Tzimtzum.Invariants
import Kav.Core

/-!
# TzimtzumV4 invariant bundle

`allInv` bundles the structural, pending, pairwise, evidence, and crossing invariant
sub-bundles as `Prop`-valued structures with one named field per invariant, so proofs access
every conjunct by name (`hinv.flow_confinement`). The `_iff` lemmas expose the underlying
conjunctions to the discharge cascades; the named lists expose the same predicates to
action-preservation checks.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- Structural invariants. Each named field is one of the 9 structural conjuncts. -/
structure invS
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop where
  root_always_active : root_always_active s
  parent_implies_active : parent_implies_active s
  single_parent : single_parent s
  no_self_parent : no_self_parent s
  root_no_parent : root_no_parent s
  capability_subsumption : capability_subsumption s
  root_all_caps : root_all_caps s
  revocation_clean : revocation_clean s
  pending_active : pending_active s

/-- Pending and gate invariants. Each named field is one of the 12 pending/gate conjuncts. -/
structure invP
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop where
  pending_unique : pending_unique s
  pending_registered : pending_registered s
  root_no_pending : root_no_pending s
  pending_ids_consumed : pending_ids_consumed s
  pending_egress_attested : pending_egress_attested s
  pending_snapshot_coherent : pending_snapshot_coherent s
  default_deny : default_deny s
  flow_confinement : flow_confinement s
  flow_confinement_weak : flow_confinement_weak s
  integrity_confinement : integrity_confinement s
  integrity_confinement_weak : integrity_confinement_weak s
  clearance_confinement : clearance_confinement s

/-- Pairwise invariants. -/
structure invPP
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop where
  pending_flow_compat : pending_flow_compat s
  pending_integ_compat : pending_integ_compat s

/-- Evidence invariants. -/
structure invE
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop where
  challenge_scoped : challenge_scoped s
  challenges_enforce_only : challenges_enforce_only s
  challenge_unique : challenge_unique s
  inspected_evidence_consumed : inspected_evidence_consumed s
  bypass_mode_sound : bypass_mode_sound s
  quarantine_pending : quarantine_pending s

/-- Crossing invariants. -/
structure invC
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop where
  grant_bounded : grant_bounded s
  grant_active : grant_active s
  grant_pinned : grant_pinned s

/-- The full TzimtzumV4 bundle. -/
structure allInv
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop where
  toInvS : invS s
  toInvP : invP s
  toInvPP : invPP s
  toInvE : invE s
  toInvC : invC s

/-! ## Conjunction views

One iff lemma per bundle. The discharge cascades (`Soundness/Common.lean`) rewrite with
these to reduce structure goals and hypotheses to the underlying `∧`-chains for
`repeat' apply And.intro` and the automated closers. Deliberately **not** `@[simp]`:
they are listed explicitly exactly where the reduction is wanted. -/

section ConjunctionViews

variable (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash)

theorem invS_iff :
    invS s ↔ (root_always_active s ∧ parent_implies_active s ∧ single_parent s
      ∧ no_self_parent s ∧ root_no_parent s ∧ capability_subsumption s ∧ root_all_caps s
      ∧ revocation_clean s ∧ pending_active s) :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ↦ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ↦ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

theorem invP_iff :
    invP s ↔ (pending_unique s ∧ pending_registered s ∧ root_no_pending s
      ∧ pending_ids_consumed s ∧ pending_egress_attested s ∧ pending_snapshot_coherent s
      ∧ default_deny s ∧ flow_confinement s ∧ flow_confinement_weak s
      ∧ integrity_confinement s ∧ integrity_confinement_weak s ∧ clearance_confinement s) :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ ↦
     ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ ↦
     ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

theorem invPP_iff : invPP s ↔ (pending_flow_compat s ∧ pending_integ_compat s) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

theorem invE_iff :
    invE s ↔ (challenge_scoped s ∧ challenges_enforce_only s ∧ challenge_unique s
      ∧ inspected_evidence_consumed s ∧ bypass_mode_sound s ∧ quarantine_pending s) :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ⟨h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ⟨h1, h2, h3, h4, h5, h6⟩⟩

theorem invC_iff : invC s ↔ (grant_bounded s ∧ grant_active s ∧ grant_pinned s) :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- The sub-bundle composition view consumed by per-action checks and the refinement. -/
theorem allInv_iff : allInv s ↔ (invS s ∧ invP s ∧ invPP s ∧ invE s ∧ invC s) :=
  ⟨fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, h4, h5⟩,
   fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, h4, h5⟩⟩

end ConjunctionViews

/-! ## Named accessors

`hinv.flow_confinement`-style dot access on the full bundle composes the two structure
projections; proofs never count conjuncts. Sub-bundle fields (`toInvS` … `toInvC` and every
leaf) are native projections. -/

section Accessors

variable {s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash}

-- Structural (S).
theorem allInv.root_always_active (h : allInv s) : root_always_active s :=
  h.toInvS.root_always_active
theorem allInv.parent_implies_active (h : allInv s) : parent_implies_active s :=
  h.toInvS.parent_implies_active
theorem allInv.single_parent (h : allInv s) : single_parent s := h.toInvS.single_parent
theorem allInv.no_self_parent (h : allInv s) : no_self_parent s := h.toInvS.no_self_parent
theorem allInv.root_no_parent (h : allInv s) : root_no_parent s := h.toInvS.root_no_parent
theorem allInv.capability_subsumption (h : allInv s) : capability_subsumption s :=
  h.toInvS.capability_subsumption
theorem allInv.root_all_caps (h : allInv s) : root_all_caps s := h.toInvS.root_all_caps
theorem allInv.revocation_clean (h : allInv s) : revocation_clean s := h.toInvS.revocation_clean
theorem allInv.pending_active (h : allInv s) : pending_active s := h.toInvS.pending_active

-- Pending and gates (P).
theorem allInv.pending_unique (h : allInv s) : pending_unique s := h.toInvP.pending_unique
theorem allInv.pending_registered (h : allInv s) : pending_registered s :=
  h.toInvP.pending_registered
theorem allInv.root_no_pending (h : allInv s) : root_no_pending s := h.toInvP.root_no_pending
theorem allInv.pending_ids_consumed (h : allInv s) : pending_ids_consumed s :=
  h.toInvP.pending_ids_consumed
theorem allInv.pending_egress_attested (h : allInv s) : pending_egress_attested s :=
  h.toInvP.pending_egress_attested
theorem allInv.pending_snapshot_coherent (h : allInv s) : pending_snapshot_coherent s :=
  h.toInvP.pending_snapshot_coherent
theorem allInv.default_deny (h : allInv s) : default_deny s := h.toInvP.default_deny
theorem allInv.flow_confinement (h : allInv s) : flow_confinement s :=
  h.toInvP.flow_confinement
theorem allInv.flow_confinement_weak (h : allInv s) : flow_confinement_weak s :=
  h.toInvP.flow_confinement_weak
theorem allInv.integrity_confinement (h : allInv s) : integrity_confinement s :=
  h.toInvP.integrity_confinement
theorem allInv.integrity_confinement_weak (h : allInv s) : integrity_confinement_weak s :=
  h.toInvP.integrity_confinement_weak
theorem allInv.clearance_confinement (h : allInv s) : clearance_confinement s :=
  h.toInvP.clearance_confinement

-- Pairwise (P′).
theorem allInv.pending_flow_compat (h : allInv s) : pending_flow_compat s :=
  h.toInvPP.pending_flow_compat
theorem allInv.pending_integ_compat (h : allInv s) : pending_integ_compat s :=
  h.toInvPP.pending_integ_compat

-- Evidence (E).
theorem allInv.challenge_scoped (h : allInv s) : challenge_scoped s :=
  h.toInvE.challenge_scoped
theorem allInv.challenges_enforce_only (h : allInv s) : challenges_enforce_only s :=
  h.toInvE.challenges_enforce_only
theorem allInv.challenge_unique (h : allInv s) : challenge_unique s := h.toInvE.challenge_unique
theorem allInv.inspected_evidence_consumed (h : allInv s) : inspected_evidence_consumed s :=
  h.toInvE.inspected_evidence_consumed
theorem allInv.bypass_mode_sound (h : allInv s) : bypass_mode_sound s :=
  h.toInvE.bypass_mode_sound
theorem allInv.quarantine_pending (h : allInv s) : quarantine_pending s :=
  h.toInvE.quarantine_pending

-- Crossing (C).
theorem allInv.grant_bounded (h : allInv s) : grant_bounded s := h.toInvC.grant_bounded
theorem allInv.grant_active (h : allInv s) : grant_active s := h.toInvC.grant_active
theorem allInv.grant_pinned (h : allInv s) : grant_pinned s := h.toInvC.grant_pinned

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
