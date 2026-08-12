import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 invocation admission and inspection resolution

`begin_invocation` classifies capability, authorization, clearance, flow, and integrity checks as
`allow`, `inspection_required`, or `deny`. The guard ties the supplied verdict to those checks.
An enforce-mode inspection requirement creates a challenge without a pending record; monitor mode
records a bypassed pending invocation. `authorize_inspected` consumes a scope-matching attestation,
rechecks admission against the current state, and creates a permitted pending record only when the
attestation is positive and the live gate admits it.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- An inspection attestation: an *input*, not state. Issuer identity and truth are the
named external seam; the kernel checks scope and one-use consumption. -/
structure InspectionAttestation (InvocationId ChallengeId AttestationId PolicyDigest
    ContentHash : Type) where
  id            : AttestationId
  /-- Scope: the invocation whose challenge this resolves. -/
  inv           : InvocationId
  /-- Challenge identifier; the challenge map is keyed by `inv`. -/
  challenge     : ChallengeId
  /-- Scope: unchanged arguments. -/
  args_hash     : ContentHash
  /-- Scope: unchanged policy. -/
  policy_digest : PolicyDigest
  /-- The inspector's verdict. -/
  positive      : Prop

/-! ## The nine checks -/

/-- Capability check. Capabilities have only allow or deny outcomes. -/
def checkCapability
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  ∀ (C : CapKind), snap.required_caps C → s.agent_cap a C

/-- Clearance check for the current speculative taint and for the new output provenance.
The new output must clear both each existing pending record and its own snapshot ceiling. -/
structure checkClearance
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) :
    Prop where
  /-- Speculative-taint arm: the agent's worst-case taint clears the snapshot ceiling. -/
  speculative : ∀ (L : ConfLevel), speculative_taint s a L → clearance_admits L snap
  /-- Pending arm: the new output clears every existing pending record's ceiling. -/
  pending : ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.agent = a → clearance_admits snap.output_conf J.policy
  /-- Self arm: the new output clears its own snapshot ceiling. -/
  self : clearance_admits snap.output_conf snap

theorem checkClearance_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) :
    checkClearance s a snap ↔
      ((∀ (L : ConfLevel), speculative_taint s a L → clearance_admits L snap)
      ∧ (∀ (I : InvocationId)
          (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
          s.pending I = some J → J.agent = a → clearance_admits snap.output_conf J.policy)
      ∧ clearance_admits snap.output_conf snap) :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- CHECK 3a/3b/3c on their strict ALLOW arms. -/
structure checkFlowStrict
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) : Prop where
  speculative : ∀ (L : ConfLevel) (E : EgressKind),
    speculative_taint s a L → egr E → s.flow_allows L E
  pending_pairs : ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.pending I = some J → J.agent = a → J.egress E → s.flow_allows snap.output_conf E
  newcomer : ∀ (E : EgressKind), egr E → s.flow_allows snap.output_conf E

theorem checkFlowStrict_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) :
    checkFlowStrict s a snap egr ↔
      ((∀ (L : ConfLevel) (E : EgressKind),
        speculative_taint s a L → egr E → s.flow_allows L E)
      ∧ (∀ (I : InvocationId)
          (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
          (E : EgressKind),
          s.pending I = some J → J.agent = a → J.egress E → s.flow_allows snap.output_conf E)
      ∧ (∀ (E : EgressKind), egr E → s.flow_allows snap.output_conf E)) :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- Flow admissibility check. A pending record in the inspect band must already be vouched;
the newcomer receives its vouch only through inspection resolution. -/
structure checkFlowAdmissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) : Prop where
  /-- Speculative-taint arm: every worst-case taint level is in the allow or inspect band. -/
  speculative : ∀ (L : ConfLevel) (E : EgressKind),
    speculative_taint s a L → egr E → s.flow_allows L E ∨ s.flow_inspects L E
  /-- Pending arm: the new output is compatible with every existing pending record's egress. -/
  pending_pairs : ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.pending I = some J → J.agent = a → J.egress E →
      s.flow_allows snap.output_conf E
      ∨ (s.flow_inspects snap.output_conf E ∧ vouched J)
  /-- Newcomer arm: the new output is in the allow or inspect band on its own egress. -/
  newcomer : ∀ (E : EgressKind), egr E →
    s.flow_allows snap.output_conf E ∨ s.flow_inspects snap.output_conf E

theorem checkFlowAdmissible_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) :
    checkFlowAdmissible s a snap egr ↔
      ((∀ (L : ConfLevel) (E : EgressKind),
        speculative_taint s a L → egr E → s.flow_allows L E ∨ s.flow_inspects L E)
      ∧ (∀ (I : InvocationId)
          (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
          (E : EgressKind),
          s.pending I = some J → J.agent = a → J.egress E →
            s.flow_allows snap.output_conf E
            ∨ (s.flow_inspects snap.output_conf E ∧ vouched J))
      ∧ (∀ (E : EgressKind), egr E →
          s.flow_allows snap.output_conf E ∨ s.flow_inspects snap.output_conf E)) :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- CHECK 5a/5b/5c on their strict ALLOW arms. 5b is the "web_fetch settles while
delete_repo is in flight" hazard, read off frozen snapshots. -/
structure checkIntegStrict
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) :
    Prop where
  speculative : ∀ (L : IntegLevel), speculative_integ s a L → integ_allows L snap
  pending_pairs : ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.agent = a → integ_allows snap.output_integ J.policy
  newcomer : integ_allows snap.output_integ snap

theorem checkIntegStrict_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) :
    checkIntegStrict s a snap ↔
      ((∀ (L : IntegLevel), speculative_integ s a L → integ_allows L snap)
      ∧ (∀ (I : InvocationId)
          (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
          s.pending I = some J → J.agent = a → integ_allows snap.output_integ J.policy)
      ∧ integ_allows snap.output_integ snap) :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- Integrity admissibility check with the same pending-record vouch rule as flow admission. -/
structure checkIntegAdmissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) :
    Prop where
  /-- Speculative-integrity arm: every worst-case level is in the allow or inspect band. -/
  speculative : ∀ (L : IntegLevel),
    speculative_integ s a L → integ_allows L snap ∨ integ_inspects L snap
  /-- Pending arm: the new output integrity is compatible with every existing record's floor. -/
  pending_pairs : ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.agent = a →
      integ_allows snap.output_integ J.policy
      ∨ (integ_inspects snap.output_integ J.policy ∧ vouched J)
  /-- Newcomer arm: the new output integrity clears or inspect-bands its own floor. -/
  newcomer : integ_allows snap.output_integ snap ∨ integ_inspects snap.output_integ snap

theorem checkIntegAdmissible_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) :
    checkIntegAdmissible s a snap ↔
      ((∀ (L : IntegLevel),
        speculative_integ s a L → integ_allows L snap ∨ integ_inspects L snap)
      ∧ (∀ (I : InvocationId)
          (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
          s.pending I = some J → J.agent = a →
            integ_allows snap.output_integ J.policy
            ∨ (integ_inspects snap.output_integ J.policy ∧ vouched J))
      ∧ (integ_allows snap.output_integ snap ∨ integ_inspects snap.output_integ snap)) :=
  ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- Strict admission: capabilities, authorization, clearance, flow, and integrity all allow. -/
structure beginAllow
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) : Prop where
  capability : checkCapability s a snap
  authorized : authorized
  clearance : checkClearance s a snap
  flow : checkFlowStrict s a snap egr
  integ : checkIntegStrict s a snap

theorem beginAllow_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) :
    beginAllow s a snap egr authorized ↔
      (checkCapability s a snap ∧ authorized ∧ checkClearance s a snap
      ∧ checkFlowStrict s a snap egr ∧ checkIntegStrict s a snap) :=
  ⟨fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, h4, h5⟩,
   fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, h4, h5⟩⟩

/-- Verdict ≠ `deny`: every check on ALLOW-or-INSPECT. -/
structure beginAdmissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) : Prop where
  capability : checkCapability s a snap
  authorized : authorized
  clearance : checkClearance s a snap
  flow : checkFlowAdmissible s a snap egr
  integ : checkIntegAdmissible s a snap

theorem beginAdmissible_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) :
    beginAdmissible s a snap egr authorized ↔
      (checkCapability s a snap ∧ authorized ∧ checkClearance s a snap
      ∧ checkFlowAdmissible s a snap egr ∧ checkIntegAdmissible s a snap) :=
  ⟨fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, h4, h5⟩,
   fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, h4, h5⟩⟩

/-- The trichotomy is a total complementary partition: strict ALLOW implies admissible. -/
theorem beginAllow_admissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) :
    beginAllow s a snap egr authorized → beginAdmissible s a snap egr authorized := by
  rintro ⟨hcap, hauth, hclr, ⟨f1, f2, f3⟩, ⟨i1, i2, i3⟩⟩
  exact ⟨hcap, hauth, hclr,
    ⟨fun L E h1 h2 ↦ Or.inl (f1 L E h1 h2),
     fun I J E h1 h2 h3 ↦ Or.inl (f2 I J E h1 h2 h3),
     fun E h ↦ Or.inl (f3 E h)⟩,
    ⟨fun L h ↦ Or.inl (i1 L h),
     fun I J h1 h2 ↦ Or.inl (i2 I J h1 h2),
     Or.inl i3⟩⟩

/-! ## `begin_invocation`

The parameters include the requested verdict. Guard clauses require it to match the computed
checks, so update selection cannot choose a different result. -/

open Classical in
kav_action begin_invocation (a : AgentId) (inv : InvocationId) (chal : ChallengeId)
    (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (ah : ContentHash) (authorized : Prop) (v : Verdict) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require active : s.agent_active a
  require not_root : a ≠ s.root_agent
  require tool_registered : s.tool_registered snap.tool
 -- Snapshot coherence: an incoherent band is a boundary rejection, never a kernel branch.
  require band_coherent : le_integ snap.integ_inspect snap.integ_floor
 -- The invocation slot, consumed identifier history, and challenge slot must all be fresh.
  require slot_free : s.pending inv = none
  require id_fresh : ¬ s.consumed_ids inv
  require challenge_fresh : s.challenges inv = none
 -- Narrowing.
  require egress_narrowing : ∀ (E : EgressKind), egr E → snap.declared_egress E
 -- Coverage: an egress-bearing action cannot be admitted on an empty attestation.
  require egress_coverage :
    (∃ (E : EgressKind), snap.declared_egress E) → (∃ (E : EgressKind), egr E)
 -- Each verdict must agree with the admission predicates; denial can transition only in monitor mode.
  require verdict_allow : v = Verdict.allow → beginAllow s a snap egr authorized
  require verdict_inspect : v = Verdict.inspection_required →
    beginAdmissible s a snap egr authorized ∧ ¬ beginAllow s a snap egr authorized
  require verdict_deny : v = Verdict.deny → ¬ beginAdmissible s a snap egr authorized
  require deny_monitor : v = Verdict.deny → s.mode = Mode.monitor
 -- Match on verdict and mode constructors so each update branch has a direct case split.
  pending := fun I =>
    if I = inv then
      (match v, s.mode with
        | Verdict.allow, _ =>
          some { agent := a, policy := snap, egress := egr, admission := Admission.plain,
                 disposition := Disposition.permitted, authorized := authorized,
                 quarantined := False }
       -- An unresolved enforce-mode challenge creates no pending record.
        | Verdict.inspection_required, Mode.enforce => none
       -- Monitor-mode non-allow outcomes remain pending as bypassed records so they constrain
       -- later admissions.
        | Verdict.inspection_required, Mode.monitor =>
          some { agent := a, policy := snap, egress := egr, admission := Admission.bypassed,
                 disposition := Disposition.monitor_bypassed, authorized := authorized,
                 quarantined := False }
        | Verdict.deny, _ =>
          some { agent := a, policy := snap, egress := egr, admission := Admission.bypassed,
                 disposition := Disposition.monitor_bypassed, authorized := authorized,
                 quarantined := False })
    else s.pending I
  challenges := fun I =>
    if I = inv then
      (match v, s.mode with
        | Verdict.inspection_required, Mode.enforce =>
          some { challenge := chal, agent := a, policy := snap, egress := egr,
                 args_hash := ah, authorized := authorized }
        | _, _ => s.challenges I)
    else s.challenges I
 -- Consumed on every arm that is a transition: freshness and `challenge_unique` both
 -- lean on it.
  consumed_ids := fun I => s.consumed_ids I ∨ I = inv

/-! ## `authorize_inspected` -/

/-- Live challenge-resolution admission: structural conditions and the current admissible gate.
The positive and negative branches use complementary conditions. -/
structure authorizeAdmits
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash) : Prop where
  active : s.agent_active sc.agent
  not_root : sc.agent ≠ s.root_agent
  tool_registered : s.tool_registered sc.policy.tool
  band_coherent : le_integ sc.policy.integ_inspect sc.policy.integ_floor
  slot_free : s.pending inv = none
  egress_narrowing : ∀ (E : EgressKind), sc.egress E → sc.policy.declared_egress E
  egress_coverage :
    (∃ (E : EgressKind), sc.policy.declared_egress E) → (∃ (E : EgressKind), sc.egress E)
  /-- The live begin-time admission gate carried by `authorizeAdmits`. -/
  toBeginAdmissible : beginAdmissible s sc.agent sc.policy sc.egress sc.authorized

theorem authorizeAdmits_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash) :
    authorizeAdmits s inv sc ↔
      (s.agent_active sc.agent
      ∧ sc.agent ≠ s.root_agent
      ∧ s.tool_registered sc.policy.tool
      ∧ le_integ sc.policy.integ_inspect sc.policy.integ_floor
      ∧ s.pending inv = none
      ∧ (∀ (E : EgressKind), sc.egress E → sc.policy.declared_egress E)
      ∧ ((∃ (E : EgressKind), sc.policy.declared_egress E) → (∃ (E : EgressKind), sc.egress E))
      ∧ beginAdmissible s sc.agent sc.policy sc.egress sc.authorized) :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ ↦ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ ↦ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-! `sc` is checked against the stored challenge before updates read it. `admit` is constrained
by the attestation verdict and the live admission predicate. -/

open Classical in
kav_action authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest
      ContentHash)
    (admit : Bool) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
 -- The challenge map contains exactly this scope at the invocation key.
  require challenge_bound : s.challenges inv = some sc
 -- Exact scope equality: invocation, challenge attribution, arguments, policy.
  require scope_invocation : att.inv = inv
  require scope_challenge : att.challenge = sc.challenge
  require scope_args : att.args_hash = sc.args_hash
  require scope_policy : att.policy_digest = sc.policy.policy_digest
 -- One-use.
  require attestation_fresh : ¬ s.consumed_attestations att.id
 -- The invocation identifier was consumed when the challenge was created.
  require id_consumed : s.consumed_ids inv
 -- Admission needs both a positive attestation and current live admission.
  require admit_pos : admit = true → att.positive ∧ authorizeAdmits s inv sc
 -- Denial is the complementary branch.
  require admit_neg : admit = false → ¬ att.positive ∨ ¬ authorizeAdmits s inv sc
  pending := fun I =>
    if I = inv ∧ admit = true then
      some { agent := sc.agent, policy := sc.policy, egress := sc.egress,
             admission := Admission.inspected att.id,
             disposition := Disposition.permitted, authorized := sc.authorized,
             quarantined := False }
    else s.pending I
 -- Both branches close the challenge and leave labels unchanged.
  challenges := fun I => if I = inv then none else s.challenges I
  consumed_attestations := fun X => s.consumed_attestations X ∨ X = att.id

/-! ## Non-vacuity -/

open Classical in
/-- Some canonical verdict always satisfies `begin_invocation`'s verdict clauses, provided
the state admits any transition at all (admissible, or monitor mode). -/
theorem begin_verdict_total
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop)
    (hmode : beginAdmissible s a snap egr authorized ∨ s.mode = Mode.monitor) :
    ∃ (v : Verdict),
      (v = Verdict.allow → beginAllow s a snap egr authorized)
      ∧ (v = Verdict.inspection_required →
          beginAdmissible s a snap egr authorized ∧ ¬ beginAllow s a snap egr authorized)
      ∧ (v = Verdict.deny → ¬ beginAdmissible s a snap egr authorized)
      ∧ (v = Verdict.deny → s.mode = Mode.monitor) := by
  by_cases hallow : beginAllow s a snap egr authorized
  · exact ⟨Verdict.allow, fun _ => hallow, by simp, by simp, by simp⟩
  · by_cases hadm : beginAdmissible s a snap egr authorized
    · exact ⟨Verdict.inspection_required, by simp, fun _ => ⟨hadm, hallow⟩, by simp, by simp⟩
    · exact ⟨Verdict.deny, by simp, by simp, fun _ => hadm, fun _ => hmode.resolve_left hadm⟩

open Classical in
/-- Some branch decision always satisfies `authorize_inspected`'s canonicity clauses. -/
theorem authorize_admit_total
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest
      ContentHash)
    (inv : InvocationId) :
    ∃ (admit : Bool),
      (admit = true → att.positive ∧ authorizeAdmits s inv sc)
      ∧ (admit = false → ¬ att.positive ∨ ¬ authorizeAdmits s inv sc) := by
  by_cases h : att.positive ∧ authorizeAdmits s inv sc
  · exact ⟨true, fun _ => h, by simp⟩
  · refine ⟨false, by simp, fun _ => ?_⟩
    by_cases hpos : att.positive
    · exact Or.inr (fun hg => h ⟨hpos, hg⟩)
    · exact Or.inl hpos

end Tzimtzum
