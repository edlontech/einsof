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
def checkClearance
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  (∀ (L : ConfLevel), speculative_taint s a L → clearance_admits L snap)
  ∧ (∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
      s.pending I = some J → J.agent = a → clearance_admits snap.output_conf J.policy)
  ∧ clearance_admits snap.output_conf snap

/-- CHECK 3a/3b/3c on their strict ALLOW arms. -/
def checkFlowStrict
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) : Prop :=
  (∀ (L : ConfLevel) (E : EgressKind),
    speculative_taint s a L → egr E → s.flow_allows L E)
  ∧ (∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
      (E : EgressKind),
      s.pending I = some J → J.agent = a → J.egress E → s.flow_allows snap.output_conf E)
  ∧ (∀ (E : EgressKind), egr E → s.flow_allows snap.output_conf E)

/-- Flow admissibility check. A pending record in the inspect band must already be vouched;
the newcomer receives its vouch only through inspection resolution. -/
def checkFlowAdmissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) : Prop :=
  (∀ (L : ConfLevel) (E : EgressKind),
    speculative_taint s a L → egr E → s.flow_allows L E ∨ s.flow_inspects L E)
  ∧ (∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
      (E : EgressKind),
      s.pending I = some J → J.agent = a → J.egress E →
        s.flow_allows snap.output_conf E
        ∨ (s.flow_inspects snap.output_conf E ∧ vouched J))
  ∧ (∀ (E : EgressKind), egr E →
      s.flow_allows snap.output_conf E ∨ s.flow_inspects snap.output_conf E)

/-- CHECK 5a/5b/5c on their strict ALLOW arms. 5b is the "web_fetch settles while
delete_repo is in flight" hazard, read off frozen snapshots. -/
def checkIntegStrict
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  (∀ (L : IntegLevel), speculative_integ s a L → integ_allows L snap)
  ∧ (∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
      s.pending I = some J → J.agent = a → integ_allows snap.output_integ J.policy)
  ∧ integ_allows snap.output_integ snap

/-- Integrity admissibility check with the same pending-record vouch rule as flow admission. -/
def checkIntegAdmissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  (∀ (L : IntegLevel), speculative_integ s a L → integ_allows L snap ∨ integ_inspects L snap)
  ∧ (∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
      s.pending I = some J → J.agent = a →
        integ_allows snap.output_integ J.policy
        ∨ (integ_inspects snap.output_integ J.policy ∧ vouched J))
  ∧ (integ_allows snap.output_integ snap ∨ integ_inspects snap.output_integ snap)

/-- Strict admission: capabilities, authorization, clearance, flow, and integrity all allow. -/
def beginAllow
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) : Prop :=
  checkCapability s a snap ∧ authorized ∧ checkClearance s a snap
  ∧ checkFlowStrict s a snap egr ∧ checkIntegStrict s a snap

/-- Verdict ≠ `deny`: every check on ALLOW-or-INSPECT. -/
def beginAdmissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) : Prop :=
  checkCapability s a snap ∧ authorized ∧ checkClearance s a snap
  ∧ checkFlowAdmissible s a snap egr ∧ checkIntegAdmissible s a snap

/-! ### Named gate accessors

Dot access (`(admitted).flow.speculative`, …) replaces `h.2.2.2.1`-style anonymous
projections in preservation proofs. The projection spelling of each gate arm lives here. -/

section GateAccessors

variable {s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash}
  {a : AgentId} {snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest}
  {egr : EgressKind → Prop} {authorized : Prop}

/-- Speculative-taint arm: the agent's worst-case taint clears the snapshot ceiling. -/
theorem checkClearance.speculative (h : checkClearance s a snap) :
    ∀ (L : ConfLevel), speculative_taint s a L → clearance_admits L snap := h.1

/-- Pending arm: the new output clears every existing pending record's ceiling. -/
theorem checkClearance.pending (h : checkClearance s a snap) :
    ∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
      s.pending I = some J → J.agent = a → clearance_admits snap.output_conf J.policy := h.2.1

/-- Self arm: the new output clears its own snapshot ceiling. -/
theorem checkClearance.self (h : checkClearance s a snap) :
    clearance_admits snap.output_conf snap := h.2.2

/-- Speculative-taint arm: every worst-case taint level is in the allow or inspect band. -/
theorem checkFlowAdmissible.speculative (h : checkFlowAdmissible s a snap egr) :
    ∀ (L : ConfLevel) (E : EgressKind), speculative_taint s a L → egr E →
      s.flow_allows L E ∨ s.flow_inspects L E := h.1

/-- Pending arm: the new output is compatible with every existing pending record's egress. -/
theorem checkFlowAdmissible.pending_pairs (h : checkFlowAdmissible s a snap egr) :
    ∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
      (E : EgressKind),
      s.pending I = some J → J.agent = a → J.egress E →
        s.flow_allows snap.output_conf E
        ∨ (s.flow_inspects snap.output_conf E ∧ vouched J) := h.2.1

/-- Newcomer arm: the new output is in the allow or inspect band on its own egress. -/
theorem checkFlowAdmissible.newcomer (h : checkFlowAdmissible s a snap egr) :
    ∀ (E : EgressKind), egr E →
      s.flow_allows snap.output_conf E ∨ s.flow_inspects snap.output_conf E := h.2.2

/-- Speculative-integrity arm: every worst-case level is in the allow or inspect band. -/
theorem checkIntegAdmissible.speculative (h : checkIntegAdmissible s a snap) :
    ∀ (L : IntegLevel), speculative_integ s a L →
      integ_allows L snap ∨ integ_inspects L snap := h.1

/-- Pending arm: the new output integrity is compatible with every existing record's floor. -/
theorem checkIntegAdmissible.pending_pairs (h : checkIntegAdmissible s a snap) :
    ∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
      s.pending I = some J → J.agent = a →
        integ_allows snap.output_integ J.policy
        ∨ (integ_inspects snap.output_integ J.policy ∧ vouched J) := h.2.1

/-- Newcomer arm: the new output integrity clears or inspect-bands its own floor. -/
theorem checkIntegAdmissible.newcomer (h : checkIntegAdmissible s a snap) :
    integ_allows snap.output_integ snap ∨ integ_inspects snap.output_integ snap := h.2.2

theorem beginAdmissible.capability (h : beginAdmissible s a snap egr authorized) :
    checkCapability s a snap := h.1

theorem beginAdmissible.clearance (h : beginAdmissible s a snap egr authorized) :
    checkClearance s a snap := h.2.2.1

theorem beginAdmissible.flow (h : beginAdmissible s a snap egr authorized) :
    checkFlowAdmissible s a snap egr := h.2.2.2.1

theorem beginAdmissible.integ (h : beginAdmissible s a snap egr authorized) :
    checkIntegAdmissible s a snap := h.2.2.2.2

end GateAccessors

/-- The trichotomy is a total complementary partition: strict ALLOW implies admissible. -/
theorem beginAllow_admissible
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest)
    (egr : EgressKind → Prop) (authorized : Prop) :
    beginAllow s a snap egr authorized → beginAdmissible s a snap egr authorized := by
  rintro ⟨hcap, hauth, hclr, ⟨f1, f2, f3⟩, ⟨i1, i2, i3⟩⟩
  exact ⟨hcap, hauth, hclr,
    ⟨fun L E h1 h2 => Or.inl (f1 L E h1 h2),
     fun I J E h1 h2 h3 => Or.inl (f2 I J E h1 h2 h3),
     fun E h => Or.inl (f3 E h)⟩,
    ⟨fun L h => Or.inl (i1 L h),
     fun I J h1 h2 => Or.inl (i2 I J h1 h2),
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
  require s.agent_active a
  require a ≠ s.root_agent
  require s.tool_registered snap.tool
 -- Snapshot coherence: an incoherent band is a boundary rejection, never a kernel branch.
  require le_integ snap.integ_inspect snap.integ_floor
 -- The invocation slot, consumed identifier history, and challenge slot must all be fresh.
  require s.pending inv = none
  require ¬ s.consumed_ids inv
  require s.challenges inv = none
 -- Narrowing.
  require ∀ (E : EgressKind), egr E → snap.declared_egress E
 -- Coverage: an egress-bearing action cannot be admitted on an empty attestation.
  require (∃ (E : EgressKind), snap.declared_egress E) → (∃ (E : EgressKind), egr E)
 -- Each verdict must agree with the admission predicates; denial can transition only in monitor mode.
  require v = Verdict.allow → beginAllow s a snap egr authorized
  require v = Verdict.inspection_required →
    beginAdmissible s a snap egr authorized ∧ ¬ beginAllow s a snap egr authorized
  require v = Verdict.deny → ¬ beginAdmissible s a snap egr authorized
  require v = Verdict.deny → s.mode = Mode.monitor
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
def authorizeAdmits
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash) : Prop :=
  s.agent_active sc.agent
  ∧ sc.agent ≠ s.root_agent
  ∧ s.tool_registered sc.policy.tool
  ∧ le_integ sc.policy.integ_inspect sc.policy.integ_floor
  ∧ s.pending inv = none
  ∧ (∀ (E : EgressKind), sc.egress E → sc.policy.declared_egress E)
  ∧ ((∃ (E : EgressKind), sc.policy.declared_egress E) → (∃ (E : EgressKind), sc.egress E))
  ∧ beginAdmissible s sc.agent sc.policy sc.egress sc.authorized

/-- The live begin-time admission gate carried by `authorizeAdmits`. -/
theorem authorizeAdmits.toBeginAdmissible
    {s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash}
    {inv : InvocationId}
    {sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash}
    (h : authorizeAdmits s inv sc) :
    beginAdmissible s sc.agent sc.policy sc.egress sc.authorized := h.2.2.2.2.2.2.2

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
  require s.challenges inv = some sc
 -- Exact scope equality: invocation, challenge attribution, arguments, policy.
  require att.inv = inv
  require att.challenge = sc.challenge
  require att.args_hash = sc.args_hash
  require att.policy_digest = sc.policy.policy_digest
 -- One-use.
  require ¬ s.consumed_attestations att.id
 -- The invocation identifier was consumed when the challenge was created.
  require s.consumed_ids inv
 -- Admission needs both a positive attestation and current live admission.
  require admit = true → att.positive ∧ authorizeAdmits s inv sc
 -- Denial is the complementary branch.
  require admit = false → ¬ att.positive ∨ ¬ authorizeAdmits s inv sc
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
