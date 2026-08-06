import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 `ingest`

`ingest` adds a frozen provenance pair to an active agent's taint and integrity observations.
Agent-to-agent provenance must bound the source agent's held labels; external provenance is an
input. A permitted ingestion satisfies the flow, clearance, and integrity holds for the target's
pending records. A monitor bypass requires monitor mode and demotes the target's pending records
so they no longer claim their gates passed.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## The holds

The standalone hold predicates let the guard constrain the supplied disposition instead of
selecting a branch with a proposition-valued conditional. -/

/-- Conf hold: the incoming taint level is admissible for every egress channel of every
pending invocation of `a`; ALLOW, or INSPECT with the pending party vouched. -/
def ingestConfHold
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (pconf : ConfLevel) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.pending I = some J → J.agent = a → J.egress E →
      s.flow_allows pconf E ∨ (s.flow_inspects pconf E ∧ vouched J)

/-- Integ hold: the incoming integrity level clears the frozen floor of every pending
invocation of `a`; ALLOW, or INSPECT with the pending party vouched. -/
def ingestIntegHold
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (pinteg : IntegLevel) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.agent = a →
      integ_allows pinteg J.policy ∨ (integ_inspects pinteg J.policy ∧ vouched J)

/-- Clearance hold: incoming confidentiality must clear every pending record owner's frozen
clearance ceiling, because the value is inserted into that owner's held taint. -/
def ingestClearHold
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (pconf : ConfLevel) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.agent = a → clearance_admits pconf J.policy

/-- All three holds. -/
def ingestHolds
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (pconf : ConfLevel) (pinteg : IntegLevel) : Prop :=
  ingestConfHold s a pconf ∧ ingestClearHold s a pconf ∧ ingestIntegHold s a pinteg

/-! `ingest (a, prov)` where `prov = (pconf, pinteg)`, plus the enforcement `disposition`.

`d = permitted` is the enforce-mode path and requires both holds; `d = monitor_bypassed` is
the monitor-mode path, requires that a hold actually failed (so the disposition is
canonical, not a free choice) and that the mode really is `monitor`, and demotes the
agent's live permits. `d = blocked` is not a transition: a refused ingestion changes no
state, and the adapter re-submits after settlement. -/

open Classical in
kav_action ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require s.agent_active a
 -- Agent-to-agent provenance must bound all labels held by the source agent. This prevents
 -- the declared pair from making source content appear less confidential or more trustworthy.
 -- `src = none` denotes external ingress, whose frozen provenance is supplied as input.
  require ∀ src', src = some src' →
    (∀ L, s.taint_levels src' L → le_conf L pconf)
    ∧ (∀ L, s.integ_levels src' L → le_integ pinteg L)
  require d ≠ Disposition.blocked
  require d = Disposition.permitted → ingestHolds s a pconf pinteg
  require d = Disposition.monitor_bypassed → ¬ ingestHolds s a pconf pinteg
  require d = Disposition.monitor_bypassed → s.mode = Mode.monitor
  taint_levels := fun A L => s.taint_levels A L ∨ (A = a ∧ L = pconf)
  integ_levels := fun A L => s.integ_levels A L ∨ (A = a ∧ L = pinteg)
  pending :=
    if d = Disposition.monitor_bypassed then demoteAllOf s.pending a else s.pending

/-! ## Non-vacuity

`d` is a trusted input, so the guards must not be jointly unsatisfiable. Exactly one
disposition is legal per state, and one always exists unless the holds fail under
`enforce`; which is precisely the case where the kernel refuses and the adapter re-submits
after settlement. -/

theorem ingest_disposition_total
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (pconf : ConfLevel) (pinteg : IntegLevel)
    (hmode : ingestHolds s a pconf pinteg ∨ s.mode = Mode.monitor) :
    ∃ d : Disposition,
      d ≠ Disposition.blocked
      ∧ (d = Disposition.permitted → ingestHolds s a pconf pinteg)
      ∧ (d = Disposition.monitor_bypassed → ¬ ingestHolds s a pconf pinteg)
      ∧ (d = Disposition.monitor_bypassed → s.mode = Mode.monitor) := by
  by_cases h : ingestHolds s a pconf pinteg
  · exact ⟨Disposition.permitted, by simp, fun _ => h, by simp, by simp⟩
  · exact ⟨Disposition.monitor_bypassed, by simp, by simp, fun _ => h,
      fun _ => hmode.resolve_left h⟩

end Tzimtzum
