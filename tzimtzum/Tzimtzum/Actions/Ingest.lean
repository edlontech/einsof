import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 — `ingest`

Delivery of governed data to an agent at a frozen provenance pair
([[2026-07-24-tzimtzum-v4/architecture|architecture]] §6.1). Definitions only.

For external ingress the provenance is the frozen source-policy label pair; for
agent-to-agent context (parent-to-child at delegation time, unendorsed child returns,
foreign-agent responses) it is read from the source agent's kernel labels, so policy can
never relabel a contaminated agent as cleaner. Missing provenance is a boundary rejection,
never a conservative default invented inside the kernel.

Updates are always the same two insertions: taint only ever grows, integrity only ever
falls (T-3, T-4). What differs by mode is whether the *holds* are enforced.

## The two holds

Carried from V3's `sentinel_elevate_taint` / `sentinel_degrade_integrity` gates with the
override arms removed. The kernel refuses an ingestion that would break a live permit; the
adapter re-submits after settlement. That is V3's "blocked degrade = the Warden must hold
the ingestion" platform obligation, made structural.

## Monitor mode demotes rather than lying (E18)

In monitor mode there is no hold: the degradation applies unconditionally, because kernel
state must track reality. But that genuinely breaks `flow_confinement` and
`integrity_confinement` for the agent's already-permitted pending records — the labels moved
under a live permit and no guard can re-establish them.

Rather than conditioning those conjuncts on `mode = enforce` (which would make the whole
gate half of the bundle vacuous under monitor, for a mode that still really executes
effects), a bypassed ingestion **demotes** the agent's pending records to
`monitor_bypassed`. `contained` then means exactly "still claimed gated", the confinement
conjuncts stay unconditional and true in *both* modes, and `bypass_mode_sound` still holds
because demotion happens only under monitor. This composes with E10: that handles a
bypassed *begin*, this handles a bypassed *ingest*.

Demotion is deliberately per-agent rather than per-broken-record. Deciding record by record
would put the whole hold predicate inside an `ite` condition — the `Classical.propDecidable`
blow-up of E8 — and the coarser rule is the honest one anyway: this ingestion was not
contained, so none of that agent's live permits is still claimed contained.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## The holds

Stated as standalone predicates rather than inline in the guard so that the action's
`disposition` parameter can be *related* to them (the E8 discipline: a decision that
controls a branch is an input plus a correctness guard, never an `ite` condition). -/

/-- Conf hold: the incoming taint level is admissible for every egress channel of every
pending invocation of `a` — ALLOW, or INSPECT with the pending party vouched (E2). -/
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
invocation of `a` — ALLOW, or INSPECT with the pending party vouched. -/
def ingestIntegHold
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (pinteg : IntegLevel) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.agent = a →
      integ_allows pinteg J.policy ∨ (integ_inspects pinteg J.policy ∧ vouched J)

/-- Clearance hold (spike finding E9, carried to `ingest`).

Without this the permitted path falsifies `clearance_confinement`: the inserted `pconf`
lands in `taint_levels a`, which `speculative_taint_contained` includes unconditionally, so
a contained pending invocation whose frozen `conf_clearance` is below `pconf` is left
violating its own clearance with no guard able to re-establish it. The flow hold does not
cover this — flow gates per *channel*, clearance gates per *target*, which is the whole
reason CHECK 2 exists. -/
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
  -- Agent-to-agent provenance is read from the SOURCE AGENT'S KERNEL LABELS, never from
  -- policy: the declared pair must dominate what the source actually holds, in both
  -- dimensions. Without this the adapter could deliver `restricted`/`untrusted` content
  -- labelled `public`/`attested` and the kernel would never know -- the bundle only proves
  -- monotonicity, so under-tainting is invisible to it. `src = none` is external ingress,
  -- where the pair is the frozen source-policy label and there is no kernel-side source.
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

/-! ## Non-vacuity (E12)

`d` is a trusted input, so the guards must not be jointly unsatisfiable. Exactly one
disposition is legal per state, and one always exists unless the holds fail under
`enforce` -- which is precisely the case where the kernel refuses and the adapter re-submits
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
