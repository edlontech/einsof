import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 — `begin_invocation` and `authorize_inspected`

The invoke gate and its asynchronous inspection resolution
([[2026-07-24-tzimtzum-v4/architecture|architecture]] §6.2–6.3 as amended by E8, E9, E13,
E14, E19, E22, E23). Definitions only — proofs are Task 9 (`begin`) and Task 8
(`authorize`).

## The gate, shared by both actions

Nine checks over a frozen snapshot and live state. Two predicates, not a `Verdict`-valued
function (E8): `beginAllow` (every conjunct on its strict ALLOW arm) and `beginAdmissible`
(ALLOW-or-INSPECT). `inspection_required` is exactly `admissible ∧ ¬ allow`; `deny` is
`¬ admissible`; the two are a total complementary partition (`beginAllow_admissible`),
which is also the branch structure the Rust refinement dispatches on (§13).

**Vouch keying (E22).** The inspect arms of the pairwise checks 3b/5b require the *pending*
party's vouch — `allows ∨ (inspects ∧ vouched J)` — because the pairwise invariant is keyed
on the constrained party and an already-admitted unvouched record can never be retroactively
inspected (E2). The newcomer-constrained arms 3a/3c/5a/5c carry no vouch term: acquiring
that vouch is exactly what the challenge does, and the admission it produces
(`inspected att`) is what discharges the invariant's arm. Consequence: an inspect-band pair
against an unvouched pending record is a **deny** at begin, not a challenge — no later
attestation could make it lawful.

**The gate reads unrestricted speculative state (E10).** Monitor-bypassed records really
run, so they really constrain the next decision; only the *invariant* filters to contained
records.

## Effects by (verdict, mode) — E1(b) + E23

| verdict | `enforce` | `monitor` |
| --- | --- | --- |
| `allow` | pend `plain`/`permitted` | pend `plain`/`permitted` |
| `inspection_required` | create challenge, pend **nothing** | pend `bypassed` |
| `deny` | **not a transition** | pend `bypassed` |

A challenge is a *blocking* construct and monitor mode never blocks, so challenges are
enforce-only (E23); an unresolved enforce-mode challenge has produced no effect and ingested
nothing, so it pends nothing (E1(b)) and every quantifier over `pending` keeps meaning "may
actually execute". `inv` is consumed into `consumed_ids` on every arm that is a transition.

## `authorize_inspected` re-evaluates the gate against live state (E13)

Scope equality is necessary but nothing like sufficient: P, P′ and `clearance_confinement`
are statements about the *current* state, which may have moved between challenge and
resolution — new pending records, new taint, revocations. So resolution re-runs the
admissible gate (the newcomer's vouch is the admission being granted; the pending-party
arms of 3b/5b are re-checked per E22) and **can deny a positively attested invocation**.
The structural conjuncts (`agent_active`, `tool_registered`, narrowing, coverage,
snapshot coherence, `pending inv = none`) are re-required rather than derived from
`challenge_scoped`, fail-closed: the action does not lean on the bundle for its own safety.

Under monitor mode this action is dead code — no challenge is ever created there (E23), so
the `∃`-guard is unsatisfiable; §6.3's monitor arm is deleted rather than modelled.

One deliberate deviation from §6.3: a **scope-mismatched** attestation is a boundary
rejection (guard failure — no transition), not a challenge-closing deny. Burning the
challenge on a mismatch would let one garbage attestation kill a legitimate pending
inspection; the challenge stays open for the correct attestation, and operator recourse for
a wedged challenge is `revoke` (which resolves it fail-closed). A scope-*matching* negative
attestation does close the challenge, consuming the attestation.
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
  /-- Scope: the challenge it answers (attribution — the map is keyed by `inv`, E14). -/
  challenge     : ChallengeId
  /-- Scope: unchanged arguments. -/
  args_hash     : ContentHash
  /-- Scope: unchanged policy. -/
  policy_digest : PolicyDigest
  /-- The inspector's verdict. -/
  positive      : Prop

/-! ## The nine checks -/

/-- CHECK 1 — capability. Two-valued: no inspect band on capabilities. -/
def checkCapability
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (snap : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  ∀ (C : CapKind), snap.required_caps C → s.agent_cap a C

/-- CHECK 2a/2b/2c — confidentiality clearance (E9). Two-valued. 2a reads the
*unrestricted* speculative taint (E10); 2b/2c are what make `clearance_confinement`
inductive — the new `output_conf` joins the agent's speculative taint post-state, so it
must clear every pending record's frozen clearance and its own. -/
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

/-- CHECK 3a/3b/3c on ALLOW-or-INSPECT. 3a/3c (newcomer-constrained) carry no vouch term —
the challenge supplies it (E22). 3b (pending-party-constrained) requires the pending
record's vouch: an unvouched pending record in an inspect-band pair is a deny. -/
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

/-- CHECK 5a/5b/5c on ALLOW-or-INSPECT, vouch keying as in `checkFlowAdmissible` (E22). -/
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

/-- Verdict `allow`: every check on its strict ALLOW arm. CHECK 4 is the `authorized`
conjunct — the per-invocation authorizer verdict, two-valued. -/
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

Parameters: the acting agent, the fresh invocation id, the challenge attribution id, the
frozen snapshot, the attested egress set, the arguments hash, the authorizer verdict, and
the computed canonical `Verdict` (E8) — related to the checks by guard, so it is canonical
rather than a free choice. -/

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
  -- Freshness (T-9): `pending` + `consumed_ids` replace V3's `invocation_used`.
  require s.pending inv = none
  require ¬ s.consumed_ids inv
  require s.challenges inv = none
  -- Narrowing.
  require ∀ (E : EgressKind), egr E → snap.declared_egress E
  -- Coverage: an egress-bearing action cannot be admitted on an empty attestation.
  require (∃ (E : EgressKind), snap.declared_egress E) → (∃ (E : EgressKind), egr E)
  -- Verdict correctness (the worst-of-classification rule, E8).
  require v = Verdict.allow → beginAllow s a snap egr authorized
  require v = Verdict.inspection_required →
    beginAdmissible s a snap egr authorized ∧ ¬ beginAllow s a snap egr authorized
  require v = Verdict.deny → ¬ beginAdmissible s a snap egr authorized
  -- An enforce-mode hard deny is not a transition; a monitor-mode one is (and pends).
  require v = Verdict.deny → s.mode = Mode.monitor
  -- The (verdict, mode) dispatch is a `match` on two small inductives, NOT nested `ite`s:
  -- an `ite` condition like `v = inspection_required ∧ s.mode = enforce` carries a
  -- `Classical.propDecidable` instance over an `And` with a state projection, and the
  -- discharge cascade `whnf`s that instance at every congruence step — measured at Task 7
  -- as the difference between a 3 s discharge and an 8M-heartbeat timeout (the same
  -- failure class as E8, one level down). A constructor `match` needs no `Decidable` at
  -- all and `grind` splits it natively.
  pending := fun I =>
    if I = inv then
      (match v, s.mode with
        | Verdict.allow, _ =>
          some { agent := a, policy := snap, egress := egr, admission := Admission.plain,
                 disposition := Disposition.permitted, authorized := authorized,
                 quarantined := False }
        -- E1(b): an unresolved enforce-mode challenge pends nothing.
        | Verdict.inspection_required, Mode.enforce => none
        -- Monitor-mode inspection_required or deny (E23): the effect really runs, so it
        -- really constrains. The canonical verdict stays in the event.
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

/-- The full live admission condition for challenge resolution (E13): the structural
re-checks, fail-closed, then the admissible gate. One named predicate so the admit and deny
guards are exact complements — anything less and the branch decision stops being canonical
(a state could satisfy neither guard, or the adapter could pick). -/
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

/-! The scope is a *parameter* pinned to the challenge map by guard (E19), so the update
expressions can read it. `admit` is the branch decision, related to the attestation verdict
and the live gate by guard — canonical, not a free choice. -/

open Classical in
kav_action authorize_inspected (inv : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash)
    (att : InspectionAttestation InvocationId ChallengeId AttestationId PolicyDigest
      ContentHash)
    (admit : Bool) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  -- The challenge exists and `sc` is it (E14: keyed by invocation).
  require s.challenges inv = some sc
  -- Exact scope equality: invocation, challenge attribution, arguments, policy.
  require att.inv = inv
  require att.challenge = sc.challenge
  require att.args_hash = sc.args_hash
  require att.policy_digest = sc.policy.policy_digest
  -- One-use.
  require ¬ s.consumed_attestations att.id
  -- Freshness history (both arms): the new pending record must satisfy
  -- `pending_ids_consumed`, and this action adds nothing to `consumed_ids` — `inv` was
  -- consumed when the challenge was created. Re-required fail-closed rather than derived
  -- from `challenge_scoped`, like every other structural conjunct here.
  require s.consumed_ids inv
  -- Admission requires a positive verdict AND the live gate (E13): the newcomer's vouch is
  -- the admission being granted, the pending-party arms re-check per E22. State may have
  -- moved since the challenge was created; a positively attested invocation can be denied.
  require admit = true → att.positive ∧ authorizeAdmits s inv sc
  -- Denial is the exact complement, so the branch decision is canonical.
  require admit = false → ¬ att.positive ∨ ¬ authorizeAdmits s inv sc
  pending := fun I =>
    if I = inv ∧ admit = true then
      some { agent := sc.agent, policy := sc.policy, egress := sc.egress,
             admission := Admission.inspected att.id,
             disposition := Disposition.permitted, authorized := sc.authorized,
             quarantined := False }
    else s.pending I
  -- The challenge closes on both arms; T-5 frames every label for every agent.
  challenges := fun I => if I = inv then none else s.challenges I
  consumed_attestations := fun X => s.consumed_attestations X ∨ X = att.id

/-! ## Non-vacuity (E12) -/

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
