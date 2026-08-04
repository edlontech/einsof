import Tzimtzum.State

/-!
# TzimtzumV4 — shared point-update helpers

`pending` and `challenges` are keyed by invocation but *owned* by an agent, so an
agent-scoped edit is an `Option`-filtering traversal rather than V3's pointwise conjunction
on a curried relation. These helpers are shared by every action that performs one, so the
actions cannot drift, and they are the exact shape the Rust `VecMap` retain/update loops
refine to (explicit index loop, no closure, no early `return`).

Each helper ships directed `@[simp]` characterization lemmas. Without them the discharge
cascade cannot see through the `Classical.propDecidable` instance on the `ite` — `grind`
stalls on it rather than splitting — and roughly ten conjuncts across five actions would
re-derive the same case analysis per goal.

The `ite` conditions here are all *small*: a single equality on an opaque sort or on a
three-constructor inductive. Architecture E8's blow-up is about `ite` over a large `Prop`
(the nine-check gate), whose decidability instance the cascade must `whnf` at every step;
that hazard does not apply to these.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

open Classical in
/-- Drop every pending record owned by `a`. -/
noncomputable def dropPendingOf
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) :
    InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) :=
  fun I =>
    match p I with
    | some J => if J.agent = a then none else some J
    | none => none

open Classical in
/-- Resolve fail-closed every open challenge owned by `a`: the challenge dies and nothing
pends. -/
noncomputable def dropChallengesOf
    (c : InvocationId →
      Option (ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
        ContentHash))
    (a : AgentId) :
    InvocationId →
      Option (ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
        ContentHash) :=
  fun I =>
    match c I with
    | some sc => if sc.agent = a then none else some sc
    | none => none

open Classical in
/-- Destroy every crossing grant held by `a`. -/
noncomputable def dropGrantsOf (g : AgentId → AssignmentDigest → Option CrossingGrant) (a : AgentId) :
    AgentId → AssignmentDigest → Option CrossingGrant :=
  fun A D => if A = a then none else g A D

/-! ## Characterization lemmas -/

@[simp] theorem dropPendingOf_eq_some
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) :
    dropPendingOf p a I = some J ↔ p I = some J ∧ J.agent ≠ a := by
  unfold dropPendingOf
  cases h : p I with
  | none => simp
  | some K => by_cases hk : K.agent = a <;> simp [hk] <;> grind

@[simp] theorem dropPendingOf_eq_none
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) (I : InvocationId) :
    dropPendingOf p a I = none ↔
      ∀ J, p I = some J → J.agent = a := by
  unfold dropPendingOf
  cases h : p I with
  | none => simp
  | some K => by_cases hk : K.agent = a <;> simp [hk]

@[simp] theorem dropChallengesOf_eq_some
    (c : InvocationId →
      Option (ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
        ContentHash))
    (a : AgentId) (I : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash) :
    dropChallengesOf c a I = some sc ↔ c I = some sc ∧ sc.agent ≠ a := by
  unfold dropChallengesOf
  cases h : c I with
  | none => simp
  | some K => by_cases hk : K.agent = a <;> simp [hk] <;> grind

@[simp] theorem dropChallengesOf_eq_none
    (c : InvocationId →
      Option (ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
        ContentHash))
    (a : AgentId) (I : InvocationId) :
    dropChallengesOf c a I = none ↔ ∀ sc, c I = some sc → sc.agent = a := by
  unfold dropChallengesOf
  cases h : c I with
  | none => simp
  | some K => by_cases hk : K.agent = a <;> simp [hk]

@[simp] theorem dropGrantsOf_self
    (g : AgentId → AssignmentDigest → Option CrossingGrant) (a : AgentId)
    (D : AssignmentDigest) :
    dropGrantsOf g a a D = none := by
  unfold dropGrantsOf; simp

@[simp] theorem dropGrantsOf_other
    (g : AgentId → AssignmentDigest → Option CrossingGrant) (a A : AgentId)
    (D : AssignmentDigest) (h : A ≠ a) :
    dropGrantsOf g a A D = g A D := by
  unfold dropGrantsOf; simp [h]

/-! ## Demotion

A pending record whose gates the environment has broken under it — a monitor-mode
ingestion, or a settlement that launders a bypassed record's provenance into the agent's
held labels — stops being *claimed* gated. `contained` is exactly that claim, so the honest
edit is to demote the agent's live permits to `monitor_bypassed` rather than to weaken the
confinement conjuncts (E18). `admission` is deliberately left alone: it records how the
invocation was *admitted*, which is history and does not change. Only `bypass_mode_sound`'s
second clause reads `admission`, and demotion never sets it to `bypassed`. -/

open Classical in
/-- Demote every pending record owned by `a` to `monitor_bypassed`. -/
noncomputable def demoteAllOf
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) :
    InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) :=
  fun I =>
    match p I with
    | some J =>
      if J.agent = a then some { J with disposition := Disposition.monitor_bypassed } else some J
    | none => none

/-- The firing form: the LHS is `demoteAllOf p a I = some K` with `K` in head position, so
`simp` can match it against an opaque `s.pending`. The directed lemmas below are the
convenient form once the pre-record is known, but they must NOT be `@[simp]` — their `J`
occurs only in hypotheses, so `simp` would have to solve `p I = some ?J` with `?J`
unassigned and would silently never fire. -/
@[simp] theorem demoteAllOf_eq_some
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) (I : InvocationId)
    (K : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) :
    demoteAllOf p a I = some K ↔
      (∃ J, p I = some J ∧ J.agent = a
        ∧ K = { J with disposition := Disposition.monitor_bypassed })
      ∨ (p I = some K ∧ K.agent ≠ a) := by
  unfold demoteAllOf
  cases h : p I with
  | none => simp
  | some J => by_cases hj : J.agent = a <;> simp [hj] <;> grind

theorem demoteAllOf_of_agent
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (h : p I = some J) (ha : J.agent = a) :
    demoteAllOf p a I = some { J with disposition := Disposition.monitor_bypassed } := by
  unfold demoteAllOf; rw [h]; simp [ha]

theorem demoteAllOf_of_other
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (h : p I = some J) (ha : J.agent ≠ a) :
    demoteAllOf p a I = some J := by
  unfold demoteAllOf; rw [h]; simp [ha]

@[simp] theorem demoteAllOf_eq_none
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (a : AgentId) (I : InvocationId) :
    demoteAllOf p a I = none ↔ p I = none := by
  unfold demoteAllOf
  cases h : p I with
  | none => simp
  | some K => by_cases hk : K.agent = a <;> simp [hk]

/-! ## Settlement point-update

Hoisted out of `settle_invocation`'s update expression: a `let`-bound lambda spliced into
`next` is zeta-reduced into both branches of the surrounding `ite` and has no
characterization lemma, so the cascade cannot compose it with `demoteAllOf_*`. -/

open Classical in
/-- Close `inv` (ordinary outcomes) or flag it quarantined (`ambiguous`), leaving every
other key alone. -/
noncomputable def settleAt
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (inv : InvocationId) (outcome : Outcome) :
    InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) :=
  fun I =>
    if I = inv then
      (match p I with
        | some J => if outcome = Outcome.ambiguous then some { J with quarantined := True } else none
        | none => none)
    else p I

@[simp] theorem settleAt_other
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (inv : InvocationId) (outcome : Outcome) (I : InvocationId) (h : I ≠ inv) :
    settleAt p inv outcome I = p I := by
  unfold settleAt; simp [h]

@[simp] theorem settleAt_self_closed
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (inv : InvocationId) (outcome : Outcome) (h : outcome ≠ Outcome.ambiguous) :
    settleAt p inv outcome inv = none := by
  unfold settleAt
  cases hp : p inv <;> simp [h, hp]

@[simp] theorem settleAt_self_quarantined
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (inv : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (h : p inv = some J) :
    settleAt p inv Outcome.ambiguous inv = some { J with quarantined := True } := by
  unfold settleAt; simp [h]

-- (A separate frame lemma is unnecessary: `demoteAllOf_of_agent` / `demoteAllOf_of_other`
-- already exhibit the post-record as the pre-record with at most `disposition` changed.)

end Tzimtzum
