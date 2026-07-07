/-!
# TzimtzumV2 — Sorts, Lattices, and State Structure (Kav port)

Faithful port of the sorts, concrete lattices, and full state structure of the Veil
spec `tzimtzum/TzimtzumV2.lean` into the Kav framework (pure Lean, mathlib-free).

Encoding decisions (locked):
- Relations are **Prop-valued** fields of the state structure `St`.
- `ConfLevel` is a **concrete inductive** with computable order/aux functions (this deletes
  Veil's ~30 ordering axioms); the declassification budget is a bounded `Nat` meter.
- The remaining uninterpreted sorts (`AgentId`, `ToolId`, `InvocationId`, `CapKind`,
  `EgressKind`, `IssuerId`, `InstructionId`) are **type variables** carried as the
  parameters of `St`.
- Immutable background relations/functions and named individuals are **fields** of `St`
  (actions never update them; the Kav frame rule preserves them).

Definitions only — no actions, no invariants, no proofs (those are later tasks).
-/

namespace Tzimtzum

/-! ## Concrete lattices

`«public»` and `«internal»` are guillemet-escaped because they are Lean 4 keywords. -/

inductive ConfLevel where
  | «public» | «internal» | sensitive | restricted
  deriving DecidableEq, Repr

/-- Numeric rank for the confidentiality total order: public < internal < sensitive < restricted. -/
def confRank : ConfLevel → Nat
  | .«public»    => 0
  | .«internal»  => 1
  | .sensitive   => 2
  | .restricted  => 3

/-- The confidentiality total order (replaces Veil's `le_conf` relation + ordering axioms). -/
def le_conf (a b : ConfLevel) : Prop := confRank a ≤ confRank b

instance (a b : ConfLevel) : Decidable (le_conf a b) := inferInstanceAs (Decidable (_ ≤ _))

/-- Protocol budget capacity (fixed; NOT operator-configurable). -/
def budget_capacity : Nat := 16

/-- Sensitivity-weighted declassification cost. Public flows are free; Restricted is the dearest. -/
def declass_weight : ConfLevel → Nat
  | .«public»    => 0
  | .«internal»  => 1
  | .sensitive   => 2
  | .restricted  => 4

/-- Saturating budget credit: add `n`, clamped at capacity. Deliberately NOT a simp lemma and
made irreducible (like `ceilingAdmits`): the `min` blows up the transitive-unfold discharge
cascade (`simp only [<unfolds>] at *` corrupts even budget-independent VCs). Proofs that need
its value use the equation lemma explicitly (`simp [budget_saturating_credit]`); its only
properties used are `≤ budget_capacity` (`Nat.min_le_left`) and functionality. -/
def budget_saturating_credit (b n : Nat) : Nat := min budget_capacity (b + n)

attribute [irreducible] budget_saturating_credit

/-! ## Integrity lattice (dual of `ConfLevel`)

Integrity is the dual taint dimension: it FALLS as an agent ingests untrusted content
(confidentiality taint RISES as an agent reads secret data). `IntegLevel` mirrors `ConfLevel`
exactly — a concrete inductive with a numeric rank and a decidable order, no ordering axioms —
and `integ_weight` prices endorsement by how far below `attested` the ingested content sits
(the dual of `declass_weight`). -/

inductive IntegLevel where
  | untrusted | standard | trusted | attested
  deriving DecidableEq, Repr

/-- Numeric rank for the integrity total order: untrusted < standard < trusted < attested. -/
def integRank : IntegLevel → Nat
  | .untrusted => 0
  | .standard  => 1
  | .trusted   => 2
  | .attested  => 3

/-- The integrity total order (mirrors `le_conf`). -/
def le_integ (a b : IntegLevel) : Prop := integRank a ≤ integRank b

instance (a b : IntegLevel) : Decidable (le_integ a b) := inferInstanceAs (Decidable (_ ≤ _))

/-- Endorsement weight: dual of `declass_weight`. Attested content is free to endorse;
untrusted is dearest. -/
def integ_weight : IntegLevel → Nat
  | .attested  => 0
  | .trusted   => 1
  | .standard  => 2
  | .untrusted => 4

/-! ## State structure

The remaining uninterpreted sorts are the type parameters. Mutable relations, immutable
background relations/functions, and named individuals are all fields. -/

structure St (AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type) where
  -- Mutable relations (Veil lines 238-249)
  agent_active        : AgentId → Prop
  agent_parent        : AgentId → AgentId → Prop
  agent_cap           : AgentId → CapKind → Prop
  agent_instruction   : AgentId → InstructionId → Prop
  taint_levels        : AgentId → ConfLevel → Prop
  -- Integrity taint (dual of `taint_levels`): levels ingested. Effective integrity is the
  -- MIN of the set; EMPTY SET = FULLY TRUSTED (dual of "empty taint set = untainted"). Every
  -- gate quantifies ∀ over the set, so an empty set passes every gate.
  integ_levels        : AgentId → IntegLevel → Prop
  agent_budget        : AgentId → Nat
  in_flight           : AgentId → InvocationId → Prop
  -- Global freshness history: set at `invoke_start`, NEVER cleared (not by `revoke`,
  -- `cascade_revoke`, or `delegate` — it is history of invocation ids, not agent state).
  invocation_used     : InvocationId → Prop
  tool_registered     : ToolId → Prop
  override_used       : AgentId → ToolId → ConfLevel → Prop
  flow_override       : AgentId → ToolId → ConfLevel → Prop
  -- Immutable background — relations (Prop-valued) and functions (Veil lines 150-214, 245)
  tool_cap            : ToolId → CapKind → Prop
  tool_egress         : ToolId → EgressKind → Prop
  tool_conf_floor     : ToolId → ConfLevel
  -- Integrity floor + vouchable inspect-band floor (dual of `tool_conf_floor`): what an
  -- agent must be to invoke. ALLOW iff level ≥ floor, INSPECT iff level ≥ inspect_floor; an
  -- inspect floor above the allow floor is an empty band — coherent by construction.
  tool_integ_floor         : ToolId → IntegLevel
  tool_integ_inspect_floor : ToolId → IntegLevel
  -- Emission: what ingesting this tool's output does to the invoking agent's integrity.
  -- Floor and emission are genuinely distinct: `delete_repo` floor `trusted` / emission
  -- `attested`; `web_fetch` floor `untrusted` / emission `untrusted`.
  tool_output_integ        : ToolId → IntegLevel
  -- Robust-declassification floors for the levers (`return_endorsed`/`grant_override`,
  -- Task 13): a shared pair used at both crossing sites.
  lever_integ_floor         : IntegLevel
  lever_integ_inspect_floor : IntegLevel
  tool_output_bounded : ToolId → Prop
  tool_issuer         : ToolId → IssuerId
  trusted_issuer      : IssuerId → Prop
  -- Per-invocation oracle verdicts (rekeyed from static per-(agent, tool) background
  -- relations): a static relation cannot express "this output conformed, the next didn't",
  -- so every per-decision verdict is attested per invocation instead. `return_conforms`
  -- stays pairwise — there is no reified return object to key on.
  invocation_conforms : InvocationId → Prop
  return_conforms     : AgentId → AgentId → Prop
  instruction_issuer  : InstructionId → IssuerId
  egress_allow_ceiling   : EgressKind → Option ConfLevel
  egress_inspect_ceiling : EgressKind → Option ConfLevel
  invocation_authorized  : InvocationId → Prop
  -- The content-gate verdict is level-independent ("this invocation's content was
  -- approved"), not tied to the taint level being vouched against: CHECK 2b already
  -- vouches an old in-flight invocation against a NEW taint level, so keying on the
  -- invocation alone (rather than a (level, invocation) pair) was the honest reading
  -- all along.
  invocation_gate_passes : InvocationId → Prop
  invocation_tool     : InvocationId → ToolId
  -- Oracle-attested egress kinds of this specific invocation (the allowlist authorizer's
  -- URL/path → destination-class classification). A relation, not a function, because a
  -- single invocation may touch several channels.
  invocation_egress   : InvocationId → EgressKind → Prop
  -- Named individuals
  root_agent          : AgentId
  cap_declassify      : CapKind
  cap_credit_budget   : CapKind
  cap_grant_override  : CapKind

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-- Ceiling-band membership: `l` is at or below the ceiling `f e`; `none` = no level
passes (strict default-deny, including Public). Deliberately NOT a simp lemma: the
discharge cascades keep the flow gates ATOMIC (the fast opaque-relation proof shape of
the pre-ceiling spec) — only the ceiling field is exposed, so frame equations close by
congruence instead of unfolding the existential at every gate site. -/
def ceilingAdmits (f : EgressKind → Option ConfLevel) (l : ConfLevel) (e : EgressKind) : Prop :=
  ∃ c, f e = some c ∧ le_conf l c

-- Opaque to the discharge cascades (`#kav_check_action` skips irreducible defs in its
-- transitive unfold set); proofs that need the existential use the equation lemma
-- explicitly (`simp [ceilingAdmits]` / `unfold ceilingAdmits`).
attribute [irreducible] ceilingAdmits

/-- Derived flow-ALLOW relation: a level flows freely iff it is at or below the egress's
allow ceiling. Simp-unfolds one step to a `ceilingAdmits` atom over the ceiling field. -/
@[simp] def St.flow_allows
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : ConfLevel) (e : EgressKind) : Prop :=
  ceilingAdmits s.egress_allow_ceiling l e

/-- Derived flow-INSPECT relation: content-gated band, levels at or below the inspect
ceiling. An inspect ceiling below the allow ceiling is an empty inspect band — coherent. -/
@[simp] def St.flow_inspects
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : ConfLevel) (e : EgressKind) : Prop :=
  ceilingAdmits s.egress_inspect_ceiling l e

/-- Affordability: the weighted cost `w` is within the agent's budget. -/
def St.affordable (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (w : Nat) : Prop :=
  w ≤ s.agent_budget a

/-- Speculative (worst-case) taint: held taint, plus the conf-floor of every in-flight tool
(Veil lines 348-351). -/
def speculative_taint
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (l : ConfLevel) : Prop :=
  s.taint_levels a l ∨ (∃ I, s.in_flight a I ∧ s.tool_conf_floor (s.invocation_tool I) = l)

/-- Speculative (worst-case) integrity: held integrity levels, plus the emission of every
in-flight tool (dual of `speculative_taint`). -/
def speculative_integ
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (l : IntegLevel) : Prop :=
  s.integ_levels a l ∨ (∃ I, s.in_flight a I ∧ s.tool_output_integ (s.invocation_tool I) = l)

/-! ## The generic graduated gate

The conf side of the invoke gate is atomic via `ceilingAdmits` over an `EgressKind →
Option ConfLevel` ceiling map, `@[irreducible]` so the discharge cascades never unfold its
existential. The integrity side has no such map — floors are plain total `IntegLevel`
functions of the tool — so its ALLOW/INSPECT atoms are bare `le_integ` comparisons with
nothing to hide from the cascade. Design §9 open question ("exact Lean encoding of the
generic graduated gate") is resolved here as **two definitionally-aligned instantiations**,
not one shared polymorphic gate: `ceilingAdmits` and its conf callers (`St.flow_allows`,
`St.flow_inspects`) stay byte-identical to what Tasks 1-9 already proved over, and the
integrity instantiation below is free to stay transparent (no `irreducible` discipline
needed — there is no existential to blow up congruence closure). Same graduated SHAPE
(ALLOW / INSPECT+vouch / DENY), two bodies. -/

/-- Derived integrity-ALLOW relation for a tool: the agent's level clears the tool's floor
(dual of `St.flow_allows`). -/
@[simp] def St.integ_allows
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : IntegLevel) (t : ToolId) : Prop :=
  le_integ (s.tool_integ_floor t) l

/-- Derived integrity-INSPECT relation for a tool: the agent's level clears the vouchable
inspect floor (dual of `St.flow_inspects`). An inspect floor above the allow floor is an
empty band — coherent by construction. -/
@[simp] def St.integ_inspects
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : IntegLevel) (t : ToolId) : Prop :=
  le_integ (s.tool_integ_inspect_floor t) l

/-- Robust-declassification lever ALLOW (Task 13): the agent's level clears the shared lever
floor. -/
@[simp] def St.lever_allows
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : IntegLevel) : Prop :=
  le_integ s.lever_integ_floor l

/-- Robust-declassification lever INSPECT (Task 13): the agent's level clears the lever's
vouchable inspect floor. -/
@[simp] def St.lever_inspects
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : IntegLevel) : Prop :=
  le_integ s.lever_integ_inspect_floor l

/-- Initial state predicate mirroring `after_init` (Veil lines 360-372): only `root_agent`
active, holding all capabilities and full budget; everything else empty. -/
def initial
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  (∀ (A : AgentId), s.agent_active A ↔ A = s.root_agent) ∧
  (∀ (A B : AgentId), ¬ s.agent_parent A B) ∧
  (∀ (A : AgentId) (C : CapKind), s.agent_cap A C ↔ A = s.root_agent) ∧
  (∀ (A : AgentId) (I : InstructionId), ¬ s.agent_instruction A I) ∧
  (∀ (A : AgentId) (L : ConfLevel), ¬ s.taint_levels A L) ∧
  (∀ (A : AgentId) (L : IntegLevel), ¬ s.integ_levels A L) ∧
  (∀ (A : AgentId), s.agent_budget A = budget_capacity) ∧
  (∀ (A : AgentId) (I : InvocationId), ¬ s.in_flight A I) ∧
  (∀ (I : InvocationId), ¬ s.invocation_used I) ∧
  (∀ (T : ToolId), ¬ s.tool_registered T) ∧
  (∀ (A : AgentId) (T : ToolId) (L : ConfLevel), ¬ s.override_used A T L) ∧
  (∀ (A : AgentId) (T : ToolId) (L : ConfLevel), ¬ s.flow_override A T L)

end Tzimtzum
