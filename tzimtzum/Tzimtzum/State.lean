/-!
# TzimtzumV2 — Sorts, Lattices, and State Structure (Kav port)

Faithful port of the sorts, concrete lattices, and full state structure of the Veil
spec `tzimtzum/TzimtzumV2.lean` into the Kav framework (pure Lean, mathlib-free).

Encoding decisions (locked):
- Relations are **Prop-valued** fields of the state structure `St`.
- `ConfLevel` and `BudgetLevel` are **concrete inductives** with computable order/aux
  functions (this deletes Veil's ~30 ordering axioms).
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

inductive BudgetLevel where
  | bl_exhausted | bl1 | bl2 | bl3 | bl4 | bl5
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

/-- Numeric rank for the budget total order: bl_exhausted < bl1 < bl2 < bl3 < bl4 < bl5. -/
def budgetRank : BudgetLevel → Nat
  | .bl_exhausted => 0
  | .bl1          => 1
  | .bl2          => 2
  | .bl3          => 3
  | .bl4          => 4
  | .bl5          => 5

/-- The budget total order (replaces Veil's `le_budget` relation + ordering axioms). -/
def le_budget (a b : BudgetLevel) : Prop := budgetRank a ≤ budgetRank b

instance (a b : BudgetLevel) : Decidable (le_budget a b) := inferInstanceAs (Decidable (_ ≤ _))

/-- Saturating one-step debit of a budget level (replaces Veil's `budget_debit` function). -/
def budget_debit : BudgetLevel → BudgetLevel
  | .bl5          => .bl4
  | .bl4          => .bl3
  | .bl3          => .bl2
  | .bl2          => .bl1
  | .bl1          => .bl_exhausted
  | .bl_exhausted => .bl_exhausted

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
  agent_budget        : AgentId → BudgetLevel → Prop
  in_flight           : AgentId → InvocationId → Prop
  tool_registered     : ToolId → Prop
  gh_taint_invoked    : AgentId → ConfLevel → Prop
  gh_taint_received   : AgentId → ConfLevel → Prop
  override_used       : AgentId → ToolId → ConfLevel → Prop
  flow_override       : AgentId → ToolId → ConfLevel → Prop
  -- Immutable background — relations (Prop-valued) and functions (Veil lines 150-214, 245)
  tool_cap            : ToolId → CapKind → Prop
  tool_egress         : ToolId → EgressKind → Prop
  tool_conf_floor     : ToolId → ConfLevel
  tool_output_bounded : ToolId → Prop
  tool_issuer         : ToolId → IssuerId
  trusted_issuer      : IssuerId → Prop
  output_conforms     : AgentId → ToolId → Prop
  instruction_issuer  : InstructionId → IssuerId
  egress_allow_ceiling   : EgressKind → Option ConfLevel
  egress_inspect_ceiling : EgressKind → Option ConfLevel
  authorizer_allows   : AgentId → ToolId → Prop
  content_gate_passes : AgentId → ToolId → Prop
  invocation_tool     : InvocationId → ToolId
  -- Named individuals
  root_agent          : AgentId
  cap_declassify      : CapKind
  cap_refresh_budget  : CapKind
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

/-- Speculative (worst-case) taint: held taint, plus the conf-floor of every in-flight tool
(Veil lines 348-351). -/
def speculative_taint
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (l : ConfLevel) : Prop :=
  s.taint_levels a l ∨ (∃ I, s.in_flight a I ∧ s.tool_conf_floor (s.invocation_tool I) = l)

/-- Initial state predicate mirroring `after_init` (Veil lines 360-372): only `root_agent`
active, holding all capabilities and full budget; everything else empty. -/
def initial
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  (∀ (A : AgentId), s.agent_active A ↔ A = s.root_agent) ∧
  (∀ (A B : AgentId), ¬ s.agent_parent A B) ∧
  (∀ (A : AgentId) (C : CapKind), s.agent_cap A C ↔ A = s.root_agent) ∧
  (∀ (A : AgentId) (I : InstructionId), ¬ s.agent_instruction A I) ∧
  (∀ (A : AgentId) (L : ConfLevel), ¬ s.taint_levels A L) ∧
  (∀ (A : AgentId) (L : BudgetLevel),
      s.agent_budget A L ↔ (A = s.root_agent ∧ L = BudgetLevel.bl5)) ∧
  (∀ (A : AgentId) (I : InvocationId), ¬ s.in_flight A I) ∧
  (∀ (T : ToolId), ¬ s.tool_registered T) ∧
  (∀ (A : AgentId) (L : ConfLevel), ¬ s.gh_taint_invoked A L) ∧
  (∀ (A : AgentId) (L : ConfLevel), ¬ s.gh_taint_received A L) ∧
  (∀ (A : AgentId) (T : ToolId) (L : ConfLevel), ¬ s.override_used A T L) ∧
  (∀ (A : AgentId) (T : ToolId) (L : ConfLevel), ¬ s.flow_override A T L)

end Tzimtzum
