# Campaign B — Numeric Budget Meter + return_endorsed Conformance Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the 5-step `BudgetLevel` enum with a bounded numeric (`Nat`/`u8`) declassification meter with sensitivity-weighted debits, convert `sentinel_refresh_budget` into a granular `sentinel_credit_budget`, and close eval finding P2 by gating `return_endorsed` on a new `return_conforms` conformance verdict — across all four layers: Kav spec, Rust kernel, Aeneas refinement, ex_argus.

**Architecture:** `agent_budget` becomes `AgentId → Nat` (spec relation `AgentId → Nat → Prop`; Rust `VecMap<AgentId, u8>`, absence == capacity). Protocol constants `budget_capacity = 16` and `declass_weight : ConfLevel → Nat` (Public 0 / Internal 1 / Sensitive 2 / Restricted 4) are fixed, not operator-configurable. The ugly 5-way enum disjunctions in `invoke_complete` / `return_endorsed` / `grant_override` postconditions collapse into linear arithmetic (`omega` / `scalar_tac`), which is the source of the "less proof work than Campaign A" claim. `return_endorsed` gains a `return_conforms : AgentId → AgentId → Prop` oracle field, filling the dead `require True` slot. The refinement is re-extracted and rebuilt to `implementation_sound` against the (still 13-action) system.

**Tech Stack:** Lean 4 (Kav framework, mathlib-free), Rust edition 2024 (zero-dep argus-kernel, Aeneas-extractable idioms), Aeneas/Charon, Elixir + Rustler.

**Design doc:** Obsidian `argus_and_tzimtzum/designs/2026-06-11-operator-fatigue-protocol-design.md` §Mechanism 5 (+ P2 ride-along). Upstream eval: `argus_and_tzimtzum/designs/2026-06-11-tzimtzum-argus-evaluation.md` (P2). All decisions there are locked and user-approved; do not relitigate them.

**Sequencing rule (locked):** Stage exits green before the next starts. Spec → kernel → extraction/refinement → bindings. The whole campaign merges only when ALL exit criteria (Stage 5) pass.

**Branch:** create `feat/campaign-b-numeric-budget` from `main` before Task 1.

---

## Hard constraints (read before any task)

- **Aeneas-extractable Rust only** in argus-kernel: Vec-backed `VecMap`/`VecSet`, explicit index `while` loops, no closures in loops, no early `return` inside loops (early return in straight-line code is fine), owned accessors when the index is computed. The budget map stays a `VecMap<AgentId, u8>`; all arithmetic is `u8` saturating (`saturating_sub`, `saturating_add` + a `.min(CAP)`), never `usize` or checked ops. Mirror the idioms already in `transitions.rs`/`state.rs`.
- **`u8` is the budget cell type.** `budget_capacity = 16` fits trivially; saturating sub discharges underflow, `min(capacity, …)` discharges the cap. No new numeric overflow surface.
- **Kav naming:** never name an action param `par`. `autoImplicit` stays enabled. Capital binders in invariants carry explicit type annotations.
- **One safety set changes shape, none change names.** The 10 safeties keep their names. The 15 strengthening invariants gain ONE: `budget_bounded` (→ 16). `budget_unique` / `active_has_budget` keep their names and statements (re-typed `BudgetLevel` → `Nat`).
- After any Lean toolchain change: `lake exe cache get` from `tzimtzum/` before `make build`.
- Commit style: simple one-line messages, no co-author trailers, no trailing whitespace.

---

## File structure (what each layer touches)

| Layer | Files |
|---|---|
| Kav spec | `tzimtzum/Tzimtzum/State.lean` (delete `BudgetLevel`, add constants + `Nat` budget + `affordable`/`min_credit` helpers), `Invariants.lean` (`budget_bounded`, re-type the two budget invariants), `Actions.lean` (invoke_complete / return_endorsed / sentinel → credit / grant_override), `Soundness/Pres{InvokeComplete,ReturnEndorsed,GrantOverride,SentinelRefreshBudget}.lean` + any `Init`/`Check` files |
| Rust kernel | `types.rs` (delete `BudgetLevel`, add `declass_weight`), `state.rs` (`VecMap<…,u8>` + helpers), `transitions.rs` (4 actions), `traits.rs` (`return_conforms`), `error.rs` (`NotConforming`), `capability.rs` (`RefreshBudget`→`CreditBudget`), `event.rs` (`SentinelCreditBudget`), `kernel.rs` (driver), `tests/safety_properties.rs` |
| Refinement | `argus_kernel.llbc` + `formal-lean/ArgusLean/Generated/ArgusKernel.lean` (re-extract), `Refinement/Bridging/*` (budget specs), `Refinement/Unified/Preservation/{InvokeComplete,ReturnEndorsed,GrantOverride,SentinelRefreshBudget→SentinelCreditBudget}.lean`, `Unified/{Relation,Bundle,Soundness}.lean`, `InitRefinement.lean` |
| ex_argus | `lib/ex_argus.ex` (`@state_version 2`→`3`), `lib/ex_argus/kernel/{state,types}.ex`, `lib/ex_argus/{native,offline,instance,replay}.ex`, `native/argus_nif/src/{enums,state,event,nifs,instance}.rs` |

---

## Stage 1 — Kav spec (tzimtzum/)

This stage is the source of truth; everything else refines against it. Each task ends with `make build` from `tzimtzum/` green. The full VC re-check happens in Task 6.

### Task 1: State.lean — numeric budget + constants

**Files:**
- Modify: `tzimtzum/Tzimtzum/State.lean`

- [ ] **Step 1: Delete the `BudgetLevel` inductive and its order/aux defs.** Remove `inductive BudgetLevel`, `budgetRank`, `le_budget`, the `Decidable (le_budget …)` instance, and `budget_debit`.

- [ ] **Step 2: Add the protocol constants** (place near `confRank`/`le_conf`, after the `ConfLevel` block):

```lean
/-- Protocol budget capacity (fixed; NOT operator-configurable). -/
def budget_capacity : Nat := 16

/-- Sensitivity-weighted declassification cost. Public flows are free; Restricted is the dearest. -/
def declass_weight : ConfLevel → Nat
  | .«public»    => 0
  | .«internal»  => 1
  | .sensitive   => 2
  | .restricted  => 4
```

- [ ] **Step 3: Re-type the budget field.** In the `St` structure, change `agent_budget : AgentId → BudgetLevel → Prop` to:

```lean
  agent_budget : AgentId → Nat → Prop
```

- [ ] **Step 4: Add the `affordable` derived def** (St-namespace, alongside the flow derived defs):

```lean
/-- The granter/agent can pay weight `w`: its (unique) budget covers `w`. -/
def St.affordable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId}
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (w : Nat) : Prop :=
  ∃ b, s.agent_budget a b ∧ w ≤ b
```

(Match the exact `St.` derived-def style already used for the ceiling/flow helpers in this file — copy that signature boilerplate.)

- [ ] **Step 5:** `make build` from `tzimtzum/`. Expect errors only in `Invariants.lean`/`Actions.lean`/`Soundness/*` (fixed in later tasks). The `State.lean` module itself must elaborate.

- [ ] **Step 6: Commit** — `feat(tzimtzum): numeric budget meter + declass_weight`

### Task 2: Invariants.lean — budget invariants over `Nat` + `budget_bounded`

**Files:**
- Modify: `tzimtzum/Tzimtzum/Invariants.lean`

- [ ] **Step 1: Re-type `budget_unique` and `active_has_budget`.** Their bodies are unchanged except the level type is now `Nat`:

```lean
def budget_unique
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (L1 L2 : Nat),
    s.agent_active A ∧ s.agent_budget A L1 ∧ s.agent_budget A L2 → L1 = L2

def active_has_budget
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId), s.agent_active A → ∃ (L : Nat), s.agent_budget A L
```

- [ ] **Step 2: Add `budget_bounded`** (new 16th strengthening invariant — keeps the reachable budget space finite so `Fin (budget_capacity+1)` model-checking / Plausible still terminate):

```lean
/-- **budget_bounded**: every recorded budget is within capacity (keeps the state space finite). -/
def budget_bounded
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (L : Nat), s.agent_budget A L → L ≤ budget_capacity
```

- [ ] **Step 3: Register it** in the invariant list (after `active_has_budget`):

```lean
  , ("budget_bounded", budget_bounded)
```

- [ ] **Step 4:** `make build` — `Invariants.lean` elaborates (`Actions.lean` may still error).

- [ ] **Step 5: Commit** — `feat(tzimtzum): budget_bounded invariant + Nat budget invariants`

### Task 3: Actions.lean — invoke_complete weighted + no-debit-when-already-tainted

**Files:**
- Modify: `tzimtzum/Tzimtzum/Actions.lean` (lines ~159-192)

The endorsed (zero-taint) condition gains the **already-tainted** guard and swaps `¬ exhausted` for `affordable`. Define a local shorthand in prose: let `floor := s.tool_conf_floor (s.invocation_tool inv)` and
`endorsed := s.tool_output_bounded (s.invocation_tool inv) ∧ s.output_conforms a (s.invocation_tool inv) ∧ s.affordable a (declass_weight floor) ∧ ¬ s.taint_levels a floor`.

- [ ] **Step 1: Rewrite the three updated fields.** Replace the `¬ (output_bounded ∧ output_conforms ∧ ¬ bl_exhausted)` predicate everywhere in `invoke_complete` with `¬ endorsed` (the new 4-conjunct), and replace the 5-way `agent_budget` debit disjunction with numeric subtraction:

```lean
  taint_levels := fun A L =>
    s.taint_levels A L
    ∨ (A = a ∧ ¬ endorsed ∧ s.tool_conf_floor (s.invocation_tool inv) = L)
  gh_taint_invoked := fun A L =>
    s.gh_taint_invoked A L
    ∨ (A = a ∧ ¬ endorsed ∧ s.tool_conf_floor (s.invocation_tool inv) = L)
  agent_budget := fun A L =>
    (A = a ∧
      ( (endorsed ∧ ∀ b, s.agent_budget a b → L = b - declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
        ∨ (¬ endorsed ∧ s.agent_budget a L) ))
    ∨ (A ≠ a ∧ s.agent_budget A L)
```

where `endorsed` is the 4-conjunct above written inline (no `let` in the action body — Kav action fields are bare). `∀ b, agent_budget a b → L = b - w` pins the post-budget via `budget_unique`/`active_has_budget`; the already-tainted guard means an agent that already holds `floor` takes the `¬ endorsed` branch — idempotent taint insert, **zero debit** (the wasted-budget fix).

- [ ] **Step 2:** `make build`. Fix elaboration only (proof VCs are Task 6).

- [ ] **Step 3: Commit** — `feat(tzimtzum): invoke_complete weighted debit + no-debit-when-tainted`

### Task 4: Actions.lean — return_endorsed conformance (P2) + flat-2 debit

**Files:**
- Modify: `tzimtzum/Tzimtzum/Actions.lean` (lines ~196-212), `tzimtzum/Tzimtzum/State.lean`

- [ ] **Step 1: Add the `return_conforms` oracle field** to the immutable-background section of `St` (mirror `output_conforms`'s `AgentId → ToolId → Prop` shape, but keyed on `child parent`):

```lean
  return_conforms : AgentId → AgentId → Prop
```

- [ ] **Step 2: Fill the dead `require True`** (line 203) and swap the budget gate to flat-2 affordability:

```lean
  require s.return_conforms child prnt          -- was `require True` (P2 fix)
  require s.affordable prnt 2
```

- [ ] **Step 3: Replace the 5-way debit** with `b - 2`:

```lean
  agent_budget := fun A L =>
    (A = prnt ∧ ∀ b, s.agent_budget prnt b → L = b - 2)
    ∨ (A ≠ prnt ∧ s.agent_budget A L)
```

- [ ] **Step 4:** `make build`. Fix elaboration only.

- [ ] **Step 5: Commit** — `feat(tzimtzum): return_endorsed conformance gate + flat-2 debit`

### Task 5: Actions.lean — sentinel_credit_budget + grant_override debit

**Files:**
- Modify: `tzimtzum/Tzimtzum/Actions.lean` (sentinel ~262-266, grant_override ~273-291, action table ~310)

- [ ] **Step 1: Rename `sentinel_refresh_budget` → `sentinel_credit_budget` with a credit amount.** It saturates at capacity (full refresh = credit `budget_capacity`):

```lean
-- sentinel_credit_budget. Capability-gated granular budget credit (saturates at capacity).
kav_action sentinel_credit_budget (a : AgentId) (n : Nat) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require s.agent_cap a s.cap_credit_budget
  agent_budget := fun A L =>
    (A = a ∧ ∀ b, s.agent_budget a b → L = min budget_capacity (b + n))
    ∨ (A ≠ a ∧ s.agent_budget A L)
```

Rename the capability accessor `cap_refresh_budget` → `cap_credit_budget` in `State.lean` (the `St` field that names the catalog cap) and at its other reference sites.

- [ ] **Step 2: grant_override — flat-1 granter debit.** Replace `require ¬ s.agent_budget granter BudgetLevel.bl_exhausted` (line 278) with `require s.affordable granter 1`, and the 5-way debit (286-290) with:

```lean
  agent_budget := fun A L =>
    (A = granter ∧ ∀ b, s.agent_budget granter b → L = b - 1)
    ∨ (A ≠ granter ∧ s.agent_budget A L)
```

- [ ] **Step 3: Update the action table** (~line 310): `("sentinel_refresh_budget", Kav.close1 sentinel_refresh_budget)` → `("sentinel_credit_budget", Kav.close2 sentinel_credit_budget)`.

- [ ] **Step 4: Re-check delegate/cascade/revoke budget clauses.** `delegate` gives the grantee full budget — change `L = BudgetLevel.bl5` (Actions.lean:45) to `L = budget_capacity`. `cascade_revoke`/`revoke` drop the budget (`A ≠ target`/`A ≠ child`) — unchanged. Init (State.lean): root at `budget_capacity` — change `L = BudgetLevel.bl5` to `L = budget_capacity`.

- [ ] **Step 5:** `make build`. Fix elaboration only.

- [ ] **Step 6: Commit** — `feat(tzimtzum): sentinel_credit_budget + numeric grant_override/delegate budget`

### Task 6: Re-prove the budget VCs (linear arithmetic)

**Files:**
- Modify: `tzimtzum/Tzimtzum/Soundness/Pres{InvokeComplete,ReturnEndorsed,GrantOverride}.lean`, the renamed `PresSentinelCreditBudget.lean` (was `PresSentinelRefreshBudget.lean`), and any `Check*`/`Init*` files the rename touches.

The "resistant" VC in each of these files is `active_has_budget` (the manually-slotted one — the 5-way disjunction needed an explicit post-budget witness). With numeric budgets the witness is `b - w` (or `min cap (b+n)`), and the disjunction proofs collapse to `omega`/`scalar_tac`.

- [ ] **Step 1: invoke_complete / return_endorsed / grant_override.** In each `Pres*` file, replace the `BudgetLevel.bl5/bl4/…` case-split (`match` on the level, the `Or.inl/Or.inr` ladder) with: obtain the current budget `b` via `active_has_budget` + `budget_unique`, supply witness `b - w` (w = `declass_weight floor` / `2` / `1`), and discharge `≤`/uniqueness goals with `omega`/`scalar_tac`. The `affordable` precondition gives `w ≤ b`, so `b - w` is exact.

- [ ] **Step 2: `budget_bounded` preservation.** New VC across ALL 13 actions. For the 4 budget-mutating actions: debit `b - w ≤ b ≤ capacity` (`omega` from `budget_bounded s`); credit `min capacity (b+n) ≤ capacity` (`Nat.min_le_left`); delegate/init `budget_capacity ≤ budget_capacity` (`rfl`/`le_refl`). For the other 9 (frame): `agent_budget` unchanged ⇒ reuse `budget_bounded s`. Add it to each action's discharge cascade; most close by `grind`/`simp_all` once the post-budget shape is exposed.

- [ ] **Step 3:** `make verify` from `tzimtzum/` (full clean re-check of all VCs). Expect green: 13 actions × (10 safeties + 16 strengthening invariants) + init.

- [ ] **Step 4: Axiom audit.** `#print axioms` on the bundled `kav_sound` (or the per-action checks) — must stay `propext`/`Classical.choice`/`Quot.sound` only, NO solver. Any new axiom is a bug; investigate before proceeding.

- [ ] **Step 5: Commit** — `feat(tzimtzum): kav_sound over numeric budget (Campaign B)`

**Stage 1 exit:** `make verify` green, axiom-clean (three standard axioms, no solver), 13 actions / 10 safeties / 16 strengthening invariants.

---

## Stage 2 — Rust kernel (argus/crates/argus-kernel)

Each task ends with `cargo test -p argus-kernel` green. TDD: failing test first where a behavior changes.

### Task 7: types.rs — delete BudgetLevel, add declass_weight

**Files:**
- Modify: `argus/crates/argus-kernel/src/types.rs`

- [x] **Step 1: Write the failing test** (replace the `budget_level_*` tests at the bottom of `types.rs`):

```rust
#[test]
fn declass_weight_by_level() {
    assert_eq!(declass_weight(ConfLevel::Public), 0);
    assert_eq!(declass_weight(ConfLevel::Internal), 1);
    assert_eq!(declass_weight(ConfLevel::Sensitive), 2);
    assert_eq!(declass_weight(ConfLevel::Restricted), 4);
}
```

- [x] **Step 2: Run it** — `cargo test -p argus-kernel declass_weight` → FAIL (`declass_weight` undefined).

- [x] **Step 3: Delete `enum BudgetLevel` + its `impl`** (lines ~138-169) and add the free function + capacity constant:

```rust
/// Protocol declassification budget capacity (fixed; not operator-configurable).
pub const BUDGET_CAPACITY: u8 = 16;

/// Sensitivity-weighted declassification cost: Public flows are free, Restricted is dearest.
pub fn declass_weight(level: ConfLevel) -> u8 {
    match level {
        ConfLevel::Public => 0,
        ConfLevel::Internal => 1,
        ConfLevel::Sensitive => 2,
        ConfLevel::Restricted => 4,
    }
}
```

- [x] **Step 4: Run** — `cargo test -p argus-kernel declass_weight` → PASS (other modules still break; fixed next tasks).

- [x] **Step 5: Commit** — `feat(argus): declass_weight + BUDGET_CAPACITY, drop BudgetLevel`

### Task 8: state.rs — numeric budget field + helpers

**Files:**
- Modify: `argus/crates/argus-kernel/src/state.rs`

- [x] **Step 1: Swap the field + import.** `use crate::types::{… , BudgetLevel, …}` drops `BudgetLevel`; the field becomes:

```rust
    /// Per-agent declassification budget (TzimtzumV2 `agent_budget`). Absence == capacity
    /// (`BUDGET_CAPACITY`): a fresh or budget-credited agent has no entry. Debited by the
    /// sensitivity weight on each endorsement; an unaffordable debit forces the fail-closed
    /// full-taint / refusal path. Reset to capacity by `clear_agent_state`.
    pub agent_budget: VecMap<AgentId, u8>,
```

- [x] **Step 2: Replace the budget helpers** (`budget`, `budget_exhausted`, `debit_budget`) with the numeric set:

```rust
    /// Current declassification budget for `agent` (absence == capacity).
    pub fn budget(&self, agent: &AgentId) -> u8 {
        match self.agent_budget.get(agent) {
            Some(b) => *b,
            None => BUDGET_CAPACITY,
        }
    }

    /// True if `agent` can pay a debit of weight `w`.
    pub fn affordable(&self, agent: &AgentId, w: u8) -> bool {
        self.budget(agent) >= w
    }

    /// Debit `agent`'s budget by weight `w` (saturating at 0). Materialises the entry.
    pub fn debit_budget(&mut self, agent: &AgentId, w: u8) {
        let next = self.budget(agent).saturating_sub(w);
        self.agent_budget.insert(agent.clone(), next);
    }

    /// Credit `agent`'s budget by `n` (saturating at capacity). Materialises the entry.
    pub fn credit_budget(&mut self, agent: &AgentId, n: u8) {
        let next = self.budget(agent).saturating_add(n).min(BUDGET_CAPACITY);
        self.agent_budget.insert(agent.clone(), next);
    }
```

Add `BUDGET_CAPACITY` to the `use crate::types::{…}` import. Note `debit_budget` now takes a weight argument (callers updated in Task 10).

- [x] **Step 3:** `cargo build -p argus-kernel` — only `transitions.rs` should still reference the old API. Commit — `feat(argus): numeric agent_budget + affordable/credit helpers`

### Task 9: capability.rs + error.rs + traits.rs — credit cap, NotConforming, return_conforms

**Files:**
- Modify: `argus/crates/argus-kernel/src/capability.rs`, `src/error.rs`, `src/traits.rs`

- [x] **Step 1: Rename the cap** `RefreshBudget` → `CreditBudget` in the `CapKind` enum, `ALL` array, `as_str` (`"refresh_budget"` → `"credit_budget"`), and `from_catalog_name`. Keep the 18-variant count. The roundtrip test still passes.

- [x] **Step 2: Add the error variant** to `KernelError`:

```rust
    /// A cross-boundary endorsed return failed the runtime conformance oracle.
    NotConforming,
```

- [x] **Step 3: Add the conformance method** to `ConformanceOracle` (a distinct verdict from `conforms`, which is tool-keyed; this one is child→parent):

```rust
    /// Did the endorsed cross-boundary return from `child` to `parent` conform to the
    /// declared contract? `return_endorsed` requires this (P2: closes the content-blind gap).
    fn return_conforms(
        &self,
        child: &AgentId,
        parent: &AgentId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool;
}
```

(Add `BackgroundTheory` import to `traits.rs` if not already present — it is.)

- [x] **Step 4:** `cargo build -p argus-kernel` (kernel.rs test oracles + transitions still need updates; expected). Commit — `feat(argus): credit_budget cap, NotConforming, return_conforms oracle`

### Task 10: transitions.rs — wire the four actions

**Files:**
- Modify: `argus/crates/argus-kernel/src/transitions.rs`

- [x] **Step 1: invoke_complete** (lines ~417-431). The endorsed predicate gains affordability (weighted) and the already-tainted guard; the debit is weighted:

```rust
        if let Some((conf_floor, output_bounded)) = meta_info {
            let weight = declass_weight(conf_floor);
            let already_tainted = st.taint_levels.set_contains(&agent, &conf_floor);
            // Zero-taint (endorsed) path: bounded + conforms + affordable AND the agent does not
            // already hold this floor (re-tainting buys nothing, so don't waste budget on it).
            let zero_taint = output_bounded
                && conformance.conforms(&agent, &tool_id, &st, bg)
                && st.affordable(&agent, weight)
                && !already_tainted;
            if zero_taint {
                st.debit_budget(&agent, weight);
            } else {
                st.taint_levels.insert_into(agent.clone(), conf_floor);
                st.gh_taint_invoked.insert_into(agent.clone(), conf_floor);
            }
        }
```

(Verify `set_contains` is the right owned VecMap-of-VecSet membership accessor — same one used in check 2b; match the existing call sites.)

- [x] **Step 2: return_endorsed** (lines ~437-468). Thread the conformance oracle in, gate on `return_conforms`, swap exhaustion for affordability (weight 2):

```rust
pub fn return_endorsed<F: ConformanceOracle>(
    mut st: KernelState,
    bg: &BackgroundTheory,
    conformance: &F,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    // ... existing parent/active/in-flight/cap checks unchanged ...
    if !conformance.return_conforms(&child, &parent, &st, bg) {
        return Err(KernelError::NotConforming);
    }
    if !st.affordable(&parent, 2) {
        return Err(KernelError::BudgetExhausted);
    }
    st.debit_budget(&parent, 2);
    Ok((st, KernelAction::ReturnEndorsed { child, parent }))
}
```

(Rename the `_bg` param to `bg`; the cap check stays `CapKind::Declassify`.)

- [x] **Step 3: sentinel_credit_budget** (replaces `sentinel_refresh_budget`, lines ~585-600):

```rust
/// Capability-gated granular budget credit (saturates at capacity). Full refresh =
/// credit `BUDGET_CAPACITY`. The rare, logged exception that keeps a long-running orchestrator
/// from dead-ending on an exhausted budget.
pub fn sentinel_credit_budget(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    agent: AgentId,
    amount: u8,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_cap.set_contains(&agent, &CapKind::CreditBudget) {
        return Err(KernelError::CapabilityMissing);
    }
    st.credit_budget(&agent, amount);
    Ok((st, KernelAction::SentinelCreditBudget { agent, amount }))
}
```

- [x] **Step 4: grant_override** (lines ~624-639). Swap exhaustion for affordability and debit weight 1:

```rust
    if !st.affordable(&granter, 1) {
        return Err(KernelError::BudgetExhausted);
    }
    // ... re-arm guard + flow_override insert + override_used remove unchanged ...
    st.debit_budget(&granter, 1);
```

- [x] **Step 5: `clear_agent_state`** (line ~61) — `st.agent_budget.remove(agent)` is unchanged (absence == capacity == "reset to full"). Verify it stays.

- [x] **Step 6: Migrate the in-module budget tests** (the `BudgetLevel::Lx` assertions, ~lines 1154-2031). Replace expected `BudgetLevel::L4` with numeric: e.g. `invoke_complete` on a Sensitive-floor tool now debits `2`, so `st.budget(a1) == BUDGET_CAPACITY - 2`; `return_endorsed` debits `2`; `grant_override` debits `1`; the exhaustion test sets the budget low (`insert(g, 1)` then a weight-2 debit refuses). Add:

```rust
#[test]
fn invoke_complete_already_tainted_does_not_debit() {
    // Pre-taint the agent at the tool's conf_floor; the endorsed path is skipped, no debit.
    // ... arrange a bounded+conforming Sensitive tool, pre-insert Sensitive taint ...
    // assert budget unchanged AND taint still present (idempotent), no debit.
}

#[test]
fn return_endorsed_non_conforming_refuses() {
    // ConformanceOracle::return_conforms == false ⇒ Err(NotConforming), no debit.
}
```

- [x] **Step 7: Run** — `cargo test -p argus-kernel` (unit). Fix until green.

- [x] **Step 8: Commit** — `feat(argus): weighted/credit/conformance budget across 4 transitions`

### Task 11: event.rs + kernel.rs — action variant + driver

**Files:**
- Modify: `argus/crates/argus-kernel/src/event.rs`, `src/kernel.rs`

- [x] **Step 1: event.rs** — rename the action variant:

```rust
    SentinelCreditBudget {
        agent: AgentId,
        amount: u8,
    },
```

Update the `kernel_action_variant_count` test constructor (still 13).

- [x] **Step 2: kernel.rs driver** — three signature changes:
  - `return_endorsed` passes the conformance oracle: `transitions::return_endorsed(self.state.clone(), &self.background, &self.conformance, child, parent)`.
  - `sentinel_refresh_budget(agent)` → `sentinel_credit_budget(&mut self, agent: AgentId, amount: u8)` delegating to `transitions::sentinel_credit_budget(…, agent, amount)`.
  - the `full_lifecycle` test's `return_endorsed` call is unchanged (driver arity is the same; `ConformsAll` already implements the trait — see Step 3).

- [x] **Step 3: test oracles** — `ConformsAll` in kernel.rs (and any other `ConformanceOracle` impl in the crate/tests) gains `return_conforms` returning `true`.

- [x] **Step 4: Run** — `cargo test -p argus-kernel`. Green. Commit — `feat(argus): SentinelCreditBudget action + conformance-threaded driver`

### Task 12: safety_properties.rs — integration suite

**Files:**
- Modify: `argus/crates/argus-kernel/tests/safety_properties.rs`

- [x] **Step 1:** Update any `BudgetLevel` / `sentinel_refresh_budget` references to the numeric API + `sentinel_credit_budget(agent, amount)`. Add a property covering the new behaviors: an agent at budget `0` cannot endorse (`invoke_complete` falls to full taint; `return_endorsed`/`grant_override` refuse), and `sentinel_credit_budget` saturates at `BUDGET_CAPACITY`.

- [x] **Step 2: Run** — `cargo test -p argus-kernel --test safety_properties` → green. Then full `cargo test` + `cargo clippy --workspace`.

- [x] **Step 3: Commit** — `test(argus): numeric budget + conformance safety properties`

**Stage 2 exit:** `cargo test` (all unit + safety) green, `cargo clippy --workspace` clean, no `BudgetLevel` symbol remains in argus-kernel.

---

## Stage 3 — Extraction + refinement (argus/formal-lean)

Proof work: statements below are exact; proof bodies are iterative. Reuse the established machinery (memory: `c2-invoke-complete`, `c2-return-endorsed-and-unendorsed-foundation`, `refinement-layer1-unified-r`, `refinement-layer2-soundness`, `wp-loop-proof-gotchas`). Exit gate is binary: `lake build` green + axiom audit.

### Task 13: Re-extract

- [x] **Step 1:** From `argus/`: run `scripts/charon-aeneas-extract.sh` → fresh `argus_kernel.llbc` + regenerated `formal-lean/ArgusLean/Generated/ArgusKernel.lean`.
- [x] **Step 2:** `lake build ArgusLean.Generated.ArgusKernel` from `argus/formal-lean/`. `u8` arithmetic (`saturating_sub`/`saturating_add`/`min`) is modeled by Aeneas as `UScalar` ops — must elaborate. If it fails, the Rust idiom is wrong (e.g. a non-saturating op or a `usize` leak); fix the Rust, do not patch the generated file.
- [x] **Step 3:** Commit — `chore(formal-lean): re-extract for numeric budget`

### Task 14: Budget bridging specs

**Files:**
- Modify: `ArgusLean/Refinement/Bridging/*` (the file holding the old `debitBudget_spec` — likely `Budget*.lean` or inline in a `StateRelation`/collection bridging file; grep `debitBudget_spec`)

- [x] **Step 1:** Replace `debitBudget_spec` (was: enum step-down) with the numeric pair: `debitBudget_spec` (concrete `saturating_sub w` relates to abstract `b - w` under `affordable`) and a new `creditBudget_spec` (concrete `saturating_add n |> min CAP` relates to abstract `min budget_capacity (b + n)`). Both discharge by `scalar_tac`/`omega` over `UScalar` ↔ `Nat` once the absence==capacity convention is bridged (reuse the existing `budget` get-style accessor spec; `budget_capacity = 16` is a literal on both sides).
- [x] **Step 2:** `affordable` bridge: concrete `budget(a) >= w` ↔ abstract `∃ b, agent_budget a b ∧ w ≤ b` (existence from `active_has_budget`, value from the get-spec).
- [x] **Step 3:** `lake build` the Bridging tree green. Commit — `feat(formal-lean): numeric budget bridging specs`

### Task 15: Preservation proofs for the four budget actions

**Files:**
- Modify: `ArgusLean/Refinement/Unified/Preservation/{InvokeComplete,ReturnEndorsed,GrantOverride}.lean`; rename `SentinelRefreshBudget.lean` → `SentinelCreditBudget.lean`
- Modify: `Unified/Relation.lean` (re-type the budget clause of `R`: `agent_budget` relation now `… → Nat → Prop`; the get-clause uses `budget`/`u8`↔`Nat`)

- [x] **Step 1: Relation re-type.** In `R` (`Relation.lean`), the budget-relating clause changes element type `BudgetLevel` → `Nat`/`u8`; the absence==capacity convention is already there (reuse it, just swap the "full" constant from `bl5` to `budget_capacity`/`16`). DONE: clause is `(budgetReadC st.agent_budget G).val = L`; field name `cap_refresh` kept (body now `a.cap_credit_budget = CapKind.CreditBudget`); new `RcAgree` oracle-agreement predicate added (mirrors `CfAgree`).
- [x] **Step 2: invoke_complete.** The endorsed branch sim now: weighted `debitBudget_spec`, plus the new `already_tainted` guard — `set_contains(taint, floor)` bridges to abstract `taint_levels a floor` (reuse the existing taint membership spec used by `return_unendorsed`/sentinel). The branch structure is unchanged; only the debit witness and the extra guard conjunct are new.
- [x] **Step 3: return_endorsed.** Add the `return_conforms` oracle hyp (a `ReturnConforms`-relating hypothesis, copy the shape of the `output_conforms`/`OracleFidelity` hyp threading); flat-2 `debitBudget_spec`; `NotConforming` error arm maps cleanly (refines a spec `require`). DONE: `return_endorsed_preservesR` takes `rcOf`/`hrc`/`hrcA`; Task 16 must supply them from the bundle's `RcAgree`.
- [x] **Step 4: grant_override.** Flat-1 `debitBudget_spec`; otherwise the Campaign A sim is intact.
- [x] **Step 5: sentinel_credit_budget.** `creditBudget_spec`; the action gained the `amount`/`n` param — the inversion (`cases` on `hok`) carries it. Reuse the old refresh sim skeleton. DONE: `SentinelRefreshBudget.lean` → `SentinelCreditBudget.lean`.
- [x] **Step 6: `budget_bounded` in `R` / `_inv_full`.** Where the relation or the WF invariant carries budget bounds, add the `≤ budget_capacity` conjunct; discharged by the spec-side `budget_bounded` (now proven in Stage 1) + the bridging value equality. DONE: no extra R conjunct needed — saturating ops keep the concrete cell ≤ 16, abstract `budget_bounded` covers the abstract side.
- [x] **Step 7:** `lake build` after each action; known gotchas that WILL recur: tuple-bind `let (a,b)` needs full `simp at hok`; `subst` on a param-equation — use `rw`; inverse-hyp pairs loop `scalar_tac` (compute arith first, then `clear`); `Ne` not rewritable. Commit per action. DONE: all 13 Preservation modules + helpers build green (1715 jobs).

### Task 16: Bundle + soundness reassembly

**Files:**
- Modify: `ArgusLean/Refinement/Unified/{Bundle,Soundness}.lean`, `InitRefinement.lean`, and the Preservation aggregator/import for the renamed file

- [x] **Step 1:** Fix the `SentinelRefreshBudget` → `SentinelCreditBudget` import/arm in `Bundle.lean`; the 13-arm `_preservesR` + `step_refines` bundle is otherwise structurally identical. DONE: also added the `rcOfAgree`/`_ok`/`_iff` trio + `hRc : RcAgree` threaded into `step_refines`'s `return_endorsed` arm; `ReturnEndorsed` now threads the conformance oracle.
- [x] **Step 2:** `InitRefinement`: root's concrete initial budget is absent (== capacity); abstract `initial` now demands `agent_budget root budget_capacity` — same get-spec the old `bl5` clause used, swapping the constant. DONE: `absInitial` gains `rcRel`, sets `cap_credit_budget := CreditBudget`; budget clause via `budgetCapacity_val`.
- [x] **Step 3:** Reassemble `implementation_sound` against the 13-action Kav system (`kav_soundP` sort-polymorphic; tzimtzum exports the 13-action `kav_sound` from Stage 1, now with the 16th invariant — confirm `Soundness.lean`'s invariant projection lines up with the new `budget_bounded` entry). DONE: `OracleFidelity` gained a 4th `return_conforms` clause (folded in — same `ConformanceOracle` trait, no new honest assumption); conclusion is the 26-conjunct `allInv` bundle (10 safeties + 16 strengthening incl. `budget_bounded`).
- [x] **Step 4:** Full `lake build` from `argus/formal-lean/` — green. Axiom audit on `implementation_sound`: same baseline set (standard three + Aeneas/Charon residuals + `CapacityOK`/`OracleFidelity` + `AgentId.root`/`sorryAx`-baseline where root is named). Any NEW axiom needs explicit justification in the commit message. DONE: 2467 jobs green; axiom set unchanged from Campaign-A baseline (no solver, no new axiom), independently reviewed.
- [x] **Step 5:** Commit — `feat(formal-lean): implementation_sound over numeric budget`

**Stage 3 exit:** formal-lean builds green, `implementation_sound` proven, axiom set documented and unchanged from the Campaign A baseline.

---

## Stage 4 — ex_argus surface (after Stages 1-3)

### Task 17: Mirror types + state_version bump

**Files:**
- Modify: `ex_argus/lib/ex_argus.ex` (`@state_version 2` → `3`)
- Modify: `ex_argus/lib/ex_argus/kernel/{state,types}.ex`
- Modify: `ex_argus/native/argus_nif/src/enums.rs`, `src/state.rs`

- [ ] **Step 1: `types.ex`** — delete the `budget_level` typedoc/type (`:exhausted | :l1 | …`); `agent_budget` values become `non_neg_integer()`. Rename the `:refresh_budget` cap atom to `:credit_budget` in the `cap_kind` union. Add a `not_conforming` error atom wherever the error atom union lives.
- [ ] **Step 2: `state.ex`** — `agent_budget: %{optional(Types.agent_id()) => non_neg_integer()}` (was `Types.budget_level()`). Update the moduledoc.
- [ ] **Step 3: `native/argus_nif/src/enums.rs`** — delete `BudgetLevelN` + its `into_kernel`/`from_kernel`/roundtrip test; rename the `RefreshBudget` cap atom variant → `CreditBudget` (atom `:credit_budget`).
- [ ] **Step 4: `native/argus_nif/src/state.rs`** — `agent_budget: HashMap<String, u8>` (drop `BudgetLevelN`); `into_kernel`/`from_kernel` map `u8` directly (no enum conversion). Update the round-trip unit test (`L3` → a numeric like `13`).
- [ ] **Step 5: `lib/ex_argus.ex`** — bump `@state_version 2` → `3`.
- [ ] **Step 6:** `cargo build` (in `native/argus_nif`) + `mix compile` (in `ex_argus`). Commit — `feat(ex_argus): numeric budget mirror + state_version 3`

### Task 18: return_conforms verdict + credit/conformance NIFs

**Files:**
- Modify: `ex_argus/native/argus_nif/src/{nifs,instance,event}.rs`, `ex_argus/lib/ex_argus/{native,offline,instance,replay}.ex`

- [ ] **Step 1: `event.rs`** — `ActionN::from_kernel`: rename the `SentinelRefreshBudget` arm → `SentinelCreditBudget` (atom `:sentinel_credit_budget`, fields `agent`, `amount`); `ErrorN` gains `NotConforming` → `:not_conforming`.
- [ ] **Step 2: `nifs.rs` (stateless) + `instance.rs`** — `return_endorsed` gains a `return_conforms: bool` arg, passed as `&ConstConformance(return_conforms)` (the kernel's `ConstConformance(bool)` impl now also covers `return_conforms`; confirm `oracles.rs`'s `ConstConformance` implements the new trait method returning its bool). `sentinel_refresh_budget(state, bg, agent)` → `sentinel_credit_budget(state, bg, agent, amount: u8)` (and the `instance_*` variant gains `amount`).
- [ ] **Step 3: `native.ex` stubs** — update the four arities:

```elixir
  def return_endorsed(_state, _bg, _child, _parent, _return_conforms), do: :erlang.nif_error(:nif_not_loaded)
  def sentinel_credit_budget(_state, _bg, _agent, _amount), do: :erlang.nif_error(:nif_not_loaded)
  def instance_return_endorsed(_h, _child, _parent, _return_conforms), do: :erlang.nif_error(:nif_not_loaded)
  def instance_sentinel_credit_budget(_h, _agent, _amount), do: :erlang.nif_error(:nif_not_loaded)
```

- [ ] **Step 4: `offline.ex` / `instance.ex`** — update the defdelegates/wrappers: `return_endorsed/5` (extra `return_conforms` verdict, mirroring how `invoke_complete/5` threads `conformance_conforms`), `sentinel_credit_budget/4` (offline) and `/3` (instance, with `amount`). Update `@spec`s and the moduledoc action list (`sentinel_refresh_budget` → `sentinel_credit_budget`).
- [ ] **Step 5: `replay.ex` / `Instance.recover`** — the log-dispatch arms: rename `:sentinel_refresh_budget` → `:sentinel_credit_budget` (now carries `amount`), and `return_endorsed` replay must carry the `return_conforms` verdict it was decided with (record it in the log entry like the other oracle verdicts; the exhaustiveness check will point at the dispatch site).
- [ ] **Step 6:** `cargo build` + `mix compile`. Commit — `feat(ex_argus): credit_budget + return_conforms NIFs`

### Task 19: ex_argus tests

**Files:**
- Modify: `ex_argus/test/**` (budget fixtures, action tests)

- [ ] **Step 1:** Migrate budget assertions from atoms to integers. Add `Instance`/`Offline` tests: weighted debit (Sensitive endorsement costs 2), `return_endorsed` refused on `return_conforms == false` (`{:error, :not_conforming}`), `sentinel_credit_budget` saturates at 16, already-tainted endorsement does not debit, recovery replay of a log containing `sentinel_credit_budget` + an endorsed `return_endorsed` reproduces the budget.
- [ ] **Step 2:** From `ex_argus/`: `mix test` — green. Commit — `test(ex_argus): numeric budget + conformance behavior`

**Stage 4 exit:** `mix test` green; replay/recovery carries `sentinel_credit_budget` amount and the `return_conforms` verdict.

---

## Stage 5 — Exit criteria + docs (merge gate)

### Task 20: Full-stack verification + docs

- [ ] **Step 1: All layers green, in order:**
  - `tzimtzum/`: `make verify` (13 actions / 10 safeties / 16 strengthening invariants, axiom-clean)
  - `argus/`: `cargo test` + `cargo clippy --workspace`
  - `argus/formal-lean/`: `lake build` + `implementation_sound` axiom audit
  - `ex_argus/`: `mix test`
- [ ] **Step 2: Grep for stragglers** — no `BudgetLevel`, `bl_exhausted`, `bl5`, `refresh_budget`, `sentinel_refresh_budget`, or `require True` remains anywhere (`rg` across `tzimtzum/`, `argus/`, `ex_argus/`). The `require True` at the old `Actions.lean:200` must be gone (P2 closed).
- [ ] **Step 3: Update `CLAUDE.md`** (root + `argus/`): budget is now a numeric meter; cap is `credit_budget`; action is `sentinel_credit_budget`; `return_endorsed` is conformance-gated; "15 strengthening invariants" → 16. Update the test counts if they changed.
- [ ] **Step 4: Update Obsidian** — flip the design doc's Mechanism 5 / Phase 3 status to IMPLEMENTED with the merge commit; add a `campaign-b-implemented` memory file + MEMORY.md pointer; mark eval P2 as RESOLVED.
- [ ] **Step 5:** Open the PR / finish the branch (use `superpowers:finishing-a-development-branch`).

**Campaign B exit (merge gate):** every layer green and axiom-clean; no budget-enum or `require True` straggler; P2 closed; docs + memory updated.

---

## Self-review notes

- **Spec coverage:** Mechanism 5's five bullets map to Tasks 1-6 (spec) / 7-12 (kernel); P2 ride-along to Tasks 4 (spec) / 9-10 (kernel) / 18 (ex_argus). `budget_bounded` (new invariant) is Task 2/6/15. `sentinel_credit_budget` rename threads Tasks 5/11/16/18.
- **No-debit-when-already-tainted** is in both the spec endorsed guard (Task 3) and the Rust `already_tainted` check (Task 10) — keep them identical or the refinement (Task 15 Step 2) breaks.
- **Type consistency:** `debit_budget` is `(agent, w: u8)` everywhere (Task 8 defines, Task 10 calls); `affordable(agent, w)`; `credit_budget(agent, n)`; spec `St.affordable s a w`; cap is `CreditBudget`/`:credit_budget`/`cap_credit_budget`; action is `SentinelCreditBudget { agent, amount }` / `sentinel_credit_budget`.
- **Deferred (not in this plan, per design):** max-of-child-taint weighting for `return_endorsed` (flat-2 here); `reincarnate`; behavior-earned budget (rejected). Eval P3 (state growth GC) and P4 vestigial-types cleanup are separate follow-ups.
