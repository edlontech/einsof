# Campaign A — Ceiling Flow Policy + grant_override Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the flow-mode matrix with two per-egress confidentiality ceilings (incoherence unrepresentable) and add a 13th protocol action `grant_override` that arms/re-arms single-use flow overrides in-band, across all four layers: Kav spec, Rust kernel, Aeneas refinement, ex_argus/argus-explain.

**Architecture:** The Kav spec swaps the `flow_allows`/`flow_inspects` relation fields for `egress_allow_ceiling`/`egress_inspect_ceiling : EgressKind → Option ConfLevel` and re-derives the old names as `St`-namespace defs, so all 13 inline gate sites and 5 flow invariants stay textually identical. `flow_override` becomes mutable state (populated exclusively by the new `grant_override` action; cleared on agent death). The Rust kernel keeps `flow_mode(level, egress) -> FlowMode` as a computed function over two `VecMap<EgressKind, ConfLevel>` ceilings, so `flow_decision`/`gate_egress`/gated transitions are untouched downstream; `flow_override` moves from `BackgroundTheory` to `KernelState`. The refinement is re-extracted and rebuilt to `implementation_sound` against the 13-action system.

**Tech Stack:** Lean 4 (Kav framework, mathlib-free), Rust edition 2024 (zero-dep argus-kernel, Aeneas-extractable idioms), Aeneas/Charon, Elixir + Rustler.

**Design doc:** Obsidian `argus_and_tzimtzum/designs/2026-06-12-campaign-a-ceilings-grant-override-design.md`. All decisions there are locked and user-approved; do not relitigate them.

**Sequencing rule (locked):** Stage exits green before the next starts. Spec → kernel → extraction/refinement → bindings. The whole campaign merges only when ALL exit criteria (Stage 5) pass.

**Branch:** create `feat/campaign-a-ceilings` from `main` before Task 1.

---

## Hard constraints (read before any task)

- **Aeneas-extractable Rust only** in argus-kernel: Vec-backed `VecMap`/`VecSet`, explicit index `while` loops, no closures in loops, no early `return` inside loops (early return in straight-line code is fine), owned accessors (`get_cloned`/`set_contains`/`get_set_or_empty`) when the index is computed. Mirror the idioms already in `transitions.rs`.
- **Kav naming:** never name an action param `par`. `autoImplicit` stays enabled. Capital binders in invariants carry explicit type annotations.
- **No new safety/invariant statements change.** The 25 invariants in `Invariants.lean` stay textually identical (they reference `s.flow_allows`/`s.flow_inspects`, which become dot-notation defs).
- After any Lean toolchain change: `lake exe cache get` from `tzimtzum/` before `make build`.
- Commit style: simple one-line messages, no co-author trailers, no trailing whitespace.

---

## Stage 1 — Kav spec (tzimtzum/ + kav/)

### Task 1: `Kav.close4`

`grant_override` has 4 params; `Kav` only has `close1`..`close3`.

**Files:**
- Modify: `kav/Kav/Transition.lean` (after `close3`, line ~22)

- [ ] **Step 1: Add close4**

```lean
def close4 {σ α β γ δ : Type} (f : α → β → γ → δ → Action σ) : Action σ :=
  { guard := fun s => ∃ a b c d, (f a b c d).guard s
    next  := fun s s' => ∃ a b c d, (f a b c d).guard s ∧ (f a b c d).next s s' }
```

- [ ] **Step 2: Build kav**

Run from `kav/`: `lake build`
Expected: green (pure addition).

- [ ] **Step 3: Commit** — `feat(kav): add close4 for 4-param actions`

### Task 2: State.lean — ceilings, derived defs, mutable flow_override, cap_grant_override

**Files:**
- Modify: `tzimtzum/Tzimtzum/State.lean`

- [ ] **Step 1: Swap the flow fields in `St`**

In the `St` structure (`State.lean:74`):
1. In the **mutable** section (after `override_used`, line 86), add:

```lean
  flow_override       : AgentId → ToolId → ConfLevel → Prop
```

2. In the **immutable background** section, DELETE the three lines (96–98):

```lean
  flow_allows         : ConfLevel → EgressKind → Prop
  flow_inspects       : ConfLevel → EgressKind → Prop
  flow_override       : AgentId → ToolId → ConfLevel → Prop
```

and in their place add the ceiling functions:

```lean
  egress_allow_ceiling   : EgressKind → Option ConfLevel
  egress_inspect_ceiling : EgressKind → Option ConfLevel
```

3. In the **named individuals** section (after `cap_refresh_budget`, line 105), add:

```lean
  cap_grant_override  : CapKind
```

- [ ] **Step 2: Add the derived defs with the old names**

After the `variable` line (line 107), add. They MUST live in the `St` namespace so every existing `s.flow_allows L E` use site resolves via dot notation unchanged:

```lean
/-- Derived flow-ALLOW relation: a level flows freely iff it is at or below the egress's
allow ceiling. `none` = no level passes (strict default-deny, including Public). -/
def St.flow_allows
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : ConfLevel) (e : EgressKind) : Prop :=
  ∃ c, s.egress_allow_ceiling e = some c ∧ le_conf l c

/-- Derived flow-INSPECT relation: content-gated band, levels at or below the inspect
ceiling. An inspect ceiling below the allow ceiling is an empty inspect band — coherent. -/
def St.flow_inspects
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (l : ConfLevel) (e : EgressKind) : Prop :=
  ∃ c, s.egress_inspect_ceiling e = some c ∧ le_conf l c
```

- [ ] **Step 3: Constrain `flow_override` in `initial`**

`initial` (line 118) gains a final conjunct (after the `override_used` line):

```lean
  ∧ (∀ (A : AgentId) (T : ToolId) (L : ConfLevel), ¬ s.flow_override A T L)
```

- [ ] **Step 4: Build** — from `tzimtzum/`: `make build`. State.lean itself must elaborate; downstream files will fail until Tasks 3–5 land (that is expected mid-stage; build the single file via `lake build Tzimtzum.State` if you want a clean signal).

### Task 3: Discharge-cascade visibility of the derived defs

`flow_allows`/`flow_inspects` were opaque relation fields with frame equations; now they are defs over `egress_allow_ceiling`/`egress_inspect_ceiling`. The provers must be able to unfold them so the (framed) ceiling fields become visible.

**Files:**
- Modify: `tzimtzum/Tzimtzum/Soundness/Common.lean` (the `kav_discharge` macro simp list, ~line 70)
- Inspect/modify: `kav/Kav/CheckAction.lean` (the `#kav_check_action` cascade's simp set)

- [ ] **Step 1:** In `kav_discharge`'s `simp only [...]` list (Common.lean), add `St.flow_allows, St.flow_inspects` right after the invariant names.
- [ ] **Step 2:** Open `kav/Kav/CheckAction.lean` and find its discharge simp set. If it unfolds invariant/action defs by name from the caller's list, nothing to do (the Check files pass `invs`/the action, and `grind` can unfold marked defs). If checks in Task 5 fail with goals stuck on `St.flow_allows`, add `attribute [simp] St.flow_allows St.flow_inspects` in `State.lean` instead — that makes both cascades see through them everywhere. Prefer the attribute route only if needed; record which route was taken in the commit message.

### Task 4: Actions.lean — clearing clauses, grant_override, 13-action system

**Files:**
- Modify: `tzimtzum/Tzimtzum/Actions.lean`

- [ ] **Step 1: Clear dead/fresh agents' overrides**

`flow_override` is now mutable, so `delegate` / `revoke` / `cascade_revoke` must clear it (same shape as their `override_used` clauses). Add one line to each:

To `delegate` (after line 50): `flow_override := fun A T L => s.flow_override A T L ∧ A ≠ grantee`
To `revoke` (after line 77): `flow_override := fun A T L => s.flow_override A T L ∧ A ≠ target`
To `cascade_revoke` (after line 95): `flow_override := fun A T L => s.flow_override A T L ∧ A ≠ child`

- [ ] **Step 2: Add the `grant_override` action**

After `sentinel_refresh_budget` (line 263):

```lean
-- grant_override (Campaign A, 13th action). Capability-gated, granter-budget-debited
-- arming/re-arming of a single-use flow override for (target, tool, lvl). The re-arm
-- guard (target has no in-flight invocations) makes both single-use invariants vacuous
-- for the target at grant time. Self-grant (granter = target) is legal — the guard then
-- binds the granter.
kav_action grant_override (granter target : AgentId) (tool : ToolId) (lvl : ConfLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active granter
  require s.agent_active target
  require s.agent_cap granter s.cap_grant_override
  require ¬ s.agent_budget granter BudgetLevel.bl_exhausted
  require ∀ (I : InvocationId), ¬ s.in_flight target I
  flow_override := fun A T L =>
    s.flow_override A T L ∨ (A = target ∧ T = tool ∧ L = lvl)
  override_used := fun A T L =>
    s.override_used A T L ∧ ¬ (A = target ∧ T = tool ∧ L = lvl)
  agent_budget := fun A L =>
    (A = granter
      ∧ ( (s.agent_budget granter BudgetLevel.bl5 ∧ L = BudgetLevel.bl4)
       ∨ (s.agent_budget granter BudgetLevel.bl4 ∧ L = BudgetLevel.bl3)
       ∨ (s.agent_budget granter BudgetLevel.bl3 ∧ L = BudgetLevel.bl2)
       ∨ (s.agent_budget granter BudgetLevel.bl2 ∧ L = BudgetLevel.bl1)
       ∨ (s.agent_budget granter BudgetLevel.bl1 ∧ L = BudgetLevel.bl_exhausted) ))
    ∨ (A ≠ granter ∧ s.agent_budget A L)
```

- [ ] **Step 3: Extend `system` to 13 actions**

In the `system` def (line 267), append to the list:

```lean
      , ("grant_override",         Kav.close4 grant_override)
```

- [ ] **Step 4: Build** — `lake build Tzimtzum.Actions` from `tzimtzum/`. Expected: elaborates clean.
- [ ] **Step 5: Commit** — `feat(tzimtzum): ceiling flow fields + grant_override action`

### Task 5: VC re-check (all 13 actions × 25 invariants + init)

**Files:**
- Create: `tzimtzum/Tzimtzum/CheckGrantOverride.lean`
- Modify: `tzimtzum/Tzimtzum.lean` (aggregator imports), `tzimtzum/Tzimtzum/Audit.lean`

- [ ] **Step 1: Write CheckGrantOverride.lean** (copy the `CheckSentinelRefreshBudget.lean` pattern):

```lean
import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def grantOverride : KAgent → KAgent → KTool → ConfLevel → Kav.Action KSt :=
  grant_override
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action grantOverride invs

end Tzimtzum
```

- [ ] **Step 2:** Add `import Tzimtzum.CheckGrantOverride` to the aggregator (`Tzimtzum.lean`) and mirror whatever the other Check modules do in `Audit.lean`.
- [ ] **Step 3: Full re-check** — from `tzimtzum/`: `make build`. ALL Check files re-verify (the three revocation actions changed; every action's VCs re-run against the now-derived flow defs).
  - Expected failures to iterate on: VCs stuck on folded `St.flow_allows` (→ Task 3 fallback), and the two single-use invariants on `grant_override`. For the latter the proof argument is: the re-arm guard `∀ I, ¬ in_flight target I` makes both `override_consumed_when_sole_justification` and `in_flight_override_consumed` vacuous for `target`; for agents ≠ target nothing changed.
  - **Contingency (from the design, use only if the inductive check demands it):** add strengthening invariant `flow_override_active`: `∀ A T L, s.flow_override A T L → s.agent_active A` to `Invariants.lean` + `allInvariants` + the `allInv` bundle + the `kav_discharge` refine tuple (25 → 26 `?_`). This is pre-approved in the design — don't ask, just record it in the commit.
  - Discharge cascade order is `trivial | grind | (simp_all <;> grind) | auto | duper` — keep invariant batches small if elaboration chokes (established C0 technique).
- [ ] **Step 4: Commit** — `test(tzimtzum): grant_override VC check + full 13-action re-check`

### Task 6: Soundness bundle (`kav_sound` over 13 actions)

**Files:**
- Create: `tzimtzum/Tzimtzum/Soundness/PresGrantOverride.lean`
- Modify: `tzimtzum/Tzimtzum/Soundness/Common.lean` (`ksystem` picks up the new `system` automatically — verify), `tzimtzum/Tzimtzum/Soundness/Bundle.lean` (consume the new module), `tzimtzum/Tzimtzum/Soundness/PresMost.lean` (only if the revocation actions' cascade now needs the flow defs — Task 3 covers it)

- [ ] **Step 1:** `grant_override` is a budget action (5-way debit shape) — the C0 record says budget actions need **manual VC slotting**, exactly like `return_endorsed`. Copy `PresReturnEndorsed.lean` to `PresGrantOverride.lean`, substitute the action (`Kav.close4 grant_override`, four intro'd params) and re-slot the budget VCs (`budget_unique`, `active_has_budget`) the same way.
- [ ] **Step 2:** Wire the new preservation lemma into `Bundle.lean`'s `reachable_sound` assembly (13th case).
- [ ] **Step 3:** From `tzimtzum/`: `make verify` (clean rebuild). Then confirm the axiom audit: `Soundness.lean`'s `#print axioms Tzimtzum.kav_sound` output must show only `propext` / `Classical.choice` / `Quot.sound`.
- [ ] **Step 4: Commit** — `feat(tzimtzum): kav_sound over 13 actions`

**Stage 1 exit:** `make verify` green, axiom-clean, 13 actions × 25(+1?) invariants.

---

## Stage 2 — Rust kernel (argus/crates/argus-kernel) + argus-explain compile migration

Note: argus-explain lives in the same workspace and consumes `bg.flow_mode` (signature unchanged — fine) and `bg.has_flow_override` + builder `set_flow`/`add_override` (break). The workspace only compiles again after Task 12, so run `cargo test -p argus-kernel` until then; full `cargo test --workspace` + clippy is the stage exit.

### Task 7: `CapKind::GrantOverride` (17 → 18)

**Files:**
- Modify: `argus/crates/argus-kernel/src/capability.rs`

- [ ] **Step 1:** Update the count test first (TDD): in `capability.rs` tests, change `assert_eq!(CapKind::ALL.len(), 17)` to `18`. Run `cargo test -p argus-kernel cap_kind` from `argus/` — expect FAIL.
- [ ] **Step 2:** Add `GrantOverride` as the last enum variant; extend `ALL` to `[CapKind; 18]` with `Self::GrantOverride`; add `Self::GrantOverride => "grant_override"` to `as_str` and `"grant_override" => Some(Self::GrantOverride)` to `from_catalog_name`.
- [ ] **Step 3:** `cargo test -p argus-kernel cap_kind` — expect PASS (count + roundtrip).
- [ ] **Step 4: Commit** — `feat(argus): CapKind::GrantOverride`

### Task 8: ConfLevel::le helper + type deletions prep

**Files:**
- Modify: `argus/crates/argus-kernel/src/types.rs`

- [ ] **Step 1:** Write the failing test in `types.rs` tests:

```rust
    #[test]
    fn conf_level_le() {
        assert!(ConfLevel::Public.le(ConfLevel::Public));
        assert!(ConfLevel::Public.le(ConfLevel::Restricted));
        assert!(!ConfLevel::Restricted.le(ConfLevel::Sensitive));
    }
```

- [ ] **Step 2:** Implement on `ConfLevel` (next to `rank()`, line ~99). A plain method, not the `Ord` trait, so the extractor sees a concrete rank compare instead of trait dispatch:

```rust
    /// Total-order compare via rank (extraction-friendly: no trait dispatch).
    pub fn le(self, other: Self) -> bool {
        self.rank() <= other.rank()
    }
```

- [ ] **Step 3:** `cargo test -p argus-kernel conf_level_le` — PASS. Commit — `feat(argus): ConfLevel::le rank compare`

### Task 9: BackgroundTheory — ceilings replace the matrix

**Files:**
- Modify: `argus/crates/argus-kernel/src/background.rs`, `argus/crates/argus-kernel/src/types.rs` (deletions at the end)

- [ ] **Step 1:** Rewrite the struct + impl. Replace `flow_policy: VecMap<FlowKey, FlowMode>` and `flow_overrides: VecSet<OverrideEntry>` (struct AND builder, both at lines 24–30 / 69–75) with:

```rust
    allow_ceiling: VecMap<EgressKind, ConfLevel>,
    inspect_ceiling: VecMap<EgressKind, ConfLevel>,
```

Delete `has_flow_override` (lines 48–54) and builder `set_flow`/`add_override` (93–101). Replace `flow_mode` (41–46) with the computed form — same signature, so `flow_decision`/`gate_egress` downstream never change:

```rust
    /// Flow mode computed from the two per-egress ceilings. Absent entry = no level
    /// passes that band (strict default-deny, including Public). ALLOW wins over
    /// INSPECT where the bands overlap; outside both bands the mode is DENY.
    pub fn flow_mode(&self, level: ConfLevel, egress: EgressKind) -> FlowMode {
        let allows = match self.allow_ceiling.get_cloned(&egress) {
            Some(c) => level.le(c),
            None => false,
        };
        if allows {
            return FlowMode::Allow;
        }
        let inspects = match self.inspect_ceiling.get_cloned(&egress) {
            Some(c) => level.le(c),
            None => false,
        };
        if inspects { FlowMode::Inspect } else { FlowMode::Deny }
    }
```

- [ ] **Step 2:** Builder API. Add to `BackgroundTheoryBuilder`:

```rust
    /// Set (or clear, with `None`) the two confidentiality ceilings for an egress kind.
    pub fn set_egress_ceilings(
        &mut self,
        egress: EgressKind,
        allow: Option<ConfLevel>,
        inspect: Option<ConfLevel>,
    ) -> &mut Self {
        match allow {
            Some(c) => { self.allow_ceiling.insert(egress, c); }
            None => { self.allow_ceiling.remove(&egress); }
        }
        match inspect {
            Some(c) => { self.inspect_ceiling.insert(egress, c); }
            None => { self.inspect_ceiling.remove(&egress); }
        }
        self
    }
```

(`VecMap::remove` exists — `clear_agent_state` uses it. If its receiver differs, mirror the call shape in `collections.rs`.)

- [ ] **Step 3:** `from_matrix` compat constructor + error enum (the old flow-matrix linter becomes a converter). Add at module level in `background.rs`:

```rust
/// A (level, egress, mode) matrix that is not representable as ceilings: per egress the
/// ALLOW set must be a downward-closed prefix and the INSPECT band must sit directly
/// above it (absent entries are DENY).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlowMatrixError {
    NonMonotone,
}
```

and on the builder:

```rust
    /// Compat constructor: build a fresh builder whose ceilings encode `entries`
    /// (a mode matrix). Errs if the matrix is not ceiling-representable.
    pub fn from_matrix(
        entries: &[(ConfLevel, EgressKind, FlowMode)],
    ) -> Result<Self, FlowMatrixError> {
        const LEVELS: [ConfLevel; 4] = [
            ConfLevel::Public,
            ConfLevel::Internal,
            ConfLevel::Sensitive,
            ConfLevel::Restricted,
        ];
        const EGRESS: [EgressKind; 4] = [
            EgressKind::NetworkExternal,
            EgressKind::NetworkInternal,
            EgressKind::FilesystemWrite,
            EgressKind::Ipc,
        ];
        let mut builder = Self::new();
        let mut gi = 0;
        while gi < EGRESS.len() {
            let egress = EGRESS[gi];
            // Resolve each level's mode for this egress (last write wins, absent = Deny).
            let mut modes = [FlowMode::Deny; 4];
            let mut ei = 0;
            while ei < entries.len() {
                let (lv, eg, md) = entries[ei];
                if eg == egress {
                    let mut li = 0;
                    while li < LEVELS.len() {
                        if LEVELS[li] == lv {
                            modes[li] = md;
                        }
                        li += 1;
                    }
                }
                ei += 1;
            }
            // ALLOW must be a prefix, INSPECT the band directly above it.
            let mut allow_top: Option<ConfLevel> = None;
            let mut inspect_top: Option<ConfLevel> = None;
            let mut in_allow = true;
            let mut in_inspect = true;
            let mut li = 0;
            let mut monotone = true;
            while li < LEVELS.len() {
                match modes[li] {
                    FlowMode::Allow => {
                        if !in_allow {
                            monotone = false;
                        }
                        allow_top = Some(LEVELS[li]);
                    }
                    FlowMode::Inspect => {
                        in_allow = false;
                        if !in_inspect {
                            monotone = false;
                        }
                        inspect_top = Some(LEVELS[li]);
                    }
                    FlowMode::Deny => {
                        in_allow = false;
                        in_inspect = false;
                    }
                }
                li += 1;
            }
            if !monotone {
                return Err(FlowMatrixError::NonMonotone);
            }
            // Spec semantics: flow_inspects is its own band-from-bottom relation (ALLOW
            // wins where they overlap), so inspect_top is the inspect ceiling directly.
            builder.set_egress_ceilings(egress, allow_top, inspect_top);
            gi += 1;
        }
        Ok(builder)
    }
```

- [ ] **Step 4:** Migrate `background.rs` tests: `deny_is_default_flow_mode` stays as-is (empty builder → Deny). Replace `flow_policy_last_write_wins` and `flow_override_check` with ceiling-semantics tests:

```rust
    #[test]
    fn ceiling_band_boundaries() {
        let mut b = BackgroundTheoryBuilder::new();
        b.set_egress_ceilings(
            EgressKind::NetworkExternal,
            Some(ConfLevel::Internal),
            Some(ConfLevel::Sensitive),
        );
        let bg = b.build();
        assert_eq!(bg.flow_mode(ConfLevel::Public, EgressKind::NetworkExternal), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Internal, EgressKind::NetworkExternal), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Sensitive, EgressKind::NetworkExternal), FlowMode::Inspect);
        assert_eq!(bg.flow_mode(ConfLevel::Restricted, EgressKind::NetworkExternal), FlowMode::Deny);
        // Unconfigured egress: deny-all, including Public.
        assert_eq!(bg.flow_mode(ConfLevel::Public, EgressKind::Ipc), FlowMode::Deny);
    }

    #[test]
    fn empty_inspect_band_is_coherent() {
        let mut b = BackgroundTheoryBuilder::new();
        b.set_egress_ceilings(
            EgressKind::Ipc,
            Some(ConfLevel::Sensitive),
            Some(ConfLevel::Internal), // below allow ceiling: empty inspect band
        );
        let bg = b.build();
        assert_eq!(bg.flow_mode(ConfLevel::Internal, EgressKind::Ipc), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Restricted, EgressKind::Ipc), FlowMode::Deny);
    }

    #[test]
    fn from_matrix_roundtrip() {
        let b = BackgroundTheoryBuilder::from_matrix(&[
            (ConfLevel::Public, EgressKind::NetworkExternal, FlowMode::Allow),
            (ConfLevel::Internal, EgressKind::NetworkExternal, FlowMode::Inspect),
            (ConfLevel::Sensitive, EgressKind::NetworkExternal, FlowMode::Deny),
        ])
        .unwrap();
        let bg = b.build();
        assert_eq!(bg.flow_mode(ConfLevel::Public, EgressKind::NetworkExternal), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Internal, EgressKind::NetworkExternal), FlowMode::Inspect);
        assert_eq!(bg.flow_mode(ConfLevel::Sensitive, EgressKind::NetworkExternal), FlowMode::Deny);
        assert_eq!(bg.flow_mode(ConfLevel::Restricted, EgressKind::NetworkExternal), FlowMode::Deny);
    }

    #[test]
    fn from_matrix_rejects_non_monotone() {
        // Allow above a Deny hole: not ceiling-representable.
        let r = BackgroundTheoryBuilder::from_matrix(&[
            (ConfLevel::Public, EgressKind::NetworkExternal, FlowMode::Deny),
            (ConfLevel::Internal, EgressKind::NetworkExternal, FlowMode::Allow),
        ]);
        assert_eq!(r.err(), Some(FlowMatrixError::NonMonotone));
    }
```

- [ ] **Step 5:** Delete `FlowKey` and `OverrideEntry` from `types.rs` (lines 116–137; keep `OverrideKey`) and drop them from the `background.rs`/`transitions.rs` imports. The crate will not compile until Tasks 10–11 finish — that's fine, finish the sequence before testing.

### Task 10: KernelState gains `flow_override`

**Files:**
- Modify: `argus/crates/argus-kernel/src/state.rs`

- [ ] **Step 1:** Add the field after `override_used` (line 21), with `flow_override: VecMap::new()` in `initial()`:

```rust
    /// Live single-use flow-override grants, armed exclusively by `grant_override`
    /// (no background seeding). Exact `override_used` shape; cleared per-agent by
    /// `clear_agent_state`.
    pub flow_override: VecMap<AgentId, VecSet<OverrideKey>>,
```

- [ ] **Step 2:** Add the accessor (mirror `override_consumed`, line 62):

```rust
    /// True if `agent` holds an (armed or consumed) `flow_override` grant for
    /// `(tool, level)`. Consumption is tracked separately in `override_used`.
    pub fn has_flow_override(&self, agent: &AgentId, tool: &ToolId, level: ConfLevel) -> bool {
        match self.flow_override.get(agent) {
            Some(grants) => grants.contains(&OverrideKey { tool: tool.clone(), level }),
            None => false,
        }
    }
```

- [ ] **Step 3:** Test in `state.rs`:

```rust
    #[test]
    fn flow_override_lookup() {
        let mut st = KernelState::initial();
        let agent = AgentId::new("a1");
        st.flow_override.insert_into(
            agent.clone(),
            OverrideKey { tool: ToolId::new("t"), level: ConfLevel::Sensitive },
        );
        assert!(st.has_flow_override(&agent, &ToolId::new("t"), ConfLevel::Sensitive));
        assert!(!st.has_flow_override(&agent, &ToolId::new("t"), ConfLevel::Public));
        assert!(!st.has_flow_override(&AgentId::new("b"), &ToolId::new("t"), ConfLevel::Sensitive));
    }
```

### Task 11: Transitions — flow_decision rewire, clear_agent_state, grant_override

**Files:**
- Modify: `argus/crates/argus-kernel/src/transitions.rs`, `src/error.rs`, `src/event.rs`, `src/kernel.rs`

- [ ] **Step 1:** `flow_decision` (transitions.rs:41–49): the Deny arm reads state, not background:

```rust
        FlowMode::Deny => {
            if st.has_flow_override(agent, tool, level)
                && !st.override_consumed(agent, tool, level)
            {
                FlowDecision::ConsumedOverride
            } else {
                FlowDecision::Denied
            }
        }
```

- [ ] **Step 2:** `clear_agent_state` (line 53) gains `st.flow_override.remove(agent);` (grants die with the agent — matches the spec's delegate/revoke/cascade clearing clauses).
- [ ] **Step 3:** `error.rs`: add variant after `ChildHasInFlight`:

```rust
    /// The grant target still has in-flight invocations (re-arm guard).
    TargetHasInFlight,
```

- [ ] **Step 4:** `event.rs`: add to `KernelAction`:

```rust
    GrantOverride {
        granter: AgentId,
        target: AgentId,
        tool: ToolId,
        level: ConfLevel,
    },
```

and extend the `kernel_action_variant_count` test array with a `GrantOverride` value, asserting `13`.

- [ ] **Step 5:** The transition (after `sentinel_refresh_budget`, transitions.rs:599). Spec parity: cap gate on granter, granter budget gate + debit (return_endorsed shape), re-arm guard, arm `(tool, level)` for target, un-consume the same key:

```rust
/// Capability-gated arming (or re-arming) of a single-use flow override for
/// `(target, tool, level)`, debited to the GRANTER's declassification budget. The re-arm
/// guard (target has no in-flight invocations) is what keeps single-use sound across
/// re-arms: no in-flight flow can be retroactively justified by the fresh grant.
/// Self-grant (granter == target) is legal; the guard then binds the granter.
pub fn grant_override(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    granter: AgentId,
    target: AgentId,
    tool: ToolId,
    level: ConfLevel,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&granter) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_active.contains(&target) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_cap.set_contains(&granter, &CapKind::GrantOverride) {
        return Err(KernelError::CapabilityMissing);
    }
    if st.budget_exhausted(&granter) {
        return Err(KernelError::BudgetExhausted);
    }
    if st.in_flight.set_nonempty(&target) {
        return Err(KernelError::TargetHasInFlight);
    }

    st.flow_override.insert_into(
        target.clone(),
        OverrideKey { tool: tool.clone(), level },
    );
    st.override_used.remove_from(
        &target,
        &OverrideKey { tool: tool.clone(), level },
    );
    st.debit_budget(&granter);

    Ok((st, KernelAction::GrantOverride { granter, target, tool, level }))
}
```

(`remove_from` exists — `invoke_complete` uses it at line 408. If its key type differs, mirror that call site.)

- [ ] **Step 6:** `kernel.rs` driver method (after `sentinel_refresh_budget`, line 199):

```rust
    pub fn grant_override(
        &mut self,
        granter: AgentId,
        target: AgentId,
        tool: ToolId,
        level: ConfLevel,
    ) -> Result<KernelEvent, KernelError> {
        self.apply(transitions::grant_override(
            self.state.clone(),
            &self.background,
            granter,
            target,
            tool,
            level,
        ))
    }
```

### Task 12: Test migration + grant_override behavior tests

**Files:**
- Modify: `argus/crates/argus-kernel/src/transitions.rs` (test mod), `src/kernel.rs` (test mod), `tests/safety_properties.rs`

- [ ] **Step 1:** Mechanical migration of every `set_flow` call in tests. Recipe per egress: collect the modes a test sets and pick equivalent ceilings, e.g. `b.set_flow(Public, NetworkExternal, Allow)` → `b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None)`. For Inspect entries: `b.set_flow(Sensitive, NetworkExternal, Inspect)` → `b.set_egress_ceilings(NetworkExternal, None, Some(ConfLevel::Sensitive))` (or with the allow ceiling the test also needs). Tests asserting Deny on unset pairs need no change (absent = deny).
- [ ] **Step 2:** Mechanical migration of every `add_override(agent, tool, level)` in tests: seed state instead —

```rust
    st.flow_override.insert_into(
        agent.clone(),
        OverrideKey { tool: tool.clone(), level },
    );
```

- [ ] **Step 3:** New behavior tests in `transitions.rs` (use the existing `state_with_agent` / `bg_with_tools` helpers):
  - `grant_override_requires_cap`: granter without `CapKind::GrantOverride` → `Err(CapabilityMissing)`.
  - `grant_override_requires_granter_budget`: granter at `BudgetLevel::Exhausted` → `Err(BudgetExhausted)`.
  - `grant_override_debits_granter`: success debits granter one level, target untouched.
  - `grant_override_rearm_refused_while_target_in_flight`: target with an in-flight invocation → `Err(TargetHasInFlight)`.
  - `grant_override_rearms_consumed_override`: arm, consume it via a DENY-mode flow (e.g. `sentinel_elevate_taint`), confirm `override_consumed` true; complete/clear the flight, re-arm via `grant_override`, confirm `override_consumed` now false and a second DENY-mode flow is again rescued exactly once (single-use holds after re-arm).
  - `grant_override_self_grant`: granter == target, legal when granter has no flights.
  - `death_clears_override_grants`: `revoke` the target, confirm `st.flow_override.get(&target)` is `None`.
- [ ] **Step 4:** `tests/safety_properties.rs`: migrate builders; the override-related safety tests (`sentinel_elevate_taint_override_is_single_use` etc.) now arm via `transitions::grant_override` from root (root holds all 18 caps) instead of `add_override` — that exercises the real in-band path.
- [ ] **Step 5:** Run `cargo test -p argus-kernel` from `argus/` — ALL pass. Then `cargo clippy -p argus-kernel` — clean.
- [ ] **Step 6: Commit** — `feat(argus): ceiling flow policy + grant_override transition`

### Task 13: argus-explain migration (compile + semantics)

**Files:**
- Modify: `argus/crates/argus-explain/src/report.rs`, `src/invoke.rs`, `src/returns.rs`, `src/sentinel.rs`, `tests/agreement.rs`

- [ ] **Step 1:** Everywhere the gate logic consulted `bg.has_flow_override(...)` (invoke.rs:28 and the analogous sites in returns.rs/sentinel.rs), switch to `st.has_flow_override(...)` — the explain entry points already receive `st`.
- [ ] **Step 2:** `Rescue` gains the now-precise ceiling counterfactual (report.rs:31). Keep `PolicyAllow` for compat is NOT wanted — replace it (the comment at report.rs:35 anticipated this):

```rust
    /// Raise the named egress's ALLOW ceiling to `to_level` (the minimal raise that
    /// would flip this finding).
    CeilingRaise { egress: EgressKind, to_level: ConfLevel },
```

Emit it where `PolicyAllow` was pushed (invoke.rs:37 and analogues): `rescues.push(Rescue::CeilingRaise { egress, to_level: level });` — the denied level IS the minimal allow-ceiling raise. Update the unit assertions (invoke.rs:229–236) accordingly. `Rescue::OverrideGrant` stays unchanged (it is now directly actionable in-band via `grant_override`).
- [ ] **Step 3:** `tests/agreement.rs` generators:
  - Replace the `modes in vec(option::of(flow_mode()), LEVELS*EGRESS)` input + `set_flow` loop in `arb_background` with per-egress ceiling pairs:

```rust
        ceilings in prop::collection::vec(
            (prop::option::of(conf_level()), prop::option::of(conf_level())),
            EGRESS.len(),
        ),
```

```rust
        for (ei, e) in EGRESS.iter().enumerate() {
            let (allow, inspect) = ceilings[ei];
            b.set_egress_ceilings(*e, allow, inspect);
        }
```

  Delete the `flow_mode()` strategy and the `overrides` input + `add_override` loop.
  - `arb_state` gains a `flow_override` mask, identical shape to its existing `override_used` generation (`AGENTS.len() * TOOLS.len() * LEVELS.len()` bools seeding `st.flow_override.insert_into(...)`).
  - Keep the `(agent, tool)`-keyed content gate exactly as is (`e0074ad` closed that blind spot — do not regress it).
- [ ] **Step 4:** Delete `argus/crates/argus-explain/tests/agreement.proptest-regressions` ONLY if seeds fail to deserialize against the new generator shapes (they encode old inputs); note the deletion in the commit message. Run `PROPTEST_CASES=4096 cargo test -p argus-explain` — agreement suite passes.
- [ ] **Step 5:** `cargo test --workspace && cargo clippy --workspace` from `argus/` — green/clean.
- [ ] **Step 6: Commit** — `feat(argus-explain): ceiling rescues + state-side overrides`

**Stage 2 exit:** full workspace tests + clippy green; kernel semantics match the 13-action spec.

---

## Stage 3 — Extraction + refinement (argus/formal-lean)

This stage is proof work: statements below are exact; proof bodies are iterative. Reuse the established machinery — every needed bridging pattern already exists (memory: `c2-*`, `refinement-layer1-unified-r`, `refinement-layer2-soundness`, `wp-loop-proof-gotchas`). Exit gate is binary: `lake build` green + axiom audit.

### Task 14: Re-extract

- [ ] **Step 1:** From `argus/`: run `scripts/charon-aeneas-extract.sh` → fresh `argus_kernel.llbc` + regenerated `formal-lean/ArgusLean/Generated/ArgusKernel.lean`.
- [ ] **Step 2:** `lake build ArgusLean.Generated.ArgusKernel` from `argus/formal-lean/` — the model must elaborate (ceilings are `VecMap` gets and `from_matrix` is index loops, both modeled). If elaboration fails, the Rust idiom is wrong — fix the Rust (Stage 2 conventions), do not patch the generated file.
- [ ] **Step 3:** Commit — `chore(formal-lean): re-extract for ceilings + grant_override`

### Task 15: Flow bridging re-proof

**Files:**
- Modify: `ArgusLean/Refinement/Bridging/FlowOracle.lean`, `FlowBridging.lean`

- [ ] **Step 1:** The abstract side: the oracle defs that modeled `flow_allows`/`flow_inspects`/`flow_mode` now follow the ceiling encoding (`∃ c, ceiling e = some c ∧ le_conf l c`). Update `flowMode`-related defs to compute from two ceiling lookups.
- [ ] **Step 2:** Re-prove `flowDecision_spec` (3-way characterization) and `gateEgress_spec` (fold) over the new `flow_mode` body: two `VecMap` gets + rank compares — per the design, simpler than the old matrix lookup. The override arm now reads the concrete state's `flow_override` field (state-side `vmsMem`, identical machinery to `override_used` — see `StateRelation.lean`'s existing clause).
- [ ] **Step 3:** `lake build` the Bridging tree green. Commit.

### Task 16: State relation + init

**Files:**
- Modify: `ArgusLean/Refinement/Bridging/StateRelation.lean`, `ArgusLean/Refinement/Unified/Relation.lean`, `InitRefinement.lean`

- [ ] **Step 1:** Move the `flow_override` clause from the background-relating side to a state-side `vmsMem` clause (copy the `override_used` clause shape verbatim, swapping fields). Add ceiling-relating clauses for the two background `VecMap`s (last-match `vecMapGet_spec` style).
- [ ] **Step 2:** `InitRefinement`: concrete initial `flow_override` is the empty `VecMap`; abstract `initial` now demands `¬ flow_override` — same proof shape as the existing `override_used` init clause.
- [ ] **Step 3:** Build green; commit.

### Task 17: Patch the existing 12 preservation proofs

**Files:**
- Modify: `ArgusLean/Refinement/Unified/Preservation/{Delegate,Revoke,CascadeRevoke}.lean` (new flow_override drop clause — reuse the override_used drop machinery: `vmLastEntry_filter_removeKept`, key-removal specs)
- Modify: `Preservation/{InvokeStart,ReturnUnendorsed,SentinelElevateTaint}.lean` (flow leaves: override lookup now state-side; abstract side textually unchanged thanks to the derived defs)
- Modify: `Preservation/{RegisterTool,LoadInstruction,GrantCapability,InvokeComplete,ReturnEndorsed,SentinelRefreshBudget}.lean` (frame-only: flow_override unchanged by these actions — add the identity clause where `R` demands it)
- Modify: `ArgusLean/Refinement/Unified/{Bridges,NodupPreservation,ViewCoincidence}.lean` as the relation change ripples

- [ ] **Step 1:** Work action-by-action, `lake build` after each; the three revocation actions first (mechanical clause copy), then the three gated actions, then the frame-only six.
- [ ] **Step 2:** Known gotchas that WILL recur (don't rediscover them): tuple-bind `let (a, b)` needs full `simp at hok`; `subst` on an equation eliminating a named param — use `rw`; inverse-hypothesis pairs loop `scalar_tac` — compute arith first, then `clear`; `Ne` is not rewritable; heartbeat bombs in `tauto` → `Or/And.imp_right`.
- [ ] **Step 3:** Commit per action or per group.

### Task 18: grant_override simulation + 13-arm bundle

**Files:**
- Create: `ArgusLean/Refinement/Unified/Preservation/GrantOverride.lean`
- Modify: `ArgusLean/Refinement/Unified/{Bundle,Soundness}.lean`

- [ ] **Step 1:** New sim, composed entirely of existing bridging: `insert_into` membership (`VecMapKVecSet.insert_into` spec) for the arm, `remove_from` spec for the un-consume, `debitBudget_spec` for the granter debit, `set_nonempty` ↔ `∃ I, in_flight` for the re-arm guard. Inversion style (`cases` on `hok`), not forward — per the C1 totality-tax decision.
- [ ] **Step 2:** `Bundle.lean`: 13th `_preservesR` + `step_refines` arm; reassemble `implementation_sound` against the 13-action Kav system (`kav_soundP` is sort-polymorphic; the tzimtzum side already exports the 13-action `kav_sound` from Stage 1).
- [ ] **Step 3:** Full `lake build` from `argus/formal-lean/` — green. Axiom audit on `implementation_sound`: same baseline set as today (standard three + Aeneas/Charon residuals + `CapacityOK`/`OracleFidelity`; `AgentId.root`/`sorryAx`-baseline axioms where root is named, per the invoke_start precedent). Any NEW axiom needs explicit justification in the commit message.
- [ ] **Step 4:** Commit — `feat(formal-lean): implementation_sound over 13 actions`

**Stage 3 exit:** formal-lean builds green, `implementation_sound` proven, axiom set documented.

---

## Stage 4 — ex_argus + argus-explain surface (after Stages 1–3)

### Task 19: Mirror types + state_version bump

**Files:**
- Modify: `ex_argus/lib/ex_argus.ex` (`@state_version 1` → `2`)
- Modify: `ex_argus/lib/ex_argus/kernel/background.ex`, `kernel/state.ex`, `kernel/types.ex`
- Modify: `ex_argus/native/argus_nif/src/state.rs` (`BackgroundN`, `StateN`), `src/enums.rs`

- [ ] **Step 1:** `background.ex`: replace `flow_policy`/`flow_overrides` with ceilings:

```elixir
  defstruct tools: %{},
            allow_ceiling: %{},
            inspect_ceiling: %{},
            trusted_issuers: [],
            instruction_issuer: %{}
```

with types `allow_ceiling: %{optional(Types.egress_kind()) => Types.conf_level()}` (same for inspect). Update the moduledoc list.
- [ ] **Step 2:** `state.ex`: add `flow_override` field mirroring `override_used`'s shape (`%{agent_id => [{tool_id, level}]}` — copy whatever encoding `override_used` uses in that struct, they must match).
- [ ] **Step 3:** `native/argus_nif/src/state.rs`: `BackgroundN` drops `flow_policy`/`flow_overrides`, gains `pub allow_ceiling: HashMap<EgressKindN, ConfLevelN>` + `inspect_ceiling`; `into_kernel` calls `b.set_egress_ceilings(egress.into_kernel(), Some(level.into_kernel()), ...)` per entry (two loops, one per map). `StateN` gains `flow_override` (copy the `override_used` field + both conversion directions in `into_kernel`/`from_kernel`). Round-trip unit tests in `state.rs` extended to cover `flow_override`.
- [ ] **Step 4:** `enums.rs`: add the `grant_override` cap atom to the `CapKind` mapping (18th).

### Task 20: grant_override through the NIF + Elixir API

**Files:**
- Modify: `ex_argus/native/argus_nif/src/nifs.rs` (stateless), `src/instance.rs`, `src/event.rs`
- Modify: `ex_argus/lib/ex_argus/native.ex`, `offline.ex`, `instance.ex`, `replay.ex`

- [ ] **Step 1:** `event.rs`: `ActionN::from_kernel` gains the `KernelAction::GrantOverride` arm (atom `:grant_override`, fields granter/target/tool/level); `ErrorN` gains `TargetHasInFlight` → `:target_has_in_flight`.
- [ ] **Step 2:** Stateless NIF in `nifs.rs` + instance NIF in `instance.rs`, copied from the `sentinel_refresh_budget` pair with the 4 args (granter, target, tool, level — no oracle callbacks; it's oracle-free like return_endorsed).
- [ ] **Step 3:** Elixir: `Native` stubs `grant_override(_state, _bg, _granter, _target, _tool, _level)` + `instance_grant_override(_h, _granter, _target, _tool, _level)`; `Offline` defdelegate; `Instance` defdelegate (`grant_override/5` on the handle). `Replay`/`Instance.recover/2`: add the `:grant_override` log-entry arm wherever the other 12 actions are dispatched (compiler/exhaustiveness will point at the dispatch site).
- [ ] **Step 4:** `Explain`-related Elixir decoding: add the `:ceiling_raise` rescue variant mapping (and remove `:policy_allow`) wherever `Rescue` atoms are decoded (grep `policy_allow` under `ex_argus/lib` + `native/argus_nif/src/explain.rs`).
- [ ] **Step 5:** Tests (`ex_argus/test/`): migrate background fixtures to ceilings; add `Instance` tests: grant → deny-mode flow rescued exactly once → re-arm refused while in-flight → re-arm after completion works; recovery replay of a log containing `grant_override` reproduces the state.
- [ ] **Step 6:** From `ex_argus/`: `mix test` — green. Commit — `feat(ex_argus): ceilings + grant_override on Instance/Offline`

**Stage 4 exit:** `mix test` green on `Instance`/`Offline`; replay/recovery carries grant_override.

---

## Stage 5 — Exit criteria + docs (merge gate)

- [ ] **Step 1: Full verification matrix** (ALL must pass, fresh runs):
  - `tzimtzum/`: `make verify` (13-action VC suite) + axiom audit
  - `argus/`: `cargo test --workspace && cargo clippy --workspace`
  - `argus/formal-lean/`: `lake build` (implementation_sound) + `#print axioms`
  - `argus/crates/argus-explain`: `PROPTEST_CASES=4096 cargo test -p argus-explain`
  - `ex_argus/`: `mix test`
- [ ] **Step 2: Docs.** Update `CLAUDE.md` (project): 12 → 13 actions, CapKind 17 → 18, flow policy description (ceilings, overrides in state), test counts. Update `argus/formal-lean/README.md` if it states 12.
- [ ] **Step 3:** Update memory: mark `campaign-a-ceilings-grant-override-design` as IMPLEMENTED with the landing commit, note any contingency invariant / new axioms / deviations.
- [ ] **Step 4:** Use superpowers:finishing-a-development-branch to integrate `feat/campaign-a-ceilings`.

---

## Notes for the implementer

- **Semantics note (recorded, not a bug):** the kernel is *stricter* than the spec on inspect-band + content-gate-fail + override-present (kernel denies; the spec disjunction would admit). Already true today; the refinement direction (kernel steps simulated by spec steps) is unaffected. Do not "fix" this.
- **Spec is source of truth.** If kernel behavior and spec diverge during Stage 2, the spec (Stage 1, as designed) wins; change the Rust.
- **`flow_mode` keeps its signature** specifically so `flow_decision`, `gate_egress`, and the three gated transitions need zero changes beyond the override-lookup rewire. If you find yourself editing their loop structure, stop — something upstream is wrong.
- **`OverrideKey` stays; `FlowKey`/`OverrideEntry` die.** The state-side grant store deliberately reuses `OverrideKey` so the refinement reuses the `override_used` bridging verbatim.
