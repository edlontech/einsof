# Kav: kernel-checked invariant verifier

Kav is a pure-Lean 4 transition-system verification framework. It uses mathlib
(Lean 4.30.0 + mathlib v4.30.0) and Duper as automation backends.

It is a reusable library. The TzimtzumV2 protocol that exercises it lives in the sibling
[`tzimtzum/`](../tzimtzum/) project, which `require`s Kav.

## What Kav is

Kav provides:

- A transition-system DSL (`kav_action`, `Kav.Action`, `Kav.TransitionSystem`) for
  defining states, actions, and invariants as pure Lean `Prop`s.
- A `#kav_check_action` command that builds and discharges per-(action, invariant)
  preservation VCs, and a `#kav_check_init` command for initiation VCs.
- A cascade tactic (`trivial | grind | (simp_all <;> grind) | auto | duper [*]`) that
  closes the generated goals kernel-checked.
- A `FiniteModel` checker (`Kav.ModelCheck`) for bug-finding on small finite instances (the
  `#kav_model_check` command).

## Two-phase design

Phase 1, inductive verification (`#kav_check_action` / `#kav_check_init`): generates and
discharges the per-(action, invariant) VCs that constitute an inductive-invariant proof.

Phase 2, bug-finding (`Kav.FiniteModel`, `#kav_model_check`): a finite-model checker that
exhaustively tests a `FiniteModel σ` (a list of concrete states plus Bool-valued
guard/next/inv) for counterexamples-to-induction (CTIs). Used during development to catch
spec bugs before attempting inductive proofs.

The `Kav.Spike` modules demonstrate phase 2 on a Bool-valued mirror of an `invoke_start`
action: `invoke_start_model_check` shows the guard fires on a non-initial seed state
(non-vacuity), while the `findCTI_broken` search confirms the mechanism detects a planted
override-consumption bug.

### Trust base

The automation cascade uses only mathlib tactics (`grind`, `simp_all`, `auto`, `duper`);
discharged VCs depend only on the three standard Lean kernel axioms:

```
[propext, Classical.choice, Quot.sound]
```

See `tzimtzum/Tzimtzum/Audit.lean` for a worked `#print axioms` audit on a real protocol.

## Building

```bash
cd kav/
lake build Kav           # base framework library
lake build KavTest       # framework self-tests (ActionTest/CheckTest/ModelCheckTest/SolveTest)
```

Toolchain: Lean 4.30.0 + mathlib v4.30.0.

## File layout

```
kav/
  lakefile.toml              Kav + KavTest build targets
  KavTest.lean               aggregator: framework Test modules
  lean-toolchain             v4.30.0
  Kav/
    Core.lean                TransitionSystem, Action, Invariant types
    Action.lean              kav_action macro
    Transition.lean          Transition DSL helpers
    Engine.lean              discharge engine (grind/auto/duper cascade)
    Check.lean               #kav_check_invariants command
    CheckAction.lean         #kav_check_action command
    CheckInit.lean           #kav_check_init command
    ModelCheck.lean          FiniteModel checker
    ModelCheckCmd.lean       #kav_model_check command
    Solve.lean               kav_solve tactic
    Spike/
      InvokeStart.lean       Prop-level spike proofs (invoke_start_pres_*)
      ModelCheck.lean        Bool-mirror model check + non-vacuity witness
```
