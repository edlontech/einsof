import Tzimtzum.Soundness.Bundle

/-! # C0 — Kav soundness bundle for TzimtzumV2 (aggregator)

Assembles the 442 per-action / per-init verification conditions (26 init + 16 x 26) into
a single reachability theorem

  `Tzimtzum.kav_sound : ∀ s, Reachable ksystem s → allInv s`

via the protocol-independent `Kav.reachable_sound` meta-induction. This is the Lean
analog of the retired Rocq `invariants_inductive` bundle; the soundness conclusion of
Phase C (C3) consumes it.

The proof is split across `Tzimtzum/Soundness/`:
* `Common`                   — `allInv`, `all_goals_fresh`, `kav_discharge`, `ksystem`.
* `PresMost`                 — initiation + the eleven cascade-discharged actions.
* `PresInvokeComplete`       — `invoke_complete_endorsed` / `invoke_complete_unendorsed`
                                (budget VCs slotted manually where the classical `ite`
                                stalls the cascade).
* `PresReturnEndorsed`       — `return_endorsed` (budget VCs slotted manually).
* `PresGrantOverride`        — `grant_override` (budget VCs slotted manually).
* `PresSentinelCreditBudget` — `sentinel_credit_budget` (budget VCs slotted manually).
* `Bundle`                   — `kav_sound` via `reachable_sound`.

## Trust base

Every proof term is kernel-checked (`grind` / `simp_all` / `auto` / `duper`, all routed
through `Kav.Engine`'s Auto→Duper rebind — no external solver oracle).
`#print axioms kav_sound` is expected to show only
`propext` / `Classical.choice` / `Quot.sound`. -/

#print axioms Tzimtzum.kav_sound
