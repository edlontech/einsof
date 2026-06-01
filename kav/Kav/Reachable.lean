import Kav.Core

/-! # Reachability closure + generic soundness combinator

The piece the per-action `#kav_check_action` / `#kav_check_init` VCs were missing: a
single `Reachable` predicate and the meta-induction that turns

  "init establishes the invariant bundle" + "every action preserves it"

into

  "every reachable state satisfies the bundle".

This is the protocol-independent analog of the (retired) Rocq `invariants_inductive`
bundle. The TzimtzumV2 instantiation — `def allInv` + the per-action preservation
lemmas + `kav_sound` — lives in `tzimtzum/`. Nothing here mentions a solver: the
combinator is a plain structural induction, so it adds nothing to the trust base
beyond the kernel. -/

namespace Kav

/-- Reachability closure of a transition system: the least predicate containing every
    initial state and closed under every labeled action (its guard must hold in the
    pre-state and its post-relation must connect pre- and post-states). -/
inductive Reachable {σ : Type} (ts : TransitionSystem σ) : σ → Prop where
  | init {s : σ} (h : ts.init s) : Reachable ts s
  | step {s s' : σ} {name : String} {act : Action σ}
      (hmem : (name, act) ∈ ts.actions)
      (hreach : Reachable ts s)
      (hguard : act.guard s)
      (hnext : act.next s s') :
      Reachable ts s'

/-- **Soundness combinator (meta-induction).** A predicate that holds at every initial
    state and is preserved by every action of the system holds at every reachable state.

    `hinit` is exactly the conjunction of the per-invariant initiation VCs (`initVC`) and
    `hpres` the conjunction of the per-(action, invariant) preservation VCs (`preservesVC`),
    bundled over `inv`. Discharging those VCs (e.g. via `#kav_check_init` /
    `#kav_check_action`) and assembling them here yields `Reachable ⊆ inv`. -/
theorem reachable_sound {σ : Type} {ts : TransitionSystem σ} {inv : σ → Prop}
    (hinit : ∀ s, ts.init s → inv s)
    (hpres : ∀ na ∈ ts.actions, ∀ s s', inv s → na.2.guard s → na.2.next s s' → inv s')
    {s : σ} (hreach : Reachable ts s) : inv s := by
  induction hreach with
  | init h => exact hinit _ h
  | step hmem _ hguard hnext ih => exact hpres _ hmem _ _ ih hguard hnext

end Kav
