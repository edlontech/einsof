import ArgusLean.Refinement.Bridging.StateRelation

/-! # Layer 1 — view-coincidence lemmas

The 12 per-action simulation lemmas each read `agent_cap` / `in_flight` / `taint_levels` /
`gh_*` / `override_used` / `agent_budget` through one of several *views*:

* `vsMem` — set membership (`agent_active`, `tool_registered`);
* `vmsMem` — `∃`-entry nested membership (the *remove*/clear actions: delegate, cascade, revoke,
  and the taint-inserting `invoke_complete` / `sentinel_elevate_taint`);
* `vmsMemLast` — *last-match* nested membership (the flow actions and `grant_capability`'s cap read);
* `capMem` — get-style cap read (delegate/cascade/revoke);
* `budgetReadC` — get-style budget read (`return_endorsed`, `invoke_complete`) vs the raw-membership
  budget clause (delegate/cascade/refresh).

The unified relation `R` (next module) picks **one canonical view per field** — the last-match /
get-style reads, since those are what the kernel literally computes. This module proves the bridges
that let each slice's view be derived from (and re-established into) the canonical one. The only
non-trivial side condition is **key-uniqueness** (`vmNodupKeys`): with duplicate keys the kernel's
last-match read disagrees with `∃`-entry membership, so `R` carries `vmNodupKeys` for every per-agent
map and these lemmas consume it.

All bridges are pure; no new axioms beyond the `register_tool` exemplar's `String`/id residuals. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

/-! ## `vmLastEntry` structural facts -/

/-- The resolved last entry of `key` is itself keyed `key` (it is drawn from the `key`-filtered
    sublist). Turns a bare `capMem`/get-style witness into a `(key, _)`-shaped one. -/
theorem vmLastEntry_key {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K) (p : K × V)
    (h : vmLastEntry l key = some p) : p.1 = key := by
  have hmem : p ∈ l.filter (vmKeyEq key) := List.mem_of_getLast? h
  rw [List.mem_filter] at hmem
  simpa [vmKeyEq] using hmem.2

/-- `key` resolves to nothing iff there is no `key`-keyed entry at all. The "absent key" half of the
    budget convention. -/
theorem vmLastEntry_none_iff {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K) :
    vmLastEntry l key = none ↔ ∀ v, (key, v) ∉ l := by
  rw [vmLastEntry, List.getLast?_eq_none_iff, List.filter_eq_nil_iff]
  constructor
  · intro h v hv
    exact absurd (by simp [vmKeyEq] : vmKeyEq key (key, v) = true) (h _ hv)
  · intro h p hp hcontra
    have hpk : p.1 = key := by simpa [vmKeyEq] using hcontra
    obtain ⟨k, v⟩ := p
    simp only at hpk; subst hpk
    exact h v hp

/-! ## `vmsMem` ↔ `vmsMemLast` (key-uniqueness coincidence) -/

/-- Under unique keys, `∃`-entry nested membership coincides with the last-match read: there is at
    most one `k`-keyed entry, so "some entry holds `v`" and "the *last* entry holds `v`" agree. This is
    the bridge that lets the remove/insert actions' `vmsMem` slices feed (and re-establish) `R`'s
    canonical `vmsMemLast` view. The `←` direction never needs uniqueness. -/
theorem vmsMem_iff_vmsMemLast {K T : Type} [DecidableEq K]
    (vm : collections.VecMap K (collections.VecSet T))
    (hnd : vmNodupKeys vm) (k : K) (v : T) :
    vmsMem vm k v ↔ vmsMemLast vm k v := by
  constructor
  · rintro ⟨vs, hmem, hv⟩
    exact ⟨vs, (vmLastEntry_nodup vm.entries.val k vs hnd).mpr hmem, hv⟩
  · rintro ⟨vs, hlast, hv⟩
    exact ⟨vs, vmLastEntry_mem _ _ _ hlast, hv⟩

/-! ## `capMem` ↔ `vmsMemLast` (definitional coincidence) -/

/-- The get-style cap read `capMem` is the last-match nested membership `vmsMemLast`. `vmLastEntry`
    only ever returns a `(N, _)`-keyed entry, so the bare-pair `capMem` and the key-shaped `vmsMemLast`
    coincide with **no** side condition. Reconciles delegate/cascade/revoke's `capMem` with the
    canonical `vmsMemLast` view of `agent_cap`. -/
theorem capMem_iff_vmsMemLast
    (vm : collections.VecMap types.AgentId (collections.VecSet capability.CapKind))
    (N : types.AgentId) (C : capability.CapKind) :
    capMem vm N C ↔ vmsMemLast vm N C := by
  constructor
  · rintro ⟨⟨k, v⟩, hp, hC⟩
    have hkey : k = N := vmLastEntry_key _ _ _ hp
    subst k
    exact ⟨v, hp, hC⟩
  · rintro ⟨vs, hlast, hC⟩
    exact ⟨(N, vs), hlast, hC⟩

/-! ## raw budget membership ↔ `budgetReadC` (key-uniqueness coincidence) -/

/-- Under unique budget keys, the raw-membership budget clause (used by delegate/cascade/refresh:
    "`(G, budgetC L)` is an entry, or `G` is absent and `L = bl5`") coincides with the get-style read
    `budgetReadC` the kernel computes (`return_endorsed`/`invoke_complete`). Uses `budgetC` injectivity
    to pin the level. The reconciliation of the two budget views the unified `R` needs. -/
theorem budgetRaw_iff_budgetReadC (vm : collections.VecMap types.AgentId types.BudgetLevel)
    (hnd : vmNodupKeys vm) (G : types.AgentId) (L : Tzimtzum.BudgetLevel) :
    (((G, budgetC L) ∈ vm.entries.val) ∨
      ((∀ bl, (G, bl) ∉ vm.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5))
    ↔ budgetReadC vm G = budgetC L := by
  unfold budgetReadC
  cases hlast : vmLastEntry vm.entries.val G with
  | none =>
    have habsent : ∀ w, (G, w) ∉ vm.entries.val := (vmLastEntry_none_iff _ _).mp hlast
    simp only []
    constructor
    · rintro (hmem | ⟨_, hL5⟩)
      · exact absurd hmem (habsent _)
      · subst hL5; rfl
    · intro h
      have hh : budgetC Tzimtzum.BudgetLevel.bl5 = budgetC L := h
      exact Or.inr ⟨habsent, (budgetC_injective hh).symm⟩
  | some p =>
    obtain ⟨k, v⟩ := p
    have hk : k = G := vmLastEntry_key _ _ _ hlast
    subst k
    have hmem : (G, v) ∈ vm.entries.val := vmLastEntry_mem _ _ _ hlast
    show (((G, budgetC L) ∈ vm.entries.val) ∨
        ((∀ bl, (G, bl) ∉ vm.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5)) ↔ v = budgetC L
    constructor
    · rintro (hmemL | ⟨habs, _⟩)
      · have hL := (vmLastEntry_nodup vm.entries.val G (budgetC L) hnd).mpr hmemL
        rw [hlast, Option.some_inj, Prod.mk.injEq] at hL
        exact hL.2
      · exact absurd hmem (habs v)
    · intro h; rw [h] at hmem; exact Or.inl hmem

end ArgusLean.Refinement
