import ArgusLean.Refinement.Collections
import Tzimtzum

/-! # C1 refinement spike — state relation

The abstract TzimtzumV2 state (`Tzimtzum.St`) instantiated at the kernel's concrete
sorts, plus the relation `Rtool` capturing exactly the fields the `register_tool`
transition reads or writes. (The full state relation `R` over all 28 fields is the C2
fan-out task; `Rtool` is the per-action slice the spike's simulation needs.) -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- The abstract TzimtzumV2 state at the kernel's concrete sorts. `ConfLevel`/`BudgetLevel`
    are concrete inductives baked into `St`; the remaining seven sorts are the extracted
    `String`/inductive types. -/
abbrev AbsState := Tzimtzum.St types.AgentId types.ToolId types.InvocationId
  capability.CapKind types.EgressKind types.IssuerId types.InstructionId

/-- State relation for the fields `register_tool` touches:
    * the mutable `tool_registered` set ↔ the concrete `VecSet`;
    * the background `trusted_issuer` predicate ↔ the `trusted_issuers` `VecSet`;
    * the background `tool_issuer` function ↔ the registered tools' metadata issuer. -/
def Rtool (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ t, a.tool_registered t ↔ vsMem st.tool_registered t) ∧
  (∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i) ∧
  (∀ t tm, bg.tool_metadata t = .ok (some tm) → a.tool_issuer t = tm.issuer)

/-- State relation for the fields `load_instruction` touches:
    * the mutable `agent_active` set ↔ the concrete `VecSet`;
    * the background `trusted_issuer` predicate ↔ the `trusted_issuers` `VecSet`;
    * the background `instruction_issuer` function ↔ the concrete lookup;
    * the mutable nested `agent_instruction` relation ↔ the concrete `VecMap`-of-`VecSet`. -/
def Rinstr (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i) ∧
  (∀ i issuer, background.BackgroundTheory.impl.instruction_issuer bg i = .ok (some issuer) →
      a.instruction_issuer i = issuer) ∧
  (∀ ag ins, a.agent_instruction ag ins ↔ vmsMem st.agent_instruction ag ins)

/-! ## Confidentiality / budget correspondence

`ConfLevel` and `BudgetLevel` are baked-in inductives of the abstract `St` (not type
parameters), so the taint/budget fields cross from the abstract lattice to the extracted
`types.*` lattice. The two are constructor-for-constructor identical; `confC` / `budgetC` are
the obvious total maps. `delegate` only ever *clears* these fields, so the proof uses the maps
opaquely (membership passes through symmetrically) — no bijectivity is required. -/

/-- Abstract → concrete confidentiality level. -/
def confC : Tzimtzum.ConfLevel → types.ConfLevel
  | .«public»   => .Public
  | .«internal» => .Internal
  | .sensitive  => .Sensitive
  | .restricted => .Restricted

/-- Abstract → concrete budget level. -/
def budgetC : Tzimtzum.BudgetLevel → types.BudgetLevel
  | .bl_exhausted => .Exhausted
  | .bl1          => .L1
  | .bl2          => .L2
  | .bl3          => .L3
  | .bl4          => .L4
  | .bl5          => .L5

/-- Get-style membership for the cap map: `C` is a cap of `N` iff the *last* `N`-keyed entry
    (the live one under `VecMap` last-match semantics) holds `C`. Survives duplicate keys, so
    the `insert grantee ∅` that `delegate` uses to clear a grantee's caps reads as empty. -/
def capMem (vm : collections.VecMap types.AgentId (collections.VecSet capability.CapKind))
    (N : types.AgentId) (C : capability.CapKind) : Prop :=
  ∃ p, vmLastEntry vm.entries.val N = some p ∧ C ∈ p.2.items.val

/-- Key-uniqueness well-formedness for a `VecMap`: the entry keys are `Nodup`. The invariant that
    makes the get-style reading of a *functional* map (`agent_parent`) faithful — without it the
    last-match rebuild in `agent_parent_drop_endpoint` disagrees with the abstract post-image
    (the counterexample the Plausible harness pins). `delegate` preserves it (it rebuilds
    `agent_parent` from an empty map). -/
def vmNodupKeys {K V : Type} (vm : collections.VecMap K V) : Prop :=
  (vm.entries.val.map Prod.fst).Nodup

/-- State relation for the ten fields `delegate` touches:

    * `agent_active` ↔ the `VecSet` (`vsMem`);
    * `agent_cap` ↔ the cap map under get-semantics (`capMem`);
    * `agent_parent` ↔ the parent map under get-semantics (`vmLastEntry`), guarded by the
      `vmNodupKeys` key-uniqueness invariant (the last conjunct);
    * `agent_instruction` / `in_flight` ↔ their nested sets (`vmsMem`, id sorts);
    * `taint_levels` / `gh_taint_invoked` / `gh_taint_received` ↔ nested `ConfLevel` sets
      (`vmsMem` through `confC`);
    * `override_used` ↔ the nested `OverrideKey` set (tool × `confC` level);
    * `agent_budget` ↔ a plain `BudgetLevel` map with the "absent key = full budget (`bl5`)"
      default that the kernel uses. -/
def Rdel (st : state.KernelState) (a : AbsState) : Prop :=
  (types.AgentId.root = .ok a.root_agent) ∧
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ N C, a.agent_cap N C ↔ capMem st.agent_cap N C) ∧
  (∀ ag ins, a.agent_instruction ag ins ↔ vmsMem st.agent_instruction ag ins) ∧
  (∀ ag inv, a.in_flight ag inv ↔ vmsMem st.in_flight ag inv) ∧
  (∀ ag L, a.taint_levels ag L ↔ vmsMem st.taint_levels ag (confC L)) ∧
  (∀ ag L, a.gh_taint_invoked ag L ↔ vmsMem st.gh_taint_invoked ag (confC L)) ∧
  (∀ ag L, a.gh_taint_received ag L ↔ vmsMem st.gh_taint_received ag (confC L)) ∧
  (∀ ag t L, a.override_used ag t L ↔
    vmsMem st.override_used ag { tool := t, level := confC L }) ∧
  (∀ G L, a.agent_budget G L ↔
    ((G, budgetC L) ∈ st.agent_budget.entries.val) ∨
    ((∀ bl, (G, bl) ∉ st.agent_budget.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5)) ∧
  (∀ C P, a.agent_parent C P ↔ vmLastEntry st.agent_parent.entries.val C = some (C, P)) ∧
  vmNodupKeys st.agent_parent

/-- State relation for the removal actions (`cascade_revoke`, `revoke`). Touches exactly the same
    ten fields as `Rdel`, with **one** difference: the `agent_budget` clause is guarded by
    `a.agent_active G`.

    This guard is forced by the asymmetry between insert and remove. The kernel's budget convention
    is "absent key = full budget (`bl5`)"; `delegate` adds an agent and sets its budget to `bl5`, so
    the unguarded clause holds (absent ↔ `bl5`). A removal action *deletes* the agent's budget entry,
    leaving it absent — which the convention reads as `bl5` — while the abstract action drops the
    agent's budget relation to `False`. Those disagree at `bl5` for the just-removed (now inactive)
    agent. They agree exactly where the convention is observable: on **active** agents. The abstract
    invariants `budget_unique` / `active_has_budget` are themselves guarded by `agent_active`,
    confirming budget is only semantically meaningful there. So the faithful refinement relation
    relates budget on active agents only; an `Rdel` pre-state implies the corresponding `Rcasc` one.
    (See [[c2-cascade-revoke]].) -/
def Rcasc (st : state.KernelState) (a : AbsState) : Prop :=
  (types.AgentId.root = .ok a.root_agent) ∧
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ N C, a.agent_cap N C ↔ capMem st.agent_cap N C) ∧
  (∀ ag ins, a.agent_instruction ag ins ↔ vmsMem st.agent_instruction ag ins) ∧
  (∀ ag inv, a.in_flight ag inv ↔ vmsMem st.in_flight ag inv) ∧
  (∀ ag L, a.taint_levels ag L ↔ vmsMem st.taint_levels ag (confC L)) ∧
  (∀ ag L, a.gh_taint_invoked ag L ↔ vmsMem st.gh_taint_invoked ag (confC L)) ∧
  (∀ ag L, a.gh_taint_received ag L ↔ vmsMem st.gh_taint_received ag (confC L)) ∧
  (∀ ag t L, a.override_used ag t L ↔
    vmsMem st.override_used ag { tool := t, level := confC L }) ∧
  (∀ G L, a.agent_active G → (a.agent_budget G L ↔
    ((G, budgetC L) ∈ st.agent_budget.entries.val) ∨
    ((∀ bl, (G, bl) ∉ st.agent_budget.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5))) ∧
  (∀ C P, a.agent_parent C P ↔ vmLastEntry st.agent_parent.entries.val C = some (C, P)) ∧
  vmNodupKeys st.agent_parent

/-- `VecMap.remove key` read through `capMem`: the removed key resolves to no caps, every other
    agent's caps are untouched. The `agent_cap` counterpart of `vmsMem_filter_removeKept`, built on
    the pure `vmLastEntry_filter_removeKept`. -/
theorem capMem_filter_removeKept
    (vm' vm : collections.VecMap types.AgentId (collections.VecSet capability.CapKind))
    (key : types.AgentId)
    (h : vm'.entries.val = vm.entries.val.filter (removeKept key)) (N : types.AgentId)
    (C : capability.CapKind) :
    capMem vm' N C ↔ capMem vm N C ∧ N ≠ key := by
  unfold capMem
  rw [h, vmLastEntry_filter_removeKept]
  by_cases hN : N = key
  · simp [hN]
  · rw [if_neg hN]
    constructor
    · rintro ⟨p, hp, hC⟩; exact ⟨⟨p, hp, hC⟩, hN⟩
    · rintro ⟨⟨p, hp, hC⟩, _⟩; exact ⟨p, hp, hC⟩

/-- State relation for the fields `grant_capability` touches: the two active gates (`vsMem`), the
    parent-edge gate read get-style (`vmLastEntry`, like the removal actions), and `agent_cap` as the
    **nested** set membership `vmsMem` — the view `set_contains` / `insert_into` operate in (the same
    one `load_instruction`'s `agent_instruction` uses), which needs no key-uniqueness side condition.
    (Distinct from `Rdel`/`Rcasc`'s get-style `capMem` view of `agent_cap`; reconciling the two is the
    future unified-`R` task, and only matters once an action mixes both.) -/
def Rgrant (st : state.KernelState) (a : AbsState) : Prop :=
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ C P, a.agent_parent C P ↔ vmLastEntry st.agent_parent.entries.val C = some (C, P)) ∧
  (∀ N C, a.agent_cap N C ↔ vmsMem st.agent_cap N C)

/-! ## Shared transition helper: `clear_agent_state`

`clear_agent_state st agent` deletes `agent`'s key from the seven per-agent maps
(`taint_levels`, `in_flight`, `gh_taint_invoked`, `gh_taint_received`, `agent_instruction`,
`override_used`, `agent_budget`) and frames everything else. Each delete is a `VecMap.remove`,
so each touched field becomes the key-filtered entry list. Shared by `delegate` / `revoke` /
`cascade_revoke`. -/
theorem clearAgentState_spec (st : state.KernelState) (agent : types.AgentId) :
    transitions.clear_agent_state st agent ⦃ st1 =>
      st1.agent_active = st.agent_active ∧
      st1.agent_parent = st.agent_parent ∧
      st1.agent_cap = st.agent_cap ∧
      st1.invocation_tool = st.invocation_tool ∧
      st1.tool_registered = st.tool_registered ∧
      st1.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept agent) ∧
      st1.in_flight.entries.val = st.in_flight.entries.val.filter (removeKept agent) ∧
      st1.gh_taint_invoked.entries.val = st.gh_taint_invoked.entries.val.filter (removeKept agent) ∧
      st1.gh_taint_received.entries.val = st.gh_taint_received.entries.val.filter (removeKept agent) ∧
      st1.agent_instruction.entries.val = st.agent_instruction.entries.val.filter (removeKept agent) ∧
      st1.override_used.entries.val = st.override_used.entries.val.filter (removeKept agent) ∧
      st1.agent_budget.entries.val = st.agent_budget.entries.val.filter (removeKept agent) ⦄ := by
  unfold transitions.clear_agent_state
  obtain ⟨vm0, h0Eq, h0⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.taint_levels agent)
  rw [h0Eq]; simp only [bind_tc_ok]
  obtain ⟨vm1, h1Eq, h1⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.in_flight agent)
  rw [h1Eq]; simp only [bind_tc_ok]
  obtain ⟨vm2, h2Eq, h2⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.gh_taint_invoked agent)
  rw [h2Eq]; simp only [bind_tc_ok]
  obtain ⟨vm3, h3Eq, h3⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.gh_taint_received agent)
  rw [h3Eq]; simp only [bind_tc_ok]
  obtain ⟨vm4, h4Eq, h4⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.agent_instruction agent)
  rw [h4Eq]; simp only [bind_tc_ok]
  obtain ⟨vm5, h5Eq, h5⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.override_used agent)
  rw [h5Eq]; simp only [bind_tc_ok]
  obtain ⟨vm6, h6Eq, h6⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.agent_budget agent)
  rw [h6Eq]; simp only [bind_tc_ok]
  exact ⟨rfl, rfl, rfl, rfl, rfl, h0, h1, h2, h3, h4, h5, h6⟩

end ArgusLean.Refinement
