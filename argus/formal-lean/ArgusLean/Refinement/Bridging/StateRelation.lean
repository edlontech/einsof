import ArgusLean.Refinement.Bridging.Collections
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

/-- Concrete → abstract confidentiality level (the inverse of `confC`). -/
def confA : types.ConfLevel → Tzimtzum.ConfLevel
  | .Public    => .«public»
  | .Internal  => .«internal»
  | .Sensitive => .sensitive
  | .Restricted => .restricted

@[simp] theorem confC_confA (l : types.ConfLevel) : confC (confA l) = l := by cases l <;> rfl

@[simp] theorem confA_confC (l : Tzimtzum.ConfLevel) : confA (confC l) = l := by cases l <;> rfl

theorem confC_injective : Function.Injective confC :=
  fun a b h => by have := congrArg confA h; simpa using this

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

/-! ## Budget reads/writes: `budget`, `budget_exhausted`, `debit_budget`

`return_endorsed` debits the recipient's budget. The kernel reads the budget through `VecMap.get`
(last-match, absent ⇒ full = `L5`) and writes it back via `VecMap.insert` (last-match overwrite or
append). The faithful state-relation view of `agent_budget` is therefore the *get-style* read
`budgetReadC` (none ⇒ `L5`), tied to the abstract level through the bijection `budgetC`. This is the
read the kernel literally computes — it needs no key-uniqueness side condition (the removal actions'
raw-membership budget clause happens to work only because *filter* drops every duplicate key; an
insert/overwrite does not, so the get-style view is the right one here, and reconciling the two is
part of the future unified-`R` task). -/

/-- The pure debit map on `BudgetLevel`: one saturating step down (`L5→L4→…→L1→Exhausted`). -/
def debitC : types.BudgetLevel → types.BudgetLevel
  | .Exhausted => .Exhausted
  | .L1 => .Exhausted
  | .L2 => .L1
  | .L3 => .L2
  | .L4 => .L3
  | .L5 => .L4

/-- The extracted `BudgetLevel.debit` is total and equals `debitC`. -/
@[simp] theorem budgetLevel_debit_spec (b : types.BudgetLevel) :
    types.BudgetLevel.debit b = .ok (debitC b) := by cases b <;> rfl

/-- Get-style budget read: the live (last) `G`-keyed budget level, defaulting to full (`L5`) when
    `G` is absent — exactly what the kernel's `KernelState.budget` computes. -/
def budgetReadC (vm : collections.VecMap types.AgentId types.BudgetLevel) (G : types.AgentId) :
    types.BudgetLevel :=
  match vmLastEntry vm.entries.val G with
  | none => types.BudgetLevel.L5
  | some p => p.2

/-- `budgetC` is injective (a constructor-for-constructor map between the two six-element lattices),
    so `budgetReadC vm G = budgetC L` pins `L` uniquely. -/
theorem budgetC_injective : Function.Injective budgetC := by
  intro a b h; cases a <;> cases b <;> simp_all [budgetC]

/-- `KernelState.budget` computes the get-style read `budgetReadC`. -/
theorem budget_spec (st : state.KernelState) (agent : types.AgentId) :
    state.KernelState.budget st agent ⦃ b => b = budgetReadC st.agent_budget agent ⦄ := by
  unfold state.KernelState.budget
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
      agentId_eq_spec types.BudgetLevel.Insts.CoreCloneClone st.agent_budget agent)
  rw [hoEq]; simp only [bind_tc_ok]
  unfold budgetReadC
  cases hL : vmLastEntry st.agent_budget.entries.val agent with
  | none => rw [hL] at ho; subst ho; simp [types.BudgetLevel.full]
  | some p => rw [hL] at ho; subst ho; simp

/-- `budget_exhausted` is `budgetReadC = Exhausted`. -/
theorem budgetExhausted_spec (st : state.KernelState) (agent : types.AgentId) :
    state.KernelState.budget_exhausted st agent ⦃ b =>
      b = true ↔ budgetReadC st.agent_budget agent = types.BudgetLevel.Exhausted ⦄ := by
  unfold state.KernelState.budget_exhausted
  obtain ⟨bl, hblEq, hbl⟩ := spec_imp_exists (budget_spec st agent)
  rw [hblEq]; simp only [bind_tc_ok, budgetLevel_eq_spec, spec_ok, decide_eq_true_eq, hbl]

/-- `debit_budget agent` debits `agent`'s budget by one level and frames everything else: the
    post-state's get-style read maps `agent` to `debitC` of its old level, all other agents
    unchanged. The capacity bound feeds the underlying `VecMap.insert`. -/
theorem debitBudget_spec (st : state.KernelState) (agent : types.AgentId)
    (hcap : st.agent_budget.entries.val.length < Usize.max) :
    state.KernelState.debit_budget st agent ⦃ st1 =>
      st1.agent_active = st.agent_active ∧ st1.agent_parent = st.agent_parent ∧
      st1.agent_cap = st.agent_cap ∧ st1.in_flight = st.in_flight ∧
      st1.taint_levels = st.taint_levels ∧ st1.gh_taint_received = st.gh_taint_received ∧
      st1.override_used = st.override_used ∧ st1.gh_taint_invoked = st.gh_taint_invoked ∧
      st1.agent_instruction = st.agent_instruction ∧ st1.invocation_tool = st.invocation_tool ∧
      st1.tool_registered = st.tool_registered ∧
      (∀ G, budgetReadC st1.agent_budget G =
        if G = agent then debitC (budgetReadC st.agent_budget agent)
        else budgetReadC st.agent_budget G) ⦄ := by
  unfold state.KernelState.debit_budget
  obtain ⟨bl, hblEq, hbl⟩ := spec_imp_exists (budget_spec st agent)
  rw [hblEq]; simp only [bind_tc_ok, budgetLevel_debit_spec, agentId_clone_spec]
  obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.BudgetLevel.Insts.CoreCloneClone st.agent_budget agent (debitC bl) hcap)
  rw [hvmEq]; simp only [bind_tc_ok, spec_ok]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, fun G => ?_⟩
  show budgetReadC vm G = _
  by_cases hG : G = agent
  · have hread : budgetReadC vm G = debitC bl := by unfold budgetReadC; rw [hvm G, if_pos hG]
    rw [hread, hbl, hG]; simp
  · have hread : budgetReadC vm G = budgetReadC st.agent_budget G := by
      unfold budgetReadC; rw [hvm G, if_neg hG]
    rw [hread, if_neg hG]

end ArgusLean.Refinement
