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

/-- The abstract TzimtzumV2 state at the kernel's concrete sorts. `ConfLevel` is a concrete
    inductive baked into `St` (the numeric budget is a plain `Nat`); the remaining seven sorts are the
    extracted `String`/inductive types. -/
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

/-! ## Confidentiality correspondence

`ConfLevel` is a baked-in inductive of the abstract `St` (not a type parameter), so the taint
fields cross from the abstract lattice to the extracted `types.*` lattice. The two are
constructor-for-constructor identical; `confC` / `confA` are the obvious total maps. (The budget is
now a plain `Nat`/`u8` numeric cell — no level map; see the budget section below.) -/

/-- Abstract → concrete confidentiality level. -/
def confC : Tzimtzum.ConfLevel → types.ConfLevel
  | .«public»   => .Public
  | .«internal» => .Internal
  | .sensitive  => .Sensitive
  | .restricted => .Restricted

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

`clear_agent_state st agent` deletes `agent`'s key from the eight per-agent maps
(`taint_levels`, `in_flight`, `gh_taint_invoked`, `gh_taint_received`, `agent_instruction`,
`override_used`, `flow_override`, `agent_budget`) and frames everything else. Each delete is a
`VecMap.remove`,
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
      st1.flow_override.entries.val = st.flow_override.entries.val.filter (removeKept agent) ∧
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
      st.flow_override agent)
  rw [h6Eq]; simp only [bind_tc_ok]
  obtain ⟨vm7, h7Eq, h7⟩ := spec_imp_exists
    (vecMapRemove_spec _ types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec _
      st.agent_budget agent)
  rw [h7Eq]; simp only [bind_tc_ok]
  exact ⟨rfl, rfl, rfl, rfl, rfl, h0, h1, h2, h3, h4, h5, h6, h7⟩

/-! ## Budget reads/writes: `budget`, `affordable`, `debit_budget`, `credit_budget`

The declassification meter is now a numeric `u8` cell (Campaign B). The kernel reads the budget
through `VecMap.get` (last-match, absent ⇒ full = `BUDGET_CAPACITY = 16`), tests affordability with
`>=`, and writes it back via `VecMap.insert` after a saturating `u8` step: `debit_budget` subtracts a
sensitivity weight `w` (`saturating_sub`), `credit_budget` adds `n` then caps at `BUDGET_CAPACITY`
(`saturating_add` then `min`). The faithful state-relation view of `agent_budget` is therefore the
*get-style* read `budgetReadC` (none ⇒ `16`) — the read the kernel literally computes, needing no
key-uniqueness side condition. The post-values are stated with the same saturating ops the kernel
runs; `scalar_tac`/`omega` discharge the `u8`↔`Nat` arithmetic downstream. -/

/-- Get-style budget read: the live (last) `G`-keyed budget cell, defaulting to full
    (`BUDGET_CAPACITY = 16`) when `G` is absent — exactly what the kernel's `KernelState.budget`
    computes. -/
def budgetReadC (vm : collections.VecMap types.AgentId Std.U8) (G : types.AgentId) : Std.U8 :=
  match vmLastEntry vm.entries.val G with
  | none => types.BUDGET_CAPACITY
  | some p => p.2

/-- The kernel's `BUDGET_CAPACITY` cell (`16#u8`) carries the abstract `budget_capacity = 16` as its
    `Nat` value. Both sides are `@[irreducible]` literals, so `simp` (not `rfl`) discharges them. The
    bridge for the "absent ⇒ full" budget convention (delegate grantee, init root). -/
@[simp] theorem budgetCapacity_val : (types.BUDGET_CAPACITY).val = Tzimtzum.budget_capacity := by
  simp [types.BUDGET_CAPACITY, Tzimtzum.budget_capacity]

/-- The `Nat` value of a saturating `u8` subtraction is the (clamped-at-0) `Nat` subtraction. The
    numeric bridge that lets the abstract `b - w` (`Nat`) debit match the kernel's `saturating_sub`
    over the `u8` budget cell; `omega` then collapses the abstract/concrete budget posts. -/
@[simp] theorem saturatingSub_val (x w : Std.U8) :
    (core.num.U8.saturating_sub x w).val = x.val - w.val := by
  have hx : x.bv.toNat < 256 := x.bv.isLt
  show (BitVec.ofNat (UScalarTy.U8.numBits) (max 0 (x.bv.toNat - w.bv.toNat))).toNat = x.bv.toNat - w.bv.toNat
  rw [BitVec.toNat_ofNat]
  have hlt : (max 0 (x.bv.toNat - w.bv.toNat)) < 2 ^ 8 := by omega
  rw [show (2 : Nat) ^ (UScalarTy.U8.numBits) = 2 ^ 8 from rfl, Nat.mod_eq_of_lt hlt]
  omega

/-- The `Nat` value of a `u8` `saturating_add` then `min BUDGET_CAPACITY` is the saturating credit
    `min budget_capacity (x.val + n.val)`. Bridges the kernel's `credit_budget` write to the abstract
    `budget_saturating_credit`. -/
@[simp] theorem saturatingAddMin_val (x n : Std.U8) :
    (core.cmp.impls.OrdU8.min (core.num.U8.saturating_add x n) types.BUDGET_CAPACITY).val
      = min Tzimtzum.budget_capacity (x.val + n.val) := by
  have hx : x.bv.toNat < 256 := x.bv.isLt
  have hn : n.bv.toNat < 256 := n.bv.isLt
  have hmax : (UScalar.max UScalarTy.U8) = 255 := by
    rw [UScalar.max_UScalarTy_U8_eq, U8.max_eq]
  have hadd : (core.num.U8.saturating_add x n).val = min (x.val + n.val) 255 := by
    show (BitVec.ofNat (UScalarTy.U8.numBits)
        (min (UScalar.max UScalarTy.U8) (x.bv.toNat + n.bv.toNat))).toNat = min (x.val + n.val) 255
    rw [BitVec.toNat_ofNat, hmax]
    have hb : min 255 (x.bv.toNat + n.bv.toNat) < 2 ^ 8 := by omega
    rw [show (2 : Nat) ^ (UScalarTy.U8.numBits) = 2 ^ 8 from rfl, Nat.mod_eq_of_lt hb]
    show min 255 (x.bv.toNat + n.bv.toNat) = min (x.bv.toNat + n.bv.toNat) 255
    omega
  rw [core.cmp.impls.OrdU8.min_val, hadd, budgetCapacity_val, Tzimtzum.budget_capacity]
  omega

/-- `KernelState.budget` computes the get-style read `budgetReadC`. -/
theorem budget_spec (st : state.KernelState) (agent : types.AgentId) :
    state.KernelState.budget st agent ⦃ b => b = budgetReadC st.agent_budget agent ⦄ := by
  unfold state.KernelState.budget
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
      agentId_eq_spec core.clone.CloneU8 st.agent_budget agent)
  rw [hoEq]; simp only [bind_tc_ok]
  unfold budgetReadC
  cases hL : vmLastEntry st.agent_budget.entries.val agent with
  | none => rw [hL] at ho; subst ho; simp
  | some p => rw [hL] at ho; subst ho; simp

/-- `affordable agent w` is the concrete affordability test `w ≤ budgetReadC agent`. The abstract
    `∃ b, agent_budget a b ∧ w ≤ b` connection is made downstream (via `R`'s budget clause +
    `active_has_budget`); here we only bridge the concrete side, built on `budget_spec`. -/
theorem affordable_spec (st : state.KernelState) (agent : types.AgentId) (w : Std.U8) :
    state.KernelState.affordable st agent w ⦃ r =>
      r = true ↔ w ≤ budgetReadC st.agent_budget agent ⦄ := by
  unfold state.KernelState.affordable
  obtain ⟨b, hbEq, hb⟩ := spec_imp_exists (budget_spec st agent)
  rw [hbEq]; simp only [bind_tc_ok, spec_ok, hb, ge_iff_le, decide_eq_true_eq]

/-- `debit_budget agent w` subtracts the sensitivity weight `w` from `agent`'s budget cell
    (saturating at `0`) and frames everything else: the post-state's get-style read maps `agent` to
    `saturating_sub` of its old cell, all other agents unchanged. The capacity bound feeds the
    underlying `VecMap.insert`. -/
theorem debitBudget_spec (st : state.KernelState) (agent : types.AgentId) (w : Std.U8)
    (hcap : st.agent_budget.entries.val.length < Usize.max) :
    state.KernelState.debit_budget st agent w ⦃ st1 =>
      st1.agent_active = st.agent_active ∧ st1.agent_parent = st.agent_parent ∧
      st1.agent_cap = st.agent_cap ∧ st1.in_flight = st.in_flight ∧
      st1.taint_levels = st.taint_levels ∧ st1.gh_taint_received = st.gh_taint_received ∧
      st1.override_used = st.override_used ∧ st1.gh_taint_invoked = st.gh_taint_invoked ∧
      st1.agent_instruction = st.agent_instruction ∧ st1.invocation_tool = st.invocation_tool ∧
      st1.tool_registered = st.tool_registered ∧ st1.flow_override = st.flow_override ∧
      (∀ G, budgetReadC st1.agent_budget G =
        if G = agent then core.num.U8.saturating_sub (budgetReadC st.agent_budget agent) w
        else budgetReadC st.agent_budget G) ⦄ := by
  unfold state.KernelState.debit_budget
  obtain ⟨b, hbEq, hb⟩ := spec_imp_exists (budget_spec st agent)
  rw [hbEq]; simp only [bind_tc_ok, core.num.U8.saturating_sub, lift, agentId_clone_spec]
  obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      core.clone.CloneU8 st.agent_budget agent (UScalar.saturating_sub b w) hcap)
  rw [hvmEq]; simp only [bind_tc_ok, spec_ok]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, fun G => ?_⟩
  show budgetReadC vm G = _
  by_cases hG : G = agent
  · have hread : budgetReadC vm G = UScalar.saturating_sub b w := by
      unfold budgetReadC; rw [hvm G, if_pos hG]
    rw [hread, hb, hG, if_pos rfl]
  · have hread : budgetReadC vm G = budgetReadC st.agent_budget G := by
      unfold budgetReadC; rw [hvm G, if_neg hG]
    rw [hread, if_neg hG]

/-- `credit_budget agent n` adds `n` to `agent`'s budget cell (saturating at `255`) then caps it at
    `BUDGET_CAPACITY = 16`, framing everything else: the post-state's get-style read maps `agent` to
    `min (saturating_add old n) BUDGET_CAPACITY`, all other agents unchanged. The capacity bound feeds
    the underlying `VecMap.insert`. -/
theorem creditBudget_spec (st : state.KernelState) (agent : types.AgentId) (n : Std.U8)
    (hcap : st.agent_budget.entries.val.length < Usize.max) :
    state.KernelState.credit_budget st agent n ⦃ st1 =>
      st1.agent_active = st.agent_active ∧ st1.agent_parent = st.agent_parent ∧
      st1.agent_cap = st.agent_cap ∧ st1.in_flight = st.in_flight ∧
      st1.taint_levels = st.taint_levels ∧ st1.gh_taint_received = st.gh_taint_received ∧
      st1.override_used = st.override_used ∧ st1.gh_taint_invoked = st.gh_taint_invoked ∧
      st1.agent_instruction = st.agent_instruction ∧ st1.invocation_tool = st.invocation_tool ∧
      st1.tool_registered = st.tool_registered ∧ st1.flow_override = st.flow_override ∧
      (∀ G, budgetReadC st1.agent_budget G =
        if G = agent then
          core.cmp.impls.OrdU8.min (core.num.U8.saturating_add (budgetReadC st.agent_budget agent) n)
            types.BUDGET_CAPACITY
        else budgetReadC st.agent_budget G) ⦄ := by
  unfold state.KernelState.credit_budget
  obtain ⟨b, hbEq, hb⟩ := spec_imp_exists (budget_spec st agent)
  rw [hbEq]
  simp only [bind_tc_ok, core.num.U8.saturating_add, lift, agentId_clone_spec]
  obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec core.clone.CloneU8 st.agent_budget
      agent (core.cmp.impls.OrdU8.min (UScalar.saturating_add b n) types.BUDGET_CAPACITY) hcap)
  rw [hvmEq]; simp only [bind_tc_ok, spec_ok]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, fun G => ?_⟩
  show budgetReadC vm G = _
  by_cases hG : G = agent
  · have hread : budgetReadC vm G =
        core.cmp.impls.OrdU8.min (UScalar.saturating_add b n) types.BUDGET_CAPACITY := by
      unfold budgetReadC; rw [hvm G, if_pos hG]
    rw [hread, hb, hG, if_pos rfl]
  · have hread : budgetReadC vm G = budgetReadC st.agent_budget G := by
      unfold budgetReadC; rw [hvm G, if_neg hG]
    rw [hread, if_neg hG]

end ArgusLean.Refinement
