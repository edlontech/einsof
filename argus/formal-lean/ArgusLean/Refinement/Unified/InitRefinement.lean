import ArgusLean.Refinement.Unified.Relation

/-! # Layer 2 — init refinement

The extracted initial state `state.KernelState.initial` relates, under the unified `R`, to an abstract
TzimtzumV2 state satisfying `Tzimtzum.initial`. This is the base case of the forward-simulation
induction (`reachable_concrete_safe`).

The only non-trivial concrete fact is that the `all_caps` build loop populates the root agent's
capability set with *every* `CapKind` (so the abstract `agent_cap A C ↔ A = root` view is faithful):
`initialCaps_loop_spec` establishes it by the `loop.spec_decr_nat` invariant `ac = ALL.take i`. Every
other field of the extracted `initial` is an empty `VecMap`/`VecSet`, plus the singleton-root
`agent_active` insert. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- `CapKind.ALL` enumerates every capability (so the root's full cap set abstracts to "holds every
    capability"). -/
theorem capKindAll_complete (C : capability.CapKind) : C ∈ capability.CapKind.ALL.val := by
  cases C <;> simp [capability.CapKind.ALL, Array.make]

/-- `CapKind.ALL` lists each capability once (so its prefix-extend in the build loop is an append). -/
theorem capKindAll_nodup : capability.CapKind.ALL.val.Nodup := by
  simp only [capability.CapKind.ALL, Array.make]; decide

/-- The `all_caps` build loop populates the set with exactly the `take i0` prefix of `CapKind.ALL`;
    on exit (`i = 17`) that is the whole enumeration, so the result holds every `CapKind`. -/
theorem initialCaps_loop_spec (all_caps : collections.VecSet capability.CapKind) (i0 : Usize)
    (hi0 : i0.val ≤ capability.CapKind.ALL.val.length)
    (hacc : all_caps.items.val = capability.CapKind.ALL.val.take i0.val) :
    state.KernelState.initial_loop all_caps i0 ⦃ vs => ∀ C : capability.CapKind, C ∈ vs.items.val ⦄ := by
  unfold state.KernelState.initial_loop
  apply loop.spec_decr_nat
    (measure := fun p => capability.CapKind.ALL.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ capability.CapKind.ALL.val.length ∧
        p.1.items.val = capability.CapKind.ALL.val.take p.2.val)
  · rintro ⟨ac, i⟩ ⟨hile, hacc'⟩
    simp only [state.KernelState.initial_loop.body]
    dsimp only at hile hacc' ⊢
    step*
    · -- cont: insert ALL[i], re-establish the prefix invariant
      have hilt : i.val < capability.CapKind.ALL.val.length := by
        have h := ‹i < s.len›
        simp only [s_post, Slice.len, Array.to_slice] at h; scalar_tac
      have hck_notin : ck ∉ ac.items.val := by
        rw [hacc', ck_post]; exact getElem_not_mem_take capKindAll_nodup hilt
      obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
        (vecSetContains_spec capability.CapKind.Insts.CoreCloneClone
          capability.CapKind.Insts.CoreCmpPartialEqCapKind capKind_eq_spec ac ck)
      have hbfalse : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd (hbIff.mp rfl) hck_notin
      have hcap : ac.items.val.length < Usize.max := by
        rw [hacc', List.length_take]; scalar_tac
      unfold collections.VecSet.insert
      rw [hbEq]
      simp only [hbfalse, Bool.false_eq_true, if_false, bind_tc_ok]
      obtain ⟨v, hvEq, hvval⟩ := spec_imp_exists (alloc.vec.Vec.push_spec ac.items ck hcap)
      rw [hvEq]
      simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      show v.val = capability.CapKind.ALL.val.take _
      rw [hvval, hacc', ck_post, i2_post,
        List.take_add_one, List.getElem?_eq_getElem hilt, Option.toList_some]
    · -- done: i = 17, prefix = whole enumeration, every CapKind present
      rename_i hlt
      have hlen : i.val = capability.CapKind.ALL.val.length := by
        simp only [s_post, Slice.len, Array.to_slice] at hlt; scalar_tac
      intro C
      rw [hacc', hlen, List.take_length]
      exact capKindAll_complete C
  · exact ⟨hi0, hacc⟩

/-- The extracted `all_caps` build (loop from the empty set) yields a set holding every capability. -/
theorem initialCaps_spec :
    state.KernelState.initial_loop
      { items := alloc.vec.Vec.new capability.CapKind } 0#usize ⦃ vs =>
      ∀ C : capability.CapKind, C ∈ vs.items.val ⦄ :=
  initialCaps_loop_spec _ 0#usize (by simp) (by simp)

/-- Field characterisation of the extracted initial state: the root is named, `agent_active` is the
    singleton `{root}`, `agent_cap` maps the root to the (complete) capability set and is key-unique,
    and every other field is empty. -/
theorem init_chars (c0 : state.KernelState) (hc0 : state.KernelState.initial = .ok c0) :
    ∃ root : types.AgentId,
      types.AgentId.root = .ok root ∧
      (∀ y, vsMem c0.agent_active y ↔ y = root) ∧
      (∀ N C, vmsMemLast c0.agent_cap N C ↔ N = root) ∧
      vmNodupKeys c0.agent_cap ∧
      c0.agent_parent.entries.val = [] ∧ c0.taint_levels.entries.val = [] ∧
      c0.integ_levels.entries.val = [] ∧
      c0.in_flight.entries.val = [] ∧ c0.invocation_tool.entries.val = [] ∧
      c0.invocation_used.items.val = [] ∧ c0.invocation_egress.entries.val = [] ∧
      c0.tool_registered.items.val = [] ∧ c0.agent_instruction.entries.val = [] ∧
      c0.override_used.entries.val = [] ∧ c0.flow_override.entries.val = [] ∧
      c0.agent_budget.entries.val = [] := by
  simp only [state.KernelState.initial, collections.VecSet.new, collections.VecMap.new,
    bind_tc_ok] at hc0
  obtain ⟨root, hroot⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hc0; simp at hc0
    | div => rw [h] at hc0; simp at hc0
  rw [hroot] at hc0
  simp only [bind_tc_ok] at hc0
  obtain ⟨acs, hacsEq, hacsMem⟩ := spec_imp_exists initialCaps_spec
  rw [hacsEq] at hc0
  simp only [agentId_clone_spec, bind_tc_ok] at hc0
  obtain ⟨aa, haaEq, haaMem⟩ := spec_imp_exists
    (vecSetInsert_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
      agentId_eq_spec { items := alloc.vec.Vec.new types.AgentId } root (by simp; scalar_tac))
  rw [haaEq] at hc0
  simp only [bind_tc_ok] at hc0
  obtain ⟨acap, hacapEq, hacapLast⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      { entries := alloc.vec.Vec.new (types.AgentId × collections.VecSet capability.CapKind) }
      root acs (by simp; scalar_tac))
  obtain ⟨acapN, hacapNEq, hacapNd⟩ := spec_imp_exists
    (vecMapInsert_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      { entries := alloc.vec.Vec.new (types.AgentId × collections.VecSet capability.CapKind) }
      root acs (by simp; scalar_tac))
  have hsame : acapN = acap := Result.ok.inj (hacapNEq.symm.trans hacapEq)
  rw [hacapEq] at hc0
  simp only [bind_tc_ok, Result.ok.injEq] at hc0
  subst hc0
  refine ⟨root, hroot, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro y; rw [haaMem y]; simp [vsMem]
  · intro N C
    show vmsMemLast acap N C ↔ N = root
    unfold vmsMemLast
    rw [hacapLast N]
    by_cases hN : N = root
    · simp [hN, hacsMem C]
    · simp [hN, vmLastEntry]
  · show vmNodupKeys acap
    rw [← hsame]; exact hacapNd (by simp [vmNodupKeys])

/-- The abstract initial state at the kernel's concrete sorts: the mutable fields per `Tzimtzum.initial`
    (only the root active, holding every capability and full budget), the immutable background fields
    read off `bg` exactly as `R` requires, and the four runtime-oracle fields set to the given
    relations (those are not constrained by `R` — they relate to the `Kernel` oracle params). The
    `return_conforms` oracle (Campaign B P2) takes its own `(child, parent)`-keyed relation `rcRel`. -/
noncomputable def absInitial (bg : background.BackgroundTheory) (root : types.AgentId)
    (cgRel auRel cfRel : types.InvocationId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop)
    (egRel : types.InvocationId → types.EgressKind → Prop) : AbsState where
  agent_active := fun A => A = root
  agent_parent := fun _ _ => False
  agent_cap := fun A _ => A = root
  agent_instruction := fun _ _ => False
  taint_levels := fun _ _ => False
  integ_levels := fun _ _ => False
  agent_budget := fun _ => Tzimtzum.budget_capacity
  in_flight := fun _ _ => False
  invocation_used := fun _ => False
  tool_registered := fun _ => False
  override_used := fun _ _ _ => False
  tool_cap := fun t C => ∃ tm, toolMetaC bg t = some tm ∧ C ∈ tm.capabilities.items.val
  tool_egress := fun T E => E ∈ egItems bg T
  tool_conf_floor := fun t => match toolMetaC bg t with
    | some tm => confA tm.conf_floor
    | none => Tzimtzum.ConfLevel.«public»
  tool_integ_floor := fun t => match toolMetaC bg t with
    | some tm => integA tm.integ_floor
    | none => Tzimtzum.IntegLevel.untrusted
  tool_integ_inspect_floor := fun t => match toolMetaC bg t with
    | some tm => integA tm.integ_inspect_floor
    | none => Tzimtzum.IntegLevel.untrusted
  tool_output_integ := fun t => match toolMetaC bg t with
    | some tm => integA tm.output_integ
    | none => Tzimtzum.IntegLevel.untrusted
  lever_integ_floor := integA bg.lever_integ_floor
  lever_integ_inspect_floor := integA bg.lever_integ_inspect_floor
  tool_output_bounded := fun t => ∃ tm, toolMetaC bg t = some tm ∧ tm.output_bounded = true
  tool_issuer := fun t => match toolMetaC bg t with | some tm => tm.issuer | none => default
  trusted_issuer := fun i => vsMem bg.trusted_issuers i
  invocation_conforms := cfRel
  return_conforms := rcRel
  instruction_issuer := fun i => match background.BackgroundTheory.impl.instruction_issuer bg i with
    | .ok (some iss) => iss
    | _ => default
  egress_allow_ceiling := fun E => (ceilC bg.allow_ceiling E).map confA
  egress_inspect_ceiling := fun E => (ceilC bg.inspect_ceiling E).map confA
  flow_override := fun _ _ _ => False
  invocation_authorized := auRel
  invocation_gate_passes := cgRel
  invocation_tool := fun _ => default
  invocation_egress := egRel
  root_agent := root
  cap_declassify := capability.CapKind.Declassify
  cap_credit_budget := capability.CapKind.CreditBudget
  cap_grant_override := capability.CapKind.GrantOverride

/-- **Init refinement.** The extracted initial state relates, under the unified `R`, to `absInitial`,
    which satisfies `Tzimtzum.initial`. The runtime-oracle relations are free parameters (the caller
    supplies the abstract oracle interpretation that the fidelity hypothesis pins to reality). -/
theorem init_refines (bg : background.BackgroundTheory)
    (cgRel auRel cfRel : types.InvocationId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (c0 : state.KernelState) (hc0 : state.KernelState.initial = .ok c0) :
    ∃ a0 : AbsState, Tzimtzum.initial a0 ∧ R c0 bg a0 ∧
      a0.invocation_gate_passes = cgRel ∧ a0.invocation_authorized = auRel ∧
      a0.invocation_conforms = cfRel ∧ a0.return_conforms = rcRel := by
  obtain ⟨root, hroot, hactive, hcap, hcapNd, hpar, htaint, hinteg, hinf, hinv, hused, hegr,
    htool, hinstr, hovr, hflow, hbud⟩ := init_chars c0 hc0
  refine ⟨absInitial bg root cgRel auRel cfRel rcRel egRel, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · -- Tzimtzum.initial (12 conjuncts, all definitional at `absInitial`)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [absInitial]
  · -- R (41 conjuncts)
    refine ⟨hroot, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; exact (hactive x).symm
    · intro t; simp [absInitial, vsMem, htool]
    · intro C P; simp [absInitial, hpar, vmLastEntry]
    · intro N C; exact (hcap N C).symm
    · intro ag ins; simp [absInitial, vmsMemLast, hinstr, vmLastEntry]
    · intro ag L; simp [absInitial, vmsMemLast, htaint, vmLastEntry]
    · intro ag L; simp [absInitial, vmsMemLast, hinteg, vmLastEntry]
    · intro ag I; simp [absInitial, vmsMemLast, hinf, vmLastEntry]
    · intro ag t L; simp [absInitial, vmsMemLast, hovr, vmLastEntry]
    · -- budget: capacity everywhere, both sides
      intro G
      simp [absInitial, budgetReadC, hbud, vmLastEntry]
    · -- invocation_used: both empty
      intro I; simp [absInitial, vsMem, hused]
    · -- invocation_egress: vacuous (nothing used)
      intro I hI; exact absurd hI (by simp [absInitial])
    · intro t tmeta C htm
      simp only [absInitial]
      constructor
      · rintro ⟨tm, htm2, hC⟩; rw [htm, Option.some.injEq] at htm2; subst htm2; exact hC
      · intro hC; exact ⟨tmeta, htm, hC⟩
    · intro T E; exact Iff.rfl
    · intro t tmeta htm; simp only [absInitial, htm]
    · intro t tmeta htm; simp only [absInitial, htm]
    · intro t tmeta htm; simp only [absInitial, htm]
    · intro t tmeta htm; simp only [absInitial, htm]
    · intro t tmeta htm
      simp only [absInitial]
      constructor
      · rintro ⟨tm, htm2, hb⟩; rw [htm, Option.some.injEq] at htm2; subst htm2; exact hb
      · intro hb; exact ⟨tmeta, htm, hb⟩
    · intro t tmeta htm; simp only [absInitial, htm]
    · intro i; exact Iff.rfl
    · intro i issuer hii; simp only [absInitial, hii]
    · intro L E
      show Tzimtzum.St.flow_allows _ L E ↔ _
      simp only [Tzimtzum.St.flow_allows, absInitial]
      exact ceilingAdmits_mapA_iff bg.allow_ceiling L E
    · intro L E
      show Tzimtzum.St.flow_inspects _ L E ↔ _
      simp only [Tzimtzum.St.flow_inspects, absInitial]
      exact ceilingAdmits_mapA_iff bg.inspect_ceiling L E
    · intro A T L
      simp only [absInitial, false_iff]
      rintro ⟨vs, hvs, _⟩; rw [hflow] at hvs; simp [vmLastEntry] at hvs
    · intro I t hIt; simp [invToolC, hinv, vmLastEntry] at hIt
    · simp [vmNodupKeys, hpar]
    · exact hcapNd
    · simp [vmNodupKeys, hinstr]
    · simp [vmNodupKeys, htaint]
    · simp [vmNodupKeys, hinteg]
    · simp [vmNodupKeys, hinf]
    · simp [vmNodupKeys, hovr]
    · simp [vmNodupKeys, hflow]
    · simp [vmNodupKeys, hbud]
    · intro ag I hmem; simp [vmsMemLast, hinf, vmLastEntry] at hmem

end ArgusLean.Refinement
