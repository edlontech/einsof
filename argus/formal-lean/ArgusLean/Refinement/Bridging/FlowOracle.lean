import ArgusLean.Refinement.Bridging.FlowBridging

/-! # Refinement — flow-oracle reads for the egress-gated actions

The concrete-only oracle reads the egress-gated actions (`return_unendorsed`, `sentinel_elevate_taint`)
perform, pinned to their faithful values so they can feed `flowDecision_spec` / `gateEgress_spec`:

* `flowMode_spec` — `flow_mode` is total (two ceiling `VecMap.get_cloned` reads, absent = deny);
  `flowModeC` is its pure value, characterised per-mode by `flowModeC_allow_iff` /
  `flowModeC_inspect_iff` / `flowModeC_deny_iff` over the pure band test `ceilAdmitsC`.
* `hasFlowOverride_spec` — `has_flow_override` is the last-match nested membership of the
  `(tool, level)` `OverrideKey` in the agent's `flow_override` set (state-side since Campaign A;
  the exact `override_consumed` shape).
* `overrideConsumed_spec` — `override_consumed` is the last-match nested membership of the
  `(tool, level)` `OverrideKey` in the agent's `override_used` set (`vmsMemLast`).

Plus the supporting `EgressKind` / `OverrideKey` / `FlowMode` / `ConfLevel.le` decidable facts —
all *proved* (nullary enums / structs of them), no extractor trust beyond the `String` ids. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## `EgressKind` / `OverrideKey` / `FlowMode` equality and clone, `ConfLevel.le` -/

deriving instance DecidableEq for types.EgressKind

/-- `EgressKind.eq` faithful decidable equality (nullary enum). -/
@[simp] theorem egressKind_eq_spec (a b : types.EgressKind) :
    types.EgressKind.Insts.CoreCmpPartialEqEgressKind.eq a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp [types.EgressKind.Insts.CoreCmpPartialEqEgressKind.eq, types.EgressKind.read_discriminant]

/-- The pure rank-compare behind `ConfLevel::le` (the kernel's trait-free total order). -/
def confLeC (a b : types.ConfLevel) : Bool :=
  match a, b with
  | .Public, _ => true
  | .Internal, .Public => false
  | .Internal, _ => true
  | .Sensitive, .Public => false
  | .Sensitive, .Internal => false
  | .Sensitive, _ => true
  | .Restricted, .Restricted => true
  | .Restricted, _ => false

/-- `ConfLevel.le` is total and computes `confLeC` (16-case rank compare). -/
@[simp] theorem confLevel_le_spec (a b : types.ConfLevel) :
    types.ConfLevel.le a b = .ok (confLeC a b) := by
  cases a <;> cases b <;> rfl

/-- `OverrideKey.clone` is the identity (field-wise). -/
@[simp] theorem overrideKey_clone_spec (a : types.OverrideKey) :
    types.OverrideKey.Insts.CoreCloneClone.clone a = .ok a := by
  obtain ⟨a1, a2⟩ := a
  simp only [types.OverrideKey.Insts.CoreCloneClone.clone, toolId_clone_spec, confLevel_clone_spec,
    bind_tc_ok]

/-! ## `tool_metadata` -/

/-- `EgressKind.clone` is the identity (nullary enum). -/
@[simp] theorem egressKind_clone_spec (a : types.EgressKind) :
    types.EgressKind.Insts.CoreCloneClone.clone a = .ok a := rfl

/-- `ToolMetadata.clone` is the identity (every field's clone is). -/
@[simp] theorem toolMetadata_clone_spec (m : background.ToolMetadata) :
    background.ToolMetadata.Insts.CoreCloneClone.clone m = .ok m := by
  obtain ⟨caps, eg, cf, ob, iss⟩ := m
  simp only [background.ToolMetadata.Insts.CoreCloneClone.clone,
    vecSetClone_spec capability.CapKind.Insts.CoreCloneClone capKind_clone_spec,
    vecSetClone_spec types.EgressKind.Insts.CoreCloneClone egressKind_clone_spec,
    confLevel_clone_spec, issuerId_clone_spec, bind_tc_ok]
  rfl

/-- The pure value of `tool_metadata`: the live (last) `tool`-keyed metadata, or `none`. -/
def toolMetaC (bg : background.BackgroundTheory) (tool : types.ToolId) :
    Option background.ToolMetadata :=
  (vmLastEntry bg.tools.entries.val tool).map Prod.snd

/-- `tool_metadata` computes `toolMetaC` (a last-match `VecMap.get_cloned`, clone is identity). -/
theorem toolMetadata_spec (bg : background.BackgroundTheory) (tool : types.ToolId) :
    background.BackgroundTheory.tool_metadata bg tool ⦃ o => o = toolMetaC bg tool ⦄ := by
  unfold background.BackgroundTheory.tool_metadata
  exact vecMapGetCloned_spec types.ToolId.Insts.CoreCloneClone
    types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec
    background.ToolMetadata.Insts.CoreCloneClone toolMetadata_clone_spec bg.tools tool

/-! ## `flow_mode` (two-ceiling band compute) -/

/-- The live ceiling for `E` in a per-egress ceiling map (last-match `get_cloned` read). -/
def ceilC (m : collections.VecMap types.EgressKind types.ConfLevel) (E : types.EgressKind) :
    Option types.ConfLevel :=
  (vmLastEntry m.entries.val E).map Prod.snd

/-- The pure band test: `level` is at or below `E`'s ceiling (absent ceiling admits nothing). -/
def ceilAdmitsC (m : collections.VecMap types.EgressKind types.ConfLevel)
    (level : types.ConfLevel) (E : types.EgressKind) : Bool :=
  match ceilC m E with
  | none => false
  | some c => confLeC level c

/-- The pure value of `flow_mode`: ALLOW iff the allow band admits, else INSPECT iff the inspect
    band admits, else DENY. -/
def flowModeC (bg : background.BackgroundTheory) (level : types.ConfLevel) (E : types.EgressKind) :
    background.FlowMode :=
  if ceilAdmitsC bg.allow_ceiling level E then background.FlowMode.Allow
  else if ceilAdmitsC bg.inspect_ceiling level E then background.FlowMode.Inspect
  else background.FlowMode.Deny

/-- `flow_mode` is total and computes `flowModeC`. -/
theorem flowMode_spec (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    background.BackgroundTheory.flow_mode bg level E ⦃ fm => fm = flowModeC bg level E ⦄ := by
  unfold background.BackgroundTheory.flow_mode
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.EgressKind.Insts.CoreCloneClone
      types.EgressKind.Insts.CoreCmpPartialEqEgressKind egressKind_eq_spec
      types.ConfLevel.Insts.CoreCloneClone confLevel_clone_spec bg.allow_ceiling E)
  rw [hoEq]; simp only [bind_tc_ok]
  obtain ⟨o1, ho1Eq, ho1⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.EgressKind.Insts.CoreCloneClone
      types.EgressKind.Insts.CoreCmpPartialEqEgressKind egressKind_eq_spec
      types.ConfLevel.Insts.CoreCloneClone confLevel_clone_spec bg.inspect_ceiling E)
  unfold flowModeC ceilAdmitsC ceilC
  rw [← ho, ← ho1]
  cases o with
  | none =>
    simp only [Bool.false_eq_true, if_false, bind_tc_ok]
    rw [ho1Eq]; simp only [bind_tc_ok]
    cases o1 with
    | none => simp
    | some c1 => simp only [confLevel_le_spec, bind_tc_ok]; split <;> simp_all
  | some c =>
    simp only [confLevel_le_spec, bind_tc_ok]
    by_cases hle : confLeC level c
    · simp [hle]
    · simp only [hle, Bool.false_eq_true, if_false, bind_tc_ok]
      rw [ho1Eq]; simp only [bind_tc_ok]
      cases o1 with
      | none => simp
      | some c1 => simp only [confLevel_le_spec, bind_tc_ok]; split <;> simp_all

/-! ### Per-mode characterisations (the R-clause mediators)

The abstract gates are band tests (`flow_allows` = allow band, `flow_inspects` = inspect band,
independently); the kernel's `FlowMode` is the prioritised three-way split. These three iffs are
the only facts the sims need to cross between the two. -/

theorem flowModeC_allow_iff (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    flowModeC bg level E = background.FlowMode.Allow ↔
      ceilAdmitsC bg.allow_ceiling level E = true := by
  unfold flowModeC
  by_cases ha : ceilAdmitsC bg.allow_ceiling level E <;>
    by_cases hi : ceilAdmitsC bg.inspect_ceiling level E <;> simp [ha, hi]

theorem flowModeC_inspect_iff (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    flowModeC bg level E = background.FlowMode.Inspect ↔
      (ceilAdmitsC bg.allow_ceiling level E = false ∧
       ceilAdmitsC bg.inspect_ceiling level E = true) := by
  unfold flowModeC
  by_cases ha : ceilAdmitsC bg.allow_ceiling level E <;>
    by_cases hi : ceilAdmitsC bg.inspect_ceiling level E <;> simp [ha, hi]

theorem flowModeC_deny_iff (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    flowModeC bg level E = background.FlowMode.Deny ↔
      (ceilAdmitsC bg.allow_ceiling level E = false ∧
       ceilAdmitsC bg.inspect_ceiling level E = false) := by
  unfold flowModeC
  by_cases ha : ceilAdmitsC bg.allow_ceiling level E <;>
    by_cases hi : ceilAdmitsC bg.inspect_ceiling level E <;> simp [ha, hi]

/-- Equational form of `flowMode_spec`, for feeding `gateEgress_spec`'s `hfmOf`. -/
theorem flowMode_eq (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    background.BackgroundTheory.flow_mode bg level E = .ok (flowModeC bg level E) := by
  obtain ⟨fm, h1, h2⟩ := spec_imp_exists (flowMode_spec bg level E); rw [← h2]; exact h1

/-! ## `has_flow_override` (state-side since Campaign A — the `override_consumed` twin) -/

/-- `has_flow_override agent tool level` is the last-match nested membership of the `(tool, level)`
    `OverrideKey` in `agent`'s `flow_override` grant set. -/
theorem hasFlowOverride_spec (st : state.KernelState) (agent : types.AgentId)
    (tool : types.ToolId) (level : types.ConfLevel) :
    state.KernelState.has_flow_override st agent tool level ⦃ b =>
      b = true ↔ vmsMemLast st.flow_override agent { tool := tool, level := level } ⦄ := by
  unfold state.KernelState.has_flow_override
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      (collections.VecSet.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCloneClone)
      st.flow_override agent)
  rw [hoEq]; simp only [bind_tc_ok]
  cases hL : vmLastEntry st.flow_override.entries.val agent with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho
    simp only [spec_ok, Bool.false_eq_true, false_iff]
    rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
  | some p =>
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    have hp1 : p.1 = agent := vmLastEntry_fst _ _ _ hL
    have hLk : vmLastEntry st.flow_override.entries.val agent = some (agent, p.2) := by rw [hL, ← hp1]
    simp only [toolId_clone_spec, bind_tc_ok]
    obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
      (vecSetContains_spec types.OverrideKey.Insts.CoreCloneClone
        types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec p.2
        { tool := tool, level := level })
    rw [hbEq]; simp only [spec_ok]
    rw [hbIff]
    constructor
    · intro hmem; exact ⟨p.2, hLk, hmem⟩
    · rintro ⟨vs, hvs, hv⟩
      rw [hLk, Option.some_inj, Prod.mk.injEq] at hvs
      obtain ⟨_, rfl⟩ := hvs; exact hv

/-! ## `override_consumed` -/

/-- `override_consumed agent tool level` is the last-match nested membership of the `(tool, level)`
    `OverrideKey` in `agent`'s `override_used` set. -/
theorem overrideConsumed_spec (st : state.KernelState) (agent : types.AgentId)
    (tool : types.ToolId) (level : types.ConfLevel) :
    state.KernelState.override_consumed st agent tool level ⦃ b =>
      b = true ↔ vmsMemLast st.override_used agent { tool := tool, level := level } ⦄ := by
  unfold state.KernelState.override_consumed
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      (collections.VecSet.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCloneClone)
      st.override_used agent)
  rw [hoEq]; simp only [bind_tc_ok]
  cases hL : vmLastEntry st.override_used.entries.val agent with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho
    simp only [spec_ok, Bool.false_eq_true, false_iff]
    rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
  | some p =>
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    have hp1 : p.1 = agent := vmLastEntry_fst _ _ _ hL
    have hLk : vmLastEntry st.override_used.entries.val agent = some (agent, p.2) := by rw [hL, ← hp1]
    simp only [toolId_clone_spec, bind_tc_ok]
    obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
      (vecSetContains_spec types.OverrideKey.Insts.CoreCloneClone
        types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec p.2
        { tool := tool, level := level })
    rw [hbEq]; simp only [spec_ok]
    rw [hbIff]
    constructor
    · intro hmem; exact ⟨p.2, hLk, hmem⟩
    · rintro ⟨vs, hvs, hv⟩
      rw [hLk, Option.some_inj, Prod.mk.injEq] at hvs
      obtain ⟨_, rfl⟩ := hvs; exact hv

/-! ## Bool-valued agreement functions

The egress-gated actions feed `gateEgress_spec` per-tool Bool oracle values. `ovC`/`ocC` are the
`has_flow_override` / `override_consumed` results as total Bool functions (the only opaque oracle is
the content gate, supplied separately). -/

/-- `has_flow_override` as a total Bool function: last-match nested membership of the grant key
    in the agent's state-side `flow_override` set (the `ocC` twin). -/
def ovC (st : state.KernelState) (agent : types.AgentId) (level : types.ConfLevel)
    (t : types.ToolId) : Bool :=
  match vmLastEntry st.flow_override.entries.val agent with
  | none => false
  | some p => decide ((⟨t, level⟩ : types.OverrideKey) ∈ p.2.items.val)

theorem ovC_eq (st : state.KernelState) (agent : types.AgentId) (level : types.ConfLevel)
    (t : types.ToolId) :
    state.KernelState.has_flow_override st agent t level = .ok (ovC st agent level t) := by
  obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (hasFlowOverride_spec st agent t level)
  rw [hb]; congr 1; unfold ovC
  cases hL : vmLastEntry st.flow_override.entries.val agent with
  | none =>
    have hnot : ¬ vmsMemLast st.flow_override agent ⟨t, level⟩ := by
      rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
    cases b <;> simp_all
  | some p =>
    have hp1 : p.1 = agent := vmLastEntry_fst _ _ _ hL
    have hiff : vmsMemLast st.flow_override agent ⟨t, level⟩ ↔
        (⟨t, level⟩ : types.OverrideKey) ∈ p.2.items.val := by
      constructor
      · rintro ⟨vs, hvs, hv⟩; rw [hL, Option.some_inj] at hvs; subst hvs; exact hv
      · intro hv; exact ⟨p.2, by rw [hL, ← hp1], hv⟩
    cases b <;> simp_all

/-- `override_consumed` as a total Bool function: last-match nested membership of the override key. -/
def ocC (st : state.KernelState) (agent : types.AgentId) (level : types.ConfLevel)
    (t : types.ToolId) : Bool :=
  match vmLastEntry st.override_used.entries.val agent with
  | none => false
  | some p => decide ((⟨t, level⟩ : types.OverrideKey) ∈ p.2.items.val)

theorem ocC_eq (st : state.KernelState) (agent : types.AgentId) (level : types.ConfLevel)
    (t : types.ToolId) :
    state.KernelState.override_consumed st agent t level = .ok (ocC st agent level t) := by
  obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (overrideConsumed_spec st agent t level)
  rw [hb]; congr 1; unfold ocC
  cases hL : vmLastEntry st.override_used.entries.val agent with
  | none =>
    have hnot : ¬ vmsMemLast st.override_used agent ⟨t, level⟩ := by
      rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
    cases b <;> simp_all
  | some p =>
    have hp1 : p.1 = agent := vmLastEntry_fst _ _ _ hL
    have hiff : vmsMemLast st.override_used agent ⟨t, level⟩ ↔
        (⟨t, level⟩ : types.OverrideKey) ∈ p.2.items.val := by
      constructor
      · rintro ⟨vs, hvs, hv⟩; rw [hL, Option.some_inj] at hvs; subst hvs; exact hv
      · intro hv; exact ⟨p.2, by rw [hL, ← hp1], hv⟩
    cases b <;> simp_all

/-! ## Per-invocation flow contribution (shared by `sentinel_elevate_taint` /
`return_unendorsed`)

`invToolC` / `egItems` and the per-invocation `invMissing` / `invDenied` / `invConsumed`
contributions to a flow loop's `missing_binding` / `denied` / `to_consume`, plus the pure
`FlowMode` keystones `egressConsumed_iff_abstractDenied` / `not_egressDenied_disj` and the
`inFlightLen` capacity helper. Bridging shared by the egress-gated actions. -/

/-- The live tool bound to `inv` (last-match `invocation_tool`), or `none`. -/
def invToolC (st : state.KernelState) (inv : types.InvocationId) : Option types.ToolId :=
  (vmLastEntry st.invocation_tool.entries.val inv).map Prod.snd

/-- A tool's egress list: empty when it has no metadata. -/
def egItems (bg : background.BackgroundTheory) (tool : types.ToolId) : List types.EgressKind :=
  match toolMetaC bg tool with
  | none => []
  | some m => m.egress.items.val

/-- `inv` lacks a tool binding (the `MissingToolBinding` condition). -/
def invMissing (st : state.KernelState) (inv : types.InvocationId) : Prop :=
  invToolC st inv = none

/-- `inv` contributes denial: its bound tool has an egress that the flow gate denies at `level`. -/
def invDenied (st : state.KernelState) (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (cgOf ovOf ocOf : types.ToolId → Bool) (inv : types.InvocationId) : Prop :=
  ∃ tool, invToolC st inv = some tool ∧
    ∃ E ∈ egItems bg tool, egressDenied (flowModeC bg level E) (cgOf tool) (ovOf tool) (ocOf tool)

/-- `inv` contributes the override key `k` to `to_consume`. -/
def invConsumed (st : state.KernelState) (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (ovOf ocOf : types.ToolId → Bool) (inv : types.InvocationId) (k : types.OverrideKey) : Prop :=
  ∃ tool, invToolC st inv = some tool ∧ k = gateConsumeKey tool level ∧
    ∃ E ∈ egItems bg tool, egressConsumed (flowModeC bg level E) (ovOf tool) (ocOf tool)

/-- A missing-binding invocation contributes no denial. -/
theorem not_invDenied_missing {st bg level cgOf ovOf ocOf} {inv : types.InvocationId}
    (h : invToolC st inv = none) : ¬ invDenied st bg level cgOf ovOf ocOf inv := by
  simp only [invDenied]; rintro ⟨tool, htool, _⟩; rw [h] at htool; simp at htool

/-- A missing-binding invocation contributes nothing to `to_consume`. -/
theorem not_invConsumed_missing {st bg level ovOf ocOf} {inv : types.InvocationId}
    {k : types.OverrideKey} (h : invToolC st inv = none) :
    ¬ invConsumed st bg level ovOf ocOf inv k := by
  simp only [invConsumed]; rintro ⟨tool, htool, _⟩; rw [h] at htool; simp at htool

/-- The length of `agent`'s live (last-match) in-flight set, `0` when `agent` is absent. -/
def inFlightLen (st : state.KernelState) (agent : types.AgentId) : Nat :=
  match vmLastEntry st.in_flight.entries.val agent with
  | none => 0
  | some p => p.2.items.val.length

/-! ## Flow-guard ⇒ consume/denied-modulo-override equivalence

The keystone single-use correspondence, at the pure `FlowMode`/`Bool` level. Under the per-egress
guard (no egress is `Denied`), a tool's `to_consume` contribution (`∃ Deny egress`, i.e.
`egressConsumed`) coincides with the abstract "an override was relied on" condition (`override present`
plus `∃ egress that the flow would deny without the override`). The guard forces `ov ∧ ¬oc` at every
`Deny` egress and rules out `Inspect`-with-failing-gate, collapsing the two to `∃ Deny egress`. -/
theorem egressConsumed_iff_abstractDenied
    (egs : List types.EgressKind) (fm : types.EgressKind → background.FlowMode) (cg ov oc : Bool)
    (hguard : ∀ E ∈ egs, ¬ egressDenied (fm E) cg ov oc) :
    (∃ E ∈ egs, egressConsumed (fm E) ov oc) ↔
    (ov = true ∧ ∃ E ∈ egs, (fm E ≠ background.FlowMode.Allow ∧
       ¬ (fm E = background.FlowMode.Inspect ∧ cg = true))) := by
  constructor
  · rintro ⟨E, hE, hd, hov, _hoc⟩
    refine ⟨hov, E, hE, ?_, ?_⟩
    · simp [hd]
    · simp [hd]
  · rintro ⟨hov, E, hE, hne, hni⟩
    refine ⟨E, hE, ?_⟩
    have hg := hguard E hE
    simp only [egressDenied] at hg
    cases hfmE : fm E with
    | Allow => rw [hfmE] at hne; exact absurd rfl hne
    | Inspect =>
      rw [hfmE] at hg hni
      exfalso
      cases cg with
      | false => exact hg (Or.inl ⟨rfl, rfl⟩)
      | true => exact hni ⟨rfl, rfl⟩
    | Deny =>
      rw [hfmE] at hg
      refine ⟨rfl, hov, ?_⟩
      cases oc with
      | false => rfl
      | true => exact absurd (Or.inr ⟨rfl, Or.inr rfl⟩) hg

/-- `¬ egressDenied` rewritten as the abstract three-way flow disjunction (Allow / Inspect-with-gate /
    fresh-override). Pure `FlowMode`/`Bool` case analysis. -/
theorem not_egressDenied_disj (fm : background.FlowMode) (cg ov oc : Bool)
    (h : ¬ egressDenied fm cg ov oc) :
    fm = background.FlowMode.Allow ∨ (fm = background.FlowMode.Inspect ∧ cg = true)
      ∨ (ov = true ∧ oc = false) := by
  simp only [egressDenied, not_or] at h
  obtain ⟨h1, h2⟩ := h
  cases fm with
  | Allow => exact Or.inl rfl
  | Inspect =>
    cases cg with
    | true => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | false => exact absurd ⟨rfl, rfl⟩ h1
  | Deny =>
    cases ov with
    | false => exact absurd ⟨rfl, Or.inl rfl⟩ h2
    | true =>
      cases oc with
      | false => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      | true => exact absurd ⟨rfl, Or.inr rfl⟩ h2

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id residuals (via
-- `Collections`). The `EgressKind`/`FlowKey`/`OverrideKey`/`FlowMode` eq/clone facts are PROVED
-- (nullary enums / structs), not trusted. The flow-policy / override reads reduce purely.
#print axioms ArgusLean.Refinement.flowMode_spec
#print axioms ArgusLean.Refinement.hasFlowOverride_spec
#print axioms ArgusLean.Refinement.overrideConsumed_spec
