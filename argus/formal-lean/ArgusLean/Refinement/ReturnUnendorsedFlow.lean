import ArgusLean.Refinement.FlowBridging

/-! # Refinement — flow-oracle reads for the egress-gated actions

The concrete-only oracle reads the egress-gated actions (`return_unendorsed`, `sentinel_elevate_taint`)
perform, pinned to their faithful values so they can feed `flowDecision_spec` / `gateEgress_spec`:

* `flowMode_spec` — `flow_mode` is total (`VecMap.get` on `flow_policy` defaults to `Deny`); `flowModeC`
  is its pure value.
* `hasFlowOverride_spec` — `has_flow_override` is membership of the `(agent, tool, level)`
  `OverrideEntry` in `flow_overrides`.
* `overrideConsumed_spec` — `override_consumed` is the last-match nested membership of the
  `(tool, level)` `OverrideKey` in the agent's `override_used` set (`vmsMemLast`).

Plus the supporting `FlowKey` / `EgressKind` / `OverrideKey` / `FlowMode` decidable-equality / clone
facts — all *proved* (nullary enums / structs of them), no extractor trust beyond the `String` ids. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## `EgressKind` / `FlowKey` / `OverrideKey` / `FlowMode` equality and clone -/

deriving instance DecidableEq for types.EgressKind
deriving instance DecidableEq for types.FlowKey

/-- `EgressKind.eq` faithful decidable equality (nullary enum). -/
@[simp] theorem egressKind_eq_spec (a b : types.EgressKind) :
    types.EgressKind.Insts.CoreCmpPartialEqEgressKind.eq a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp [types.EgressKind.Insts.CoreCmpPartialEqEgressKind.eq, types.EgressKind.read_discriminant]

/-- `FlowKey.eq` faithful decidable equality: level (enum) then egress (enum). -/
@[simp] theorem flowKey_eq_spec (a b : types.FlowKey) :
    types.FlowKey.Insts.CoreCmpPartialEqFlowKey.eq a b = .ok (decide (a = b)) := by
  obtain ⟨l1, e1⟩ := a; obtain ⟨l2, e2⟩ := b
  simp only [types.FlowKey.Insts.CoreCmpPartialEqFlowKey.eq, confLevel_eq_spec, bind_tc_ok]
  by_cases hl : l1 = l2
  · subst hl; simp [egressKind_eq_spec]
  · simp [hl]

/-- `FlowKey.clone` is the identity (nullary-enum fields, body `ok self`). -/
@[simp] theorem flowKey_clone_spec (a : types.FlowKey) :
    types.FlowKey.Insts.CoreCloneClone.clone a = .ok a := rfl

/-- `FlowMode.clone` is the identity (body `ok self`). -/
@[simp] theorem flowMode_clone_spec (a : background.FlowMode) :
    background.FlowMode.Insts.CoreCloneClone.clone a = .ok a := rfl

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

/-! ## `flow_mode` -/

/-- The pure value of `flow_mode`: the live `(level, egress)` policy entry, defaulting to `Deny`. -/
def flowModeC (bg : background.BackgroundTheory) (level : types.ConfLevel) (E : types.EgressKind) :
    background.FlowMode :=
  match vmLastEntry bg.flow_policy.entries.val { level := level, egress := E } with
  | none => background.FlowMode.Deny
  | some p => p.2

/-- `flow_mode` is total and computes `flowModeC`. -/
theorem flowMode_spec (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    background.BackgroundTheory.flow_mode bg level E ⦃ fm => fm = flowModeC bg level E ⦄ := by
  unfold background.BackgroundTheory.flow_mode
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.FlowKey.Insts.CoreCloneClone types.FlowKey.Insts.CoreCmpPartialEqFlowKey
      flowKey_eq_spec background.FlowMode.Insts.CoreCloneClone bg.flow_policy
      { level := level, egress := E })
  rw [hoEq]; simp only [bind_tc_ok]
  unfold flowModeC
  cases hL : vmLastEntry bg.flow_policy.entries.val { level := level, egress := E } with
  | none => rw [hL] at ho; subst ho; simp
  | some p => rw [hL] at ho; subst ho; simp

/-- Equational form of `flowMode_spec`, for feeding `gateEgress_spec`'s `hfmOf`. -/
theorem flowMode_eq (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    background.BackgroundTheory.flow_mode bg level E = .ok (flowModeC bg level E) := by
  obtain ⟨fm, h1, h2⟩ := spec_imp_exists (flowMode_spec bg level E); rw [← h2]; exact h1

/-! ## `has_flow_override` -/

/-- `has_flow_override agent tool level` is membership of the `(agent, tool, level)` `OverrideEntry`
    in `flow_overrides`. -/
theorem hasFlowOverride_spec (bg : background.BackgroundTheory) (agent : types.AgentId)
    (tool : types.ToolId) (level : types.ConfLevel) :
    background.BackgroundTheory.has_flow_override bg agent tool level ⦃ b =>
      b = true ↔ vsMem bg.flow_overrides { agent := agent, tool := tool, level := level } ⦄ := by
  unfold background.BackgroundTheory.has_flow_override
  rw [agentId_clone_spec, bind_tc_ok, toolId_clone_spec, bind_tc_ok]
  exact vecSetContains_spec types.OverrideEntry.Insts.CoreCloneClone
    types.OverrideEntry.Insts.CoreCmpPartialEqOverrideEntry overrideEntry_eq_spec
    bg.flow_overrides { agent := agent, tool := tool, level := level }

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

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id residuals (via
-- `Collections`). The `EgressKind`/`FlowKey`/`OverrideKey`/`FlowMode` eq/clone facts are PROVED
-- (nullary enums / structs), not trusted. The flow-policy / override reads reduce purely.
#print axioms ArgusLean.Refinement.flowMode_spec
#print axioms ArgusLean.Refinement.hasFlowOverride_spec
#print axioms ArgusLean.Refinement.overrideConsumed_spec
