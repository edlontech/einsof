import ArgusLean.Refinement.Unified.Preservation.RegisterTool
import ArgusLean.Refinement.Unified.Preservation.LoadInstruction
import ArgusLean.Refinement.Unified.Preservation.GrantCapability
import ArgusLean.Refinement.Unified.Preservation.SentinelRefreshBudget
import ArgusLean.Refinement.Unified.Preservation.ReturnEndorsed

/-! # Layer 1 — top-level dispatch + the `step_refines` bundle (in progress)

The capstone of Layer 1: a single concrete step `kernelStep`, the abstract action it refines
(`absActionOf`), and the bundle theorem `step_refines` collapsing the 12 per-action `_preservesR`
lemmas into one "the kernel simulates the spec, preserving `R`" statement.

`kernelStep` and `absActionOf` are total dispatchers over `event.KernelAction` (the extracted action
tag carries every parameter). The oracle-backed transitions (`invoke_start`, `invoke_complete`,
`return_unendorsed`, `sentinel_elevate_taint`) take the `Kernel<A,C,F,E>` oracle instances + parameters,
so `kernelStep` is parameterised by them; their `step_refines` cases consume the `CgAgree` / `AuAgree` /
`CfAgree` agreement hypotheses (the runtime-oracle fields kept out of `R`).

## Status (2026-06-03)

`step_refines` is **not yet assembled**: 5 of the 12 `_preservesR` lemmas are proven
(`register_tool`, `load_instruction`, `grant_capability`, `sentinel_refresh_budget`,
`return_endorsed`), the other 7 (the three `clear_agent_state` removals `delegate` / `revoke` /
`cascade_revoke` and the four oracle actions `invoke_start` / `invoke_complete` /
`return_unendorsed` / `sentinel_elevate_taint`) remain. This file provides the dispatcher + the
`CapacityOK` capacity-honesty hypothesis + the oracle-extraction helpers, so the assembly is a
mechanical case-split once those land. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

/-- The concrete step: dispatch a tagged `event.KernelAction` to its extracted transition. The four
    oracle-backed transitions thread the `Kernel<A,C,F,E>` instances/parameters. -/
noncomputable def kernelStep {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (act : event.KernelAction) :
    Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError) :=
  match act with
  | .RegisterTool tool => transitions.register_tool st bg tool
  | .LoadInstruction agent instr => transitions.load_instruction st bg agent instr
  | .Delegate grantor grantee => transitions.delegate st bg grantor grantee
  | .GrantCapability parent child cap => transitions.grant_capability st bg parent child cap
  | .Revoke parent target => transitions.revoke st bg parent target
  | .CascadeRevoke child parent => transitions.cascade_revoke st bg child parent
  | .InvokeStart agent tool inv =>
      transitions.invoke_start aInst cgInst st bg authorizer content_gate agent tool inv
  | .InvokeComplete agent inv => transitions.invoke_complete cfInst st bg conformance agent inv
  | .ReturnEndorsed child parent => transitions.return_endorsed st bg child parent
  | .ReturnUnendorsed child parent =>
      transitions.return_unendorsed cgInst st bg content_gate child parent
  | .SentinelElevateTaint agent level =>
      transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
  | .SentinelRefreshBudget agent => transitions.sentinel_refresh_budget st bg agent

/-- The abstract action a tagged step refines: the matching `Tzimtzum` action at the tag's parameters.
    `SentinelElevateTaint` maps its concrete `ConfLevel` to the abstract lattice via `confA`. -/
def absActionOf (act : event.KernelAction) : Kav.Action AbsState :=
  match act with
  | .RegisterTool tool => Tzimtzum.register_tool tool
  | .LoadInstruction agent instr => Tzimtzum.load_instruction agent instr
  | .Delegate grantor grantee => Tzimtzum.delegate grantor grantee
  | .GrantCapability parent child cap => Tzimtzum.grant_capability parent child cap
  | .Revoke parent target => Tzimtzum.revoke parent target
  | .CascadeRevoke child parent => Tzimtzum.cascade_revoke child parent
  | .InvokeStart agent tool inv => Tzimtzum.invoke_start agent tool inv
  | .InvokeComplete agent inv => Tzimtzum.invoke_complete agent inv
  | .ReturnEndorsed child parent => Tzimtzum.return_endorsed child parent
  | .ReturnUnendorsed child parent => Tzimtzum.return_unendorsed child parent
  | .SentinelElevateTaint agent level => Tzimtzum.sentinel_elevate_taint agent (confA level)
  | .SentinelRefreshBudget agent => Tzimtzum.sentinel_refresh_budget agent

/-! ## Capacity honesty

Every `_preservesR` lemma takes its `…entries.length < Usize.max` (and joint/multiplicative) bounds as
free hypotheses. There is no resource model to discharge them — a `Vec` cannot in practice grow past
`usize::MAX`, but proving it is out of scope (see the remaining-work note). The bundle states the
capacity assumption explicitly rather than pretending it away; `CapacityOK st` is the per-action
conjunction needed by whichever transition fires. (Stated abstractly here; the per-action instances are
the bounds each `_preservesR` already lists.) -/

/-- Placeholder for the per-step capacity assumption. The concrete bounds are the ones each
    `_preservesR` lemma takes; `step_refines` will be stated against the relevant instance. -/
abbrev CapacityOK (_st : state.KernelState) : Prop := True

/-! ## Runtime-oracle extraction

From the state-level `CgAgree` / `AuAgree` / `CfAgree` agreements, extract the per-agent boolean
reductions (`cgOf`/`auOf`/`cfOf`) and their `_ok`/`_iff` halves that the oracle-backed action lemmas
take. Uses `Classical.choose` (already in the standard TCB). -/

/-- The content-gate reduction at a fixed agent, from `CgAgree`. -/
noncomputable def cgOfAgree {C : Type} {cgInst : traits.ContentGateOracle C} {content_gate : C}
    {st : state.KernelState} {bg : background.BackgroundTheory} {a : AbsState}
    (h : CgAgree cgInst content_gate st bg a) (ag : types.AgentId) : types.ToolId → Bool :=
  fun t => (h ag t).choose

theorem cgOfAgree_ok {C : Type} {cgInst : traits.ContentGateOracle C} {content_gate : C}
    {st : state.KernelState} {bg : background.BackgroundTheory} {a : AbsState}
    (h : CgAgree cgInst content_gate st bg a) (ag : types.AgentId) (t : types.ToolId) :
    cgInst.passes content_gate ag t st bg = .ok (cgOfAgree h ag t) := (h ag t).choose_spec.1

theorem cgOfAgree_iff {C : Type} {cgInst : traits.ContentGateOracle C} {content_gate : C}
    {st : state.KernelState} {bg : background.BackgroundTheory} {a : AbsState}
    (h : CgAgree cgInst content_gate st bg a) (ag : types.AgentId) (t : types.ToolId) :
    cgOfAgree h ag t = true ↔ a.content_gate_passes ag t := (h ag t).choose_spec.2

/-- The authorizer reduction at a fixed `(agent, tool)`, from `AuAgree`. -/
theorem auOfAgree {A : Type} {aInst : traits.AuthorizerOracle A} {authorizer : A}
    {st : state.KernelState} {bg : background.BackgroundTheory} {a : AbsState}
    (h : AuAgree aInst authorizer st bg a) (ag : types.AgentId) (t : types.ToolId) :
    ∃ b : Bool, aInst.allows authorizer ag t st bg = .ok b ∧ (b = true ↔ a.authorizer_allows ag t) :=
  h ag t

/-- The conformance reduction at a fixed agent, from `CfAgree` (state-independent). -/
noncomputable def cfOfAgree {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : CfAgree cfInst conformance bg a) (ag : types.AgentId) : types.ToolId → Bool :=
  fun t => (h ag t).choose

theorem cfOfAgree_ok {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : CfAgree cfInst conformance bg a) (ag : types.AgentId) (t : types.ToolId) (s : state.KernelState) :
    cfInst.conforms conformance ag t s bg = .ok (cfOfAgree h ag t) := (h ag t).choose_spec.1 s

theorem cfOfAgree_iff {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : CfAgree cfInst conformance bg a) (ag : types.AgentId) (t : types.ToolId) :
    cfOfAgree h ag t = true ↔ a.output_conforms ag t := (h ag t).choose_spec.2

end ArgusLean.Refinement
