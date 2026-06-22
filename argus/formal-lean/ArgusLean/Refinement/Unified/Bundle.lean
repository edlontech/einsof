import ArgusLean.Refinement.Unified.Preservation.RegisterTool
import ArgusLean.Refinement.Unified.Preservation.LoadInstruction
import ArgusLean.Refinement.Unified.Preservation.GrantCapability
import ArgusLean.Refinement.Unified.Preservation.SentinelCreditBudget
import ArgusLean.Refinement.Unified.Preservation.ReturnEndorsed
import ArgusLean.Refinement.Unified.Preservation.Revoke
import ArgusLean.Refinement.Unified.Preservation.CascadeRevoke
import ArgusLean.Refinement.Unified.Preservation.Delegate
import ArgusLean.Refinement.Unified.Preservation.InvokeComplete
import ArgusLean.Refinement.Unified.Preservation.SentinelElevateTaint
import ArgusLean.Refinement.Unified.Preservation.ReturnUnendorsed
import ArgusLean.Refinement.Unified.Preservation.InvokeStart
import ArgusLean.Refinement.Unified.Preservation.GrantOverride

/-! # Layer 1 — top-level dispatch + the `step_refines` bundle

The capstone of Layer 1: a single concrete step `kernelStep`, the abstract action it refines
(`absActionOf`), and the bundle theorem `step_refines` collapsing the 12 per-action `_preservesR`
lemmas into one "the kernel simulates the spec, preserving `R`" statement.

`kernelStep` and `absActionOf` are total dispatchers over `event.KernelAction` (the extracted action
tag carries every parameter). The oracle-backed transitions (`invoke_start`, `invoke_complete`,
`return_unendorsed`, `sentinel_elevate_taint`) take the `Kernel<A,C,F,E>` oracle instances + parameters,
so `kernelStep` is parameterised by them; their `step_refines` cases consume the `CgAgree` / `AuAgree` /
`CfAgree` agreement hypotheses (the runtime-oracle fields kept out of `R`).

## Status (2026-06-03)

`step_refines` is **assembled**: all 12 `_preservesR` lemmas are proven, and `step_refines` collapses
them into one "the kernel step simulates the spec, preserving `R`" statement by a case-split on the
extracted action tag. The capacity-honesty assumptions are the per-action `StepPre` bundle (the exact
bounds each `_preservesR` lists; there is no resource model to discharge them — see the note below); the
runtime-oracle agreements are the `CgAgree` / `AuAgree` / `CfAgree` hypotheses, reduced to the per-agent
`cgOf` / `auOf` / `cfOf` the oracle-backed lemmas take via the extraction helpers. `InvokeStart`'s
abstract binding prediction (`a.invocation_tool inv = tool`) is the last `StepPre` conjunct. -/

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
  | .ReturnEndorsed child parent =>
      transitions.return_endorsed cfInst st bg conformance child parent
  | .ReturnUnendorsed child parent =>
      transitions.return_unendorsed cgInst st bg content_gate child parent
  | .SentinelElevateTaint agent level =>
      transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
  | .SentinelCreditBudget agent amount => transitions.sentinel_credit_budget st bg agent amount
  | .GrantOverride granter target tool level =>
      transitions.grant_override st bg granter target tool level

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
  | .SentinelCreditBudget agent amount => Tzimtzum.sentinel_credit_budget agent amount.val
  | .GrantOverride granter target tool level =>
      Tzimtzum.grant_override granter target tool (confA level)

/-! ## Capacity honesty + per-action precondition

Every `_preservesR` lemma takes its `…entries.length < Usize.max` (and joint/multiplicative) bounds as
free hypotheses. There is no resource model to discharge them — a `Vec` cannot in practice grow past
`usize::MAX`, but proving it is out of scope. The bundle states the capacity assumption explicitly
rather than pretending it away: `StepPre st bg a act` is the per-action conjunction of exactly the
bounds the fired transition's `_preservesR` lists, plus — for `InvokeStart` — the abstract binding
prediction `a.invocation_tool inv = tool` (the one non-capacity precondition, the oracle agreement on
the invocation's tool). The agent-tree removals (`revoke` / `cascade_revoke`) need none, so their slot
is `True`; `sentinel_credit_budget` needs only its `agent_budget` capacity bound (the credit insert). -/

/-- The per-action precondition `step_refines` consumes for `act`: the capacity bounds its
    `_preservesR` lemma requires, plus `InvokeStart`'s abstract binding prediction. -/
def StepPre (st : state.KernelState) (_bg : background.BackgroundTheory) (a : AbsState)
    (act : event.KernelAction) : Prop :=
  match act with
  | .RegisterTool _ => st.tool_registered.items.val.length < Usize.max
  | .LoadInstruction _ _ =>
      st.agent_instruction.entries.val.length < Usize.max ∧
      (∀ p ∈ st.agent_instruction.entries.val, p.2.items.val.length < Usize.max)
  | .Delegate _ _ =>
      st.agent_active.items.val.length < Usize.max ∧
      st.agent_cap.entries.val.length < Usize.max ∧
      st.agent_parent.entries.val.length < Usize.max
  | .GrantCapability _ _ _ =>
      st.agent_cap.entries.val.length < Usize.max ∧
      (∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
  | .Revoke _ _ => True
  | .CascadeRevoke _ _ => True
  | .InvokeStart agent tool inv =>
      (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1 ≤ Usize.max) ∧
      st.override_used.entries.val.length < Usize.max ∧
      (∀ p ∈ st.override_used.entries.val,
        p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
          + vmSetLen st.in_flight agent + 1) ≤ Usize.max) ∧
      st.invocation_tool.entries.val.length < Usize.max ∧
      st.in_flight.entries.val.length < Usize.max ∧
      (∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max) ∧
      a.invocation_tool inv = tool
  | .InvokeComplete _ _ =>
      st.agent_budget.entries.val.length < Usize.max ∧
      st.taint_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      st.gh_taint_invoked.entries.val.length < Usize.max ∧
      (∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
  | .ReturnEndorsed _ _ => st.agent_budget.entries.val.length < Usize.max
  | .ReturnUnendorsed child parent =>
      (vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max) ∧
      st.taint_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.taint_levels.entries.val,
        p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max) ∧
      (vmSetLen st.taint_levels child ≤ Usize.max) ∧
      st.gh_taint_received.entries.val.length < Usize.max ∧
      (∀ p ∈ st.gh_taint_received.entries.val,
        p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max) ∧
      st.override_used.entries.val.length < Usize.max ∧
      (∀ p ∈ st.override_used.entries.val,
        p.2.items.val.length + vmSetLen st.taint_levels child * vmSetLen st.in_flight parent
          ≤ Usize.max)
  | .SentinelElevateTaint agent _ =>
      (inFlightLen st agent ≤ Usize.max) ∧
      st.override_used.entries.val.length < Usize.max ∧
      (∀ p ∈ st.override_used.entries.val, p.2.items.val.length + inFlightLen st agent ≤ Usize.max) ∧
      st.taint_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      st.gh_taint_invoked.entries.val.length < Usize.max ∧
      (∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
  | .SentinelCreditBudget _ _ => st.agent_budget.entries.val.length < Usize.max
  | .GrantOverride _ _ _ _ =>
      st.flow_override.entries.val.length < Usize.max ∧
      (∀ p ∈ st.flow_override.entries.val, p.2.items.val.length < Usize.max) ∧
      st.agent_budget.entries.val.length < Usize.max

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

/-- The return-conformance reduction at a fixed `(child, parent)`, from `RcAgree` (state-independent). -/
noncomputable def rcOfAgree {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : RcAgree cfInst conformance bg a) (c p : types.AgentId) : Bool :=
  (h c p).choose

theorem rcOfAgree_ok {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : RcAgree cfInst conformance bg a) (c p : types.AgentId) (s : state.KernelState) :
    cfInst.return_conforms conformance c p s bg = .ok (rcOfAgree h c p) := (h c p).choose_spec.1 s

theorem rcOfAgree_iff {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : RcAgree cfInst conformance bg a) (c p : types.AgentId) :
    rcOfAgree h c p = true ↔ a.return_conforms c p := (h c p).choose_spec.2

/-! ## The bundle: `step_refines`

The capstone. For any concrete state related to the abstract by `R`, with the runtime oracles agreeing
(`CgAgree`/`AuAgree`/`CfAgree`) and the fired action's capacity precondition (`StepPre`) met, every
successful `kernelStep` is matched by the abstract `absActionOf act` — establishing its guard, producing
a successor, and **preserving `R`**. One case per extracted action tag, each dispatching to the action's
`_preservesR` lemma; the four oracle-backed cases reduce the state-level agreements to the per-agent
`cgOf`/`auOf`/`cfOf` the lemmas take. This is the single "the kernel simulates the spec" statement the
12 per-action islands collapse into. -/

theorem step_refines {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (act : event.KernelAction)
    (hR : R st bg a)
    (hCg : CgAgree cgInst content_gate st bg a)
    (hAu : AuAgree aInst authorizer st bg a)
    (hCf : CfAgree cfInst conformance bg a)
    (hRc : RcAgree cfInst conformance bg a)
    (hPre : StepPre st bg a act)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : kernelStep aInst cgInst cfInst authorizer content_gate conformance st bg act
      = .ok (.Ok (st', ev))) :
    ∃ a', (absActionOf act).guard a ∧ (absActionOf act).next a a' ∧ R st' bg a' := by
  cases act with
  | RegisterTool tool =>
      exact register_tool_preservesR st bg a tool hR hPre st' ev hok
  | LoadInstruction agent instr =>
      exact load_instruction_preservesR st bg a agent instr hR hPre.1 hPre.2 st' ev hok
  | Delegate grantor grantee =>
      exact delegate_preservesR st bg a grantor grantee hR hPre.1 hPre.2.1 hPre.2.2 st' ev hok
  | GrantCapability parent child cap =>
      exact grant_capability_preservesR st bg a parent child cap hR hPre.1 hPre.2 st' ev hok
  | Revoke parent target =>
      exact revoke_preservesR st bg a parent target hR st' ev hok
  | CascadeRevoke child parent =>
      exact cascade_revoke_preservesR st bg a child parent hR st' ev hok
  | InvokeStart agent tool inv =>
      obtain ⟨auOf, hau, hauA⟩ := auOfAgree hAu agent tool
      exact invoke_start_preservesR aInst cgInst st bg authorizer content_gate a agent tool inv
        (cgOfAgree hCg agent) auOf (fun t => cgOfAgree_ok hCg agent t)
        (fun t => cgOfAgree_iff hCg agent t) hau hauA hPre.2.2.2.2.2.2 hR hPre.1 hPre.2.1 hPre.2.2.1
        hPre.2.2.2.1 hPre.2.2.2.2.1 hPre.2.2.2.2.2.1 st' ev hok
  | InvokeComplete agent inv =>
      exact invoke_complete_preservesR cfInst st bg conformance a agent inv (cfOfAgree hCf agent)
        (fun t s => cfOfAgree_ok hCf agent t s) (fun t => cfOfAgree_iff hCf agent t) hR
        hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2.1 hPre.2.2.2.2 st' ev hok
  | ReturnEndorsed child parent =>
      exact return_endorsed_preservesR cfInst st bg conformance a child parent
        (rcOfAgree hRc child parent) (rcOfAgree_ok hRc child parent) (rcOfAgree_iff hRc child parent)
        hR hPre st' ev hok
  | ReturnUnendorsed child parent =>
      exact return_unendorsed_preservesR cgInst st bg content_gate a child parent
        (cgOfAgree hCg parent) (fun t => cgOfAgree_ok hCg parent t)
        (fun t => cgOfAgree_iff hCg parent t) hR hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2.1
        hPre.2.2.2.2.1 hPre.2.2.2.2.2.1 hPre.2.2.2.2.2.2.1 hPre.2.2.2.2.2.2.2 st' ev hok
  | SentinelElevateTaint agent level =>
      exact sentinel_elevate_taint_preservesR cgInst st bg content_gate a agent level
        (cgOfAgree hCg agent) (fun t => cgOfAgree_ok hCg agent t)
        (fun t => cgOfAgree_iff hCg agent t) hR hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2.1
        hPre.2.2.2.2.1 hPre.2.2.2.2.2.1 hPre.2.2.2.2.2.2 st' ev hok
  | SentinelCreditBudget agent amount =>
      exact sentinel_credit_budget_preservesR st bg a agent amount hR hPre st' ev hok
  | GrantOverride granter target tool level =>
      exact grant_override_preservesR st bg a granter target tool level hR
        hPre.1 hPre.2.1 hPre.2.2 st' ev hok

end ArgusLean.Refinement
