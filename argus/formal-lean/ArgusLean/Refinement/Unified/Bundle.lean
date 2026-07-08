import ArgusLean.Refinement.Unified.Preservation.RegisterTool
import ArgusLean.Refinement.Unified.Preservation.UnregisterTool
import ArgusLean.Refinement.Unified.Preservation.LoadInstruction
import ArgusLean.Refinement.Unified.Preservation.GrantCapability
import ArgusLean.Refinement.Unified.Preservation.SentinelCreditBudget
import ArgusLean.Refinement.Unified.Preservation.ReturnEndorsed
import ArgusLean.Refinement.Unified.Preservation.Revoke
import ArgusLean.Refinement.Unified.Preservation.CascadeRevoke
import ArgusLean.Refinement.Unified.Preservation.Delegate
import ArgusLean.Refinement.Unified.Preservation.InvokeComplete
import ArgusLean.Refinement.Unified.Preservation.SentinelElevateTaint
import ArgusLean.Refinement.Unified.Preservation.SentinelDegradeIntegrity
import ArgusLean.Refinement.Unified.Preservation.ReturnUnendorsed
import ArgusLean.Refinement.Unified.Preservation.InvokeStart
import ArgusLean.Refinement.Unified.Preservation.GrantOverride

/-! # Layer 1 — top-level dispatch + the `step_refines` bundle

V3 (task 14): a single concrete step `kernelStep` over the driver-level command `KernelCmd`, the
abstract action it refines (`absActionOf`), and the bundle theorem `step_refines` collapsing the
15 per-transition `_preservesR` lemmas into one "the kernel simulates the spec, preserving `R`"
statement over the **16** spec actions.

`KernelCmd` is the command surface, not the output `event.KernelAction`: `InvokeStart`
additionally carries the classifier's attested egress set (an input the kernel persists — the
event does not repeat it), and `InvokeComplete` carries no `endorsed` flag (which branch fired is
a RESULT, visible only in the returned event — design §5.4: the kernel's single `invoke_complete`
refines the split pair, the event's `Bool` selecting the spec action). `absActionOf` therefore
takes the command AND the returned event; only the `InvokeComplete` arm inspects the event.

Two hypotheses beyond `R` + the oracle agreements:

* `hFlightUsed` — the spec's `in_flight_implies_used` strengthening invariant at the abstract
  state; the soundness induction supplies it from `Tzimtzum.kav_soundP` at the reachable abstract
  state (design §5.7).
* `StepPre` — the fired transition's capacity bounds, plus `InvokeStart`'s two oracle-seam
  predictions: the abstract tool binding (`a.invocation_tool inv = tool`) and the fresh
  invocation's attested-egress agreement (`hEgAgree`, the per-invocation half of `OracleFidelity`
  that `R`'s used-only `RinvocationEgress` deliberately cannot supply). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

/-- The driver-level command: the extracted transition inputs (see module header for how this
    differs from the output `event.KernelAction`). -/
inductive KernelCmd where
  | RegisterTool : types.ToolId → KernelCmd
  | UnregisterTool : types.ToolId → KernelCmd
  | LoadInstruction : types.AgentId → types.InstructionId → KernelCmd
  | Delegate : types.AgentId → types.AgentId → KernelCmd
  | GrantCapability : types.AgentId → types.AgentId → capability.CapKind → KernelCmd
  | Revoke : types.AgentId → types.AgentId → KernelCmd
  | CascadeRevoke : types.AgentId → types.AgentId → KernelCmd
  | InvokeStart : types.AgentId → types.ToolId → types.InvocationId →
      collections.VecSet types.EgressKind → KernelCmd
  | InvokeComplete : types.AgentId → types.InvocationId → KernelCmd
  | ReturnEndorsed : types.AgentId → types.AgentId → types.ConfLevel → types.IntegLevel →
      KernelCmd
  | ReturnUnendorsed : types.AgentId → types.AgentId → KernelCmd
  | SentinelElevateTaint : types.AgentId → types.ConfLevel → KernelCmd
  | SentinelDegradeIntegrity : types.AgentId → types.IntegLevel → KernelCmd
  | SentinelCreditBudget : types.AgentId → Std.U8 → KernelCmd
  | GrantOverride : types.AgentId → types.AgentId → types.ToolId → types.ConfLevel → KernelCmd

/-- The concrete step: dispatch a `KernelCmd` to its extracted transition. The oracle-backed
    transitions thread the `Kernel<A,C,F,E>` instances/parameters. -/
noncomputable def kernelStep {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (cmd : KernelCmd) :
    Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError) :=
  match cmd with
  | .RegisterTool tool => transitions.register_tool st bg tool
  | .UnregisterTool tool => transitions.unregister_tool st bg tool
  | .LoadInstruction agent instr => transitions.load_instruction st bg agent instr
  | .Delegate grantor grantee => transitions.delegate st bg grantor grantee
  | .GrantCapability parent child cap => transitions.grant_capability st bg parent child cap
  | .Revoke parent target => transitions.revoke st bg parent target
  | .CascadeRevoke child parent => transitions.cascade_revoke st bg child parent
  | .InvokeStart agent tool inv attested_egress =>
      transitions.invoke_start aInst cgInst st bg authorizer content_gate agent tool inv
        attested_egress
  | .InvokeComplete agent inv => transitions.invoke_complete cfInst st bg conformance agent inv
  | .ReturnEndorsed child parent clvl ilvl =>
      transitions.return_endorsed cfInst st bg conformance child parent clvl ilvl
  | .ReturnUnendorsed child parent =>
      transitions.return_unendorsed cgInst st bg content_gate child parent
  | .SentinelElevateTaint agent level =>
      transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
  | .SentinelDegradeIntegrity agent level =>
      transitions.sentinel_degrade_integrity cgInst st bg content_gate agent level
  | .SentinelCreditBudget agent amount => transitions.sentinel_credit_budget st bg agent amount
  | .GrantOverride granter target tool level =>
      transitions.grant_override st bg granter target tool level

/-- The abstract action a command refines. Only the `InvokeComplete` arm inspects the returned
    event: the `endorsed : Bool` it carries selects the split pair's branch (design §5.4). The
    concrete lattice levels map via `confA`/`integA`. -/
def absActionOf (cmd : KernelCmd) (ev : event.KernelAction) : Kav.Action AbsState :=
  match cmd with
  | .RegisterTool tool => Tzimtzum.register_tool tool
  | .UnregisterTool tool => Tzimtzum.unregister_tool tool
  | .LoadInstruction agent instr => Tzimtzum.load_instruction agent instr
  | .Delegate grantor grantee => Tzimtzum.delegate grantor grantee
  | .GrantCapability parent child cap => Tzimtzum.grant_capability parent child cap
  | .Revoke parent target => Tzimtzum.revoke parent target
  | .CascadeRevoke child parent => Tzimtzum.cascade_revoke child parent
  | .InvokeStart agent tool inv _ => Tzimtzum.invoke_start agent tool inv
  | .InvokeComplete agent inv =>
      match ev with
      | .InvokeComplete _ _ true => Tzimtzum.invoke_complete_endorsed agent inv
      | _ => Tzimtzum.invoke_complete_unendorsed agent inv
  | .ReturnEndorsed child parent clvl ilvl =>
      Tzimtzum.return_endorsed child parent (confA clvl) (integA ilvl)
  | .ReturnUnendorsed child parent => Tzimtzum.return_unendorsed child parent
  | .SentinelElevateTaint agent level => Tzimtzum.sentinel_elevate_taint agent (confA level)
  | .SentinelDegradeIntegrity agent level =>
      Tzimtzum.sentinel_degrade_integrity agent (integA level)
  | .SentinelCreditBudget agent amount => Tzimtzum.sentinel_credit_budget agent amount.val
  | .GrantOverride granter target tool level =>
      Tzimtzum.grant_override granter target tool (confA level)

/-! ## Capacity honesty + per-command precondition

Every `_preservesR` lemma takes its `…length < Usize.max` (and joint/multiplicative) bounds as
free hypotheses — there is no resource model to discharge them. `StepPre st bg a cmd` is the
per-command conjunction of exactly the bounds the fired transition's `_preservesR` lists, plus —
for `InvokeStart` — the two oracle-seam predictions (module header). `revoke`/`cascade_revoke`/
`unregister_tool` need none, so their slot is `True`. -/

/-- The per-command precondition `step_refines` consumes. -/
def StepPre (st : state.KernelState) (_bg : background.BackgroundTheory) (a : AbsState)
    (cmd : KernelCmd) : Prop :=
  match cmd with
  | .RegisterTool _ => st.tool_registered.items.val.length < Usize.max
  | .UnregisterTool _ => True
  | .LoadInstruction _ _ =>
      st.agent_instruction.entries.val.length < Usize.max ∧
      (∀ p ∈ st.agent_instruction.entries.val, p.2.items.val.length < Usize.max)
  | .Delegate _ _ =>
      st.agent_active.items.val.length < Usize.max ∧
      st.agent_cap.entries.val.length < Usize.max ∧
      st.agent_parent.entries.val.length < Usize.max ∧
      st.agent_budget.entries.val.length < Usize.max
  | .GrantCapability _ _ _ =>
      st.agent_cap.entries.val.length < Usize.max ∧
      (∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
  | .Revoke _ _ => True
  | .CascadeRevoke _ _ => True
  | .InvokeStart agent tool inv attested_egress =>
      (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1 ≤ Usize.max) ∧
      (vmSetLen st.integ_levels agent + vmSetLen st.in_flight agent ≤ Usize.max) ∧
      st.override_used.entries.val.length < Usize.max ∧
      (∀ p ∈ st.override_used.entries.val,
        p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent + 1
          + vmSetLen st.in_flight agent) ≤ Usize.max) ∧
      st.invocation_tool.entries.val.length < Usize.max ∧
      st.in_flight.entries.val.length < Usize.max ∧
      (∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max) ∧
      st.invocation_used.items.val.length < Usize.max ∧
      st.invocation_egress.entries.val.length < Usize.max ∧
      a.invocation_tool inv = tool ∧
      (∀ E, a.invocation_egress inv E ↔ vsMem attested_egress E)
  | .InvokeComplete _ _ =>
      st.agent_budget.entries.val.length < Usize.max ∧
      st.taint_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      st.integ_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
  | .ReturnEndorsed _ _ _ _ => st.agent_budget.entries.val.length < Usize.max
  | .ReturnUnendorsed child parent =>
      st.taint_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.taint_levels.entries.val,
        p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max) ∧
      (vmSetLen st.taint_levels child ≤ Usize.max) ∧
      st.integ_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.integ_levels.entries.val,
        p.2.items.val.length + vmSetLen st.integ_levels child ≤ Usize.max) ∧
      (vmSetLen st.integ_levels child ≤ Usize.max) ∧
      st.override_used.entries.val.length < Usize.max ∧
      (∀ p ∈ st.override_used.entries.val,
        p.2.items.val.length + vmSetLen st.taint_levels child * vmSetLen st.in_flight parent
          ≤ Usize.max) ∧
      (vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
  | .SentinelElevateTaint agent _ =>
      st.taint_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      st.override_used.entries.val.length < Usize.max ∧
      (∀ p ∈ st.override_used.entries.val,
        p.2.items.val.length + vmSetLen st.in_flight agent ≤ Usize.max) ∧
      (vmSetLen st.in_flight agent ≤ Usize.max)
  | .SentinelDegradeIntegrity _ _ =>
      st.integ_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
  | .SentinelCreditBudget _ _ => st.agent_budget.entries.val.length < Usize.max
  | .GrantOverride _ _ _ _ =>
      st.flow_override.entries.val.length < Usize.max ∧
      (∀ p ∈ st.flow_override.entries.val, p.2.items.val.length < Usize.max) ∧
      st.agent_budget.entries.val.length < Usize.max

/-! ## Runtime-oracle extraction

The oracle-backed lemmas either take the state-level agreements directly (`hCg`/`hAu`), or —
for the conformance verdicts — the per-invocation boolean reductions extracted here via
`Classical.choose` (already in the standard TCB). -/

/-- The conformance reduction at a fixed `(agent, inv)`, from `CfAgree` (state-independent,
    per-invocation). -/
noncomputable def cfOfAgree {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : CfAgree cfInst conformance bg a) (ag : types.AgentId) (inv : types.InvocationId) :
    types.ToolId → Bool :=
  fun t => (h ag t inv).choose

theorem cfOfAgree_ok {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : CfAgree cfInst conformance bg a) (ag : types.AgentId) (inv : types.InvocationId)
    (t : types.ToolId) (s : state.KernelState) :
    cfInst.conforms conformance ag t inv s bg = .ok (cfOfAgree h ag inv t) :=
  (h ag t inv).choose_spec.1 s

theorem cfOfAgree_iff {F : Type} {cfInst : traits.ConformanceOracle F} {conformance : F}
    {bg : background.BackgroundTheory} {a : AbsState}
    (h : CfAgree cfInst conformance bg a) (ag : types.AgentId) (inv : types.InvocationId)
    (t : types.ToolId) :
    cfOfAgree h ag inv t = true ↔ a.invocation_conforms inv := (h ag t inv).choose_spec.2

/-- The return-conformance reduction at a fixed `(child, parent)`, from `RcAgree`
    (state-independent, pairwise). -/
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

/-! ## The bundle: `step_refines` -/

set_option maxHeartbeats 1000000

theorem step_refines {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (cmd : KernelCmd)
    (hR : R st bg a)
    (hCg : CgAgree cgInst content_gate st bg a)
    (hAu : AuAgree aInst authorizer st bg a)
    (hCf : CfAgree cfInst conformance bg a)
    (hRc : RcAgree cfInst conformance bg a)
    (hFlightUsed : ∀ ag I, a.in_flight ag I → a.invocation_used I)
    (hPre : StepPre st bg a cmd)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : kernelStep aInst cgInst cfInst authorizer content_gate conformance st bg cmd
      = .ok (.Ok (st', ev))) :
    ∃ a', (absActionOf cmd ev).guard a ∧ (absActionOf cmd ev).next a a' ∧ R st' bg a' := by
  cases cmd with
  | RegisterTool tool =>
      exact register_tool_preservesR st bg a tool hR hPre st' ev hok
  | UnregisterTool tool =>
      exact unregister_tool_preservesR st bg a tool hR st' ev hok
  | LoadInstruction agent instr =>
      exact load_instruction_preservesR st bg a agent instr hR hPre.1 hPre.2 st' ev hok
  | Delegate grantor grantee =>
      exact delegate_preservesR st bg a grantor grantee hR hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2
        st' ev hok
  | GrantCapability parent child cap =>
      exact grant_capability_preservesR st bg a parent child cap hR hPre.1 hPre.2 st' ev hok
  | Revoke parent target =>
      exact revoke_preservesR st bg a parent target hR st' ev hok
  | CascadeRevoke child parent =>
      exact cascade_revoke_preservesR st bg a child parent hR st' ev hok
  | InvokeStart agent tool inv attested_egress =>
      obtain ⟨hcapFlow, hcapInteg, hcapOvE, hcapOvJoint, hcapInvT, hcapInflE, hcapInflS,
        hcapUsed, hcapEgress, hinvtool, hEgAgree⟩ := hPre
      exact invoke_start_preservesR aInst cgInst st bg authorizer content_gate a agent tool inv
        attested_egress hR hCg hAu hEgAgree hinvtool hFlightUsed hcapFlow hcapInteg hcapOvE
        hcapOvJoint hcapInvT hcapInflE hcapInflS hcapUsed hcapEgress st' ev hok
  | InvokeComplete agent inv =>
      obtain ⟨hcapBudget, hcapTaintE, hcapTaintS, hcapIntegE, hcapIntegS⟩ := hPre
      -- Learn which branch fired from the returned event, then dispatch the split pair.
      obtain ⟨-, -, tool, tmeta, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hBranch⟩ :=
        invoke_complete_inv_full cfInst st bg conformance agent inv (cfOfAgree hCf agent inv)
          (fun t s => cfOfAgree_ok hCf agent inv t s) hR.wfInflight hcapBudget hcapTaintE
          hcapTaintS hcapIntegE hcapIntegS st' ev hok
      rcases hBranch with ⟨hEv, -, -, -, -, -⟩ | ⟨hEv, -, -, -, -, -, -⟩ <;> subst hEv
      · exact invoke_complete_endorsed_preservesR cfInst st bg conformance a agent inv
          (cfOfAgree hCf agent inv) (fun t s => cfOfAgree_ok hCf agent inv t s)
          (fun t => cfOfAgree_iff hCf agent inv t) hR hcapBudget hcapTaintE hcapTaintS
          hcapIntegE hcapIntegS st' hok
      · exact invoke_complete_unendorsed_preservesR cfInst st bg conformance a agent inv
          (cfOfAgree hCf agent inv) (fun t s => cfOfAgree_ok hCf agent inv t s)
          (fun t => cfOfAgree_iff hCf agent inv t) hR hcapBudget hcapTaintE hcapTaintS
          hcapIntegE hcapIntegS st' hok
  | ReturnEndorsed child parent clvl ilvl =>
      exact return_endorsed_preservesR cfInst st bg conformance a child parent clvl ilvl
        (rcOfAgree hRc child parent) (rcOfAgree_ok hRc child parent)
        (rcOfAgree_iff hRc child parent) hR hPre st' ev hok
  | ReturnUnendorsed child parent =>
      obtain ⟨hcapTaintE, hcapTaintJ, hcapTaintO, hcapIntegE, hcapIntegJ, hcapIntegO, hcapOvE,
        hcapOvJ, hcapCons⟩ := hPre
      exact return_unendorsed_preservesR cgInst st bg content_gate a child parent hR hCg
        hFlightUsed hcapTaintE hcapTaintJ hcapTaintO hcapIntegE hcapIntegJ hcapIntegO hcapOvE
        hcapOvJ hcapCons st' ev hok
  | SentinelElevateTaint agent level =>
      obtain ⟨hcapTaintE, hcapTaintS, hcapOvE, hcapOvJ, hcapCons⟩ := hPre
      exact sentinel_elevate_taint_preservesR cgInst st bg content_gate a agent level hR hCg
        hFlightUsed hcapTaintE hcapTaintS hcapOvE hcapOvJ hcapCons st' ev hok
  | SentinelDegradeIntegrity agent level =>
      exact sentinel_degrade_integrity_preservesR cgInst st bg content_gate a agent level hR hCg
        hPre.1 hPre.2 st' ev hok
  | SentinelCreditBudget agent amount =>
      exact sentinel_credit_budget_preservesR st bg a agent amount hR hPre st' ev hok
  | GrantOverride granter target tool level =>
      exact grant_override_preservesR st bg a granter target tool level hR
        hPre.1 hPre.2.1 hPre.2.2 st' ev hok

end ArgusLean.Refinement
