import ArgusLean.Refinement.Unified.Bundle
import ArgusLean.Refinement.Unified.InitRefinement
import Tzimtzum.Soundness.Bundle

/-! # Layer 2 — V4 forward simulation and implementation soundness

Every successful step of the extracted twelve-command kernel simulates exactly one TzimtzumV4
system action. Composing V4 initialization, `step_refines`, abstract reachability, and
`Tzimtzum.kav_soundP` yields `implementation_sound`: every reachable extracted state relates to an
abstract state satisfying all 32 V4 invariants.

## Explicit trust assumptions

* `CapacityOK` states initialization root coherence and the exact branch-specific collection bounds
  needed by each successful extracted transition. It also fixes the per-invocation policy snapshot
  prediction and retains the explicit `grant_crossing n < 2^32` boundary obligation.
* `OracleFidelity` contains only the authorizer verdict and egress classification supplied to a
  successful `begin_invocation`. Inspection, quarantine resolution, and crossing conformance are
  explicit scoped one-use attestations checked by the kernel and are not oracle assumptions.

Neither assumption is hidden in concrete reachability.
-/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

set_option maxHeartbeats 4000000

private abbrev sysActs : List (String × Kav.Action AbsState) :=
  (Tzimtzum.system : Kav.TransitionSystem AbsState).actions

private theorem mem_register :
    ("register_tool", Kav.close1 Tzimtzum.register_tool) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_unregister :
    ("unregister_tool", Kav.close1 Tzimtzum.unregister_tool) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_delegate :
    ("delegate", Kav.close2 Tzimtzum.delegate) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_grant_capability :
    ("grant_capability", Kav.close3 Tzimtzum.grant_capability) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_grant_crossing :
    ("grant_crossing", Kav.close4 Tzimtzum.grant_crossing) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_revoke :
    ("revoke", Kav.close2 Tzimtzum.revoke) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_cascade :
    ("cascade_revoke", Kav.close2 Tzimtzum.cascade_revoke) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_ingest :
    ("ingest", Kav.close5 Tzimtzum.ingest) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_begin :
    ("begin_invocation", Kav.close8 Tzimtzum.begin_invocation) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_authorize :
    ("authorize_inspected", Kav.close4 Tzimtzum.authorize_inspected) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_settle :
    ("settle_invocation", Kav.close7 Tzimtzum.settle_invocation) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

private theorem mem_cross :
    ("cross_output", Kav.close3 Tzimtzum.cross_output) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

/-- Lift the command-indexed abstract step into the reachability closure of the twelve-action V4
system. -/
theorem absStep_reachable
    (snapRel : types.InvocationId → AbsSnapshot)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (auRel : types.InvocationId → Prop)
    (a a' : AbsState) (cmd : KernelCmd)
    (hreach : Kav.Reachable Tzimtzum.system a)
    (hstep : AbsStep snapRel egRel auRel cmd a a') :
    Kav.Reachable Tzimtzum.system a' := by
  cases cmd with
  | RegisterTool tool =>
      exact Kav.Reachable.step mem_register hreach ⟨tool, hstep.1⟩
        ⟨tool, hstep.1, hstep.2⟩
  | UnregisterTool tool =>
      exact Kav.Reachable.step mem_unregister hreach ⟨tool, hstep.1⟩
        ⟨tool, hstep.1, hstep.2⟩
  | Delegate grantor grantee =>
      exact Kav.Reachable.step mem_delegate hreach ⟨grantor, grantee, hstep.1⟩
        ⟨grantor, grantee, hstep.1, hstep.2⟩
  | GrantCapability parent child cap =>
      exact Kav.Reachable.step mem_grant_capability hreach ⟨parent, child, cap, hstep.1⟩
        ⟨parent, child, cap, hstep.1, hstep.2⟩
  | GrantCrossing grantor agent assignment n =>
      exact Kav.Reachable.step mem_grant_crossing hreach
        ⟨grantor, agent, assignment, n.val, hstep.1⟩
        ⟨grantor, agent, assignment, n.val, hstep.1, hstep.2⟩
  | Revoke parent target =>
      exact Kav.Reachable.step mem_revoke hreach ⟨parent, target, hstep.1⟩
        ⟨parent, target, hstep.1, hstep.2⟩
  | CascadeRevoke child parent =>
      exact Kav.Reachable.step mem_cascade hreach ⟨child, parent, hstep.1⟩
        ⟨child, parent, hstep.1, hstep.2⟩
  | Ingest agent src pconf pinteg =>
      obtain ⟨dispo, hg, hn⟩ := hstep
      exact Kav.Reachable.step mem_ingest hreach
        ⟨agent, src, confA pconf, integA pinteg, dispo, hg⟩
        ⟨agent, src, confA pconf, integA pinteg, dispo, hg, hn⟩
  | BeginInvocation agent inv chal snap egr ah authorized =>
      obtain ⟨verdict, hg, hn⟩ := hstep
      exact Kav.Reachable.step mem_begin hreach
        ⟨agent, inv, chal, snapRel inv, egRel inv, ah, auRel inv, verdict, hg⟩
        ⟨agent, inv, chal, snapRel inv, egRel inv, ah, auRel inv, verdict, hg, hn⟩
  | AuthorizeInspected inv att =>
      obtain ⟨scope, admit, hg, hn⟩ := hstep
      exact Kav.Reachable.step mem_authorize hreach
        ⟨inv, scope, inspectionA att, admit, hg⟩
        ⟨inv, scope, inspectionA att, admit, hg, hn⟩
  | SettleInvocation inv outcome att =>
      obtain ⟨agent, dispo, clvl, ilvl, hg, hn⟩ := hstep
      exact Kav.Reachable.step mem_settle hreach
        ⟨inv, agent, dispo, outcomeA outcome, clvl, ilvl, att.map resolutionA, hg⟩
        ⟨inv, agent, dispo, outcomeA outcome, clvl, ilvl, att.map resolutionA, hg, hn⟩
  | CrossOutput q =>
      obtain ⟨branch, dispo, hg, hn⟩ := hstep
      exact Kav.Reachable.step mem_cross hreach ⟨crossA q, branch, dispo, hg⟩
        ⟨crossA q, branch, dispo, hg, hn⟩

/-- Reachability of the pure extracted kernel under fixed governed background. No capacity,
root-coherence, or oracle premise is baked into this relation. -/
inductive ReachableConcrete (bg : background.BackgroundTheory) : state.KernelState → Prop where
  | init {c : state.KernelState} (h : state.KernelState.initial = .ok c) :
      ReachableConcrete bg c
  | step {c c' : state.KernelState} {cmd : KernelCmd} {ev : event.KernelAction}
      (hc : ReachableConcrete bg c)
      (hok : kernelStep c bg cmd = .ok (.Ok (c', ev))) :
      ReachableConcrete bg c'

/-- The narrowed V4 oracle-fidelity contract, required only for successful begin commands. -/
def OracleFidelity (bg : background.BackgroundTheory)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (auRel : types.InvocationId → Prop) : Prop :=
  ∀ c c' cmd ev, ReachableConcrete bg c →
    kernelStep c bg cmd = .ok (.Ok (c', ev)) → StepFidelity egRel auRel cmd

/-- The explicit extraction/resource contract. Root coherence is required at initialization;
`StepPre` is required only for commands that actually fire from a reachable related state. -/
structure CapacityOK (bg : background.BackgroundTheory)
    (snapRel : types.InvocationId → AbsSnapshot) : Prop where
  root_coherent : types.AgentId.root = .ok bg.root_agent
  step_capacity : ∀ c a cmd c' ev, ReachableConcrete bg c → R c bg a →
    kernelStep c bg cmd = .ok (.Ok (c', ev)) → StepPre c a snapRel cmd

/-- Forward simulation: every reachable concrete V4 state relates to a reachable abstract V4
state. -/
theorem reachable_concrete_safe
    (bg : background.BackgroundTheory)
    (snapRel : types.InvocationId → AbsSnapshot)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (auRel : types.InvocationId → Prop)
    (hfid : OracleFidelity bg egRel auRel)
    (hcap : CapacityOK bg snapRel)
    (c : state.KernelState) (hc : ReachableConcrete bg c) :
    ∃ a, R c bg a ∧ Kav.Reachable Tzimtzum.system a := by
  induction hc with
  | init h =>
      obtain ⟨a0, hinit, hR⟩ := init_refines bg hcap.root_coherent _ h
      exact ⟨a0, hR, Kav.Reachable.init hinit⟩
  | @step c c' cmd ev hcpre hok ih =>
      obtain ⟨a, hR, hreach⟩ := ih
      have hAll : Tzimtzum.allInv a := Tzimtzum.kav_soundP a hreach
      have hScoped : Tzimtzum.challenge_scoped a := hAll.challenge_scoped
      have hPre : StepPre c a snapRel cmd :=
        hcap.step_capacity c a cmd c' ev hcpre hR hok
      have hFid : StepFidelity egRel auRel cmd := hfid c c' cmd ev hcpre hok
      obtain ⟨a', hstep, hR'⟩ :=
        step_refines c bg a snapRel egRel auRel cmd hR hScoped hPre hFid c' ev hok
      exact ⟨a', hR', absStep_reachable snapRel egRel auRel a a' cmd hreach hstep⟩

/-- **V4 implementation soundness.** Modulo only `CapacityOK`, `OracleFidelity`, and the documented
extractor/opaque-operation trust seams, every reachable state of the extracted kernel refines a
TzimtzumV4 state satisfying the complete 32-invariant bundle over all twelve actions. -/
theorem implementation_sound
    (bg : background.BackgroundTheory)
    (snapRel : types.InvocationId → AbsSnapshot)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (auRel : types.InvocationId → Prop)
    (hfid : OracleFidelity bg egRel auRel)
    (hcap : CapacityOK bg snapRel)
    (c : state.KernelState) (hc : ReachableConcrete bg c) :
    ∃ a, R c bg a ∧ Tzimtzum.allInv a := by
  obtain ⟨a, hR, hreach⟩ :=
    reachable_concrete_safe bg snapRel egRel auRel hfid hcap c hc
  exact ⟨a, hR, Tzimtzum.kav_soundP a hreach⟩

#print axioms implementation_sound

end ArgusLean.Refinement
