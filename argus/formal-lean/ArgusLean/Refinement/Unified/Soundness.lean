import ArgusLean.Refinement.Unified.Bundle
import ArgusLean.Refinement.Unified.InitRefinement
import Tzimtzum.Soundness.Bundle

/-! # Layer 2 — forward simulation + end-to-end soundness (C3)

The crown jewel: every reachable state of the extracted `argus-kernel` model satisfies the TzimtzumV2
safety bundle. Composed from:

* **init refinement** (`init_refines`) + **`step_refines`** (Layer 1) — a forward simulation
  `reachable_concrete_safe`: every reachable concrete state relates (under `R`) to a *reachable*
  abstract state;
* **`Tzimtzum.kav_soundP`** (the sort-polymorphic Kav soundness, C0) — every reachable abstract state
  satisfies `allInv`.

## The two honest assumptions

`implementation_sound` is stated with two explicit hypotheses that are *not* discharged, because they
cannot be without modelling resources or the (external, unverified) oracles:

* **`CapacityOK`** — the `Vec`-capacity bounds (`…length < Usize.max`) each transition needs. A `Vec`
  cannot grow past `usize::MAX` in practice, but proving it needs a resource model. Stated, not faked.
* **`OracleFidelity`** — the runtime `ContentGate` / `Authorizer` / `Conformance` oracles (the latter
  supplying both the `conforms` and the Campaign-B `return_conforms` verdict) agree, at every reachable
  state, with the fixed abstract oracle interpretation (`cgRel` / `auRel` / `cfRel` / `rcRel`). Per the
  guest-model ADR the oracles are external and unverified; this is the interface contract the
  refinement assumes of them. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

set_option maxHeartbeats 4000000

/-- Lift one abstract step (`absActionOf act` firing from `a` to `a'`) to the reachability closure of
    the TzimtzumV2 system: the closed action `closeN <action>` is in `system.actions`, and the
    parametrised guard/next witness its existential closure. -/
private abbrev sysActs : List (String × Kav.Action AbsState) :=
  (Tzimtzum.system : Kav.TransitionSystem AbsState).actions

private theorem mem_rt : ("register_tool", Kav.close1 Tzimtzum.register_tool) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_del : ("delegate", Kav.close2 Tzimtzum.delegate) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_gc : ("grant_capability", Kav.close3 Tzimtzum.grant_capability) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_rev : ("revoke", Kav.close2 Tzimtzum.revoke) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_casc : ("cascade_revoke", Kav.close2 Tzimtzum.cascade_revoke) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_is : ("invoke_start", Kav.close3 Tzimtzum.invoke_start) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_ic : ("invoke_complete", Kav.close2 Tzimtzum.invoke_complete) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_re : ("return_endorsed", Kav.close2 Tzimtzum.return_endorsed) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_ru : ("return_unendorsed", Kav.close2 Tzimtzum.return_unendorsed) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_set : ("sentinel_elevate_taint", Kav.close2 Tzimtzum.sentinel_elevate_taint) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_scb : ("sentinel_credit_budget", Kav.close2 Tzimtzum.sentinel_credit_budget) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_li : ("load_instruction", Kav.close2 Tzimtzum.load_instruction) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_go : ("grant_override", Kav.close4 Tzimtzum.grant_override) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

theorem absStep_reachable (a a' : AbsState) (act : event.KernelAction)
    (hreach : Kav.Reachable Tzimtzum.system a)
    (hguard : (absActionOf act).guard a) (hnext : (absActionOf act).next a a') :
    Kav.Reachable Tzimtzum.system a' :=
  match act, hguard, hnext with
  | .RegisterTool tool, hg, hn => Kav.Reachable.step mem_rt hreach ⟨tool, hg⟩ ⟨tool, hg, hn⟩
  | .Delegate grantor grantee, hg, hn =>
      Kav.Reachable.step mem_del hreach ⟨grantor, grantee, hg⟩ ⟨grantor, grantee, hg, hn⟩
  | .GrantCapability parent child cap, hg, hn =>
      Kav.Reachable.step mem_gc hreach ⟨parent, child, cap, hg⟩ ⟨parent, child, cap, hg, hn⟩
  | .Revoke parent target, hg, hn =>
      Kav.Reachable.step mem_rev hreach ⟨parent, target, hg⟩ ⟨parent, target, hg, hn⟩
  | .CascadeRevoke child parent, hg, hn =>
      Kav.Reachable.step mem_casc hreach ⟨child, parent, hg⟩ ⟨child, parent, hg, hn⟩
  | .InvokeStart agent tool inv, hg, hn =>
      Kav.Reachable.step mem_is hreach ⟨agent, tool, inv, hg⟩ ⟨agent, tool, inv, hg, hn⟩
  | .InvokeComplete agent inv, hg, hn =>
      Kav.Reachable.step mem_ic hreach ⟨agent, inv, hg⟩ ⟨agent, inv, hg, hn⟩
  | .ReturnEndorsed child parent, hg, hn =>
      Kav.Reachable.step mem_re hreach ⟨child, parent, hg⟩ ⟨child, parent, hg, hn⟩
  | .ReturnUnendorsed child parent, hg, hn =>
      Kav.Reachable.step mem_ru hreach ⟨child, parent, hg⟩ ⟨child, parent, hg, hn⟩
  | .SentinelElevateTaint agent level, hg, hn =>
      Kav.Reachable.step mem_set hreach ⟨agent, confA level, hg⟩ ⟨agent, confA level, hg, hn⟩
  | .SentinelCreditBudget agent amount, hg, hn =>
      Kav.Reachable.step mem_scb hreach ⟨agent, amount.val, hg⟩ ⟨agent, amount.val, hg, hn⟩
  | .LoadInstruction agent instr, hg, hn =>
      Kav.Reachable.step mem_li hreach ⟨agent, instr, hg⟩ ⟨agent, instr, hg, hn⟩
  | .GrantOverride granter target tool level, hg, hn =>
      Kav.Reachable.step mem_go hreach ⟨granter, target, tool, confA level, hg⟩
        ⟨granter, target, tool, confA level, hg, hn⟩

/-- The abstract oracle fields are immutable background — every action frames them — so a step never
    changes `content_gate_passes` / `authorizer_allows` / `output_conforms` / `return_conforms`. Lets
    the fixed oracle interpretation persist across the forward-simulation induction. -/
theorem absNext_oracle_frame (a a' : AbsState) (act : event.KernelAction)
    (hn : (absActionOf act).next a a') :
    a'.content_gate_passes = a.content_gate_passes ∧
    a'.authorizer_allows = a.authorizer_allows ∧ a'.output_conforms = a.output_conforms ∧
    a'.return_conforms = a.return_conforms := by
  cases act <;>
    simp only [absActionOf, Tzimtzum.register_tool, Tzimtzum.load_instruction, Tzimtzum.delegate,
      Tzimtzum.grant_capability, Tzimtzum.revoke, Tzimtzum.cascade_revoke, Tzimtzum.invoke_start,
      Tzimtzum.invoke_complete, Tzimtzum.return_endorsed, Tzimtzum.return_unendorsed,
      Tzimtzum.sentinel_elevate_taint, Tzimtzum.sentinel_credit_budget,
      Tzimtzum.grant_override] at hn <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> tauto

/-- Reachability closure of the extracted kernel: states reachable from `KernelState.initial` by any
    sequence of successful `kernelStep`s (under fixed oracle instances/params and background `bg`). -/
inductive ReachableConcrete {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F) (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory) : state.KernelState → Prop where
  | init {c : state.KernelState} (h : state.KernelState.initial = .ok c) :
      ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c
  | step {c c' : state.KernelState} {act ev : event.KernelAction}
      (hc : ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c)
      (hok : kernelStep aInst cgInst cfInst authorizer content_gate conformance c bg act
        = .ok (.Ok (c', ev))) :
      ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c'

/-- **Oracle-fidelity assumption.** At every reachable concrete state the runtime oracles agree with
    the fixed abstract interpretation (`cgRel` / `auRel` / `cfRel` / `rcRel`). The two conformance
    verdicts are state-independent, as the kernel's are. -/
def OracleFidelity {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F) (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory)
    (cgRel auRel cfRel : types.AgentId → types.ToolId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop) : Prop :=
  ∀ c, ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c →
    (∀ ag t, ∃ b : Bool, cgInst.passes content_gate ag t c bg = .ok b ∧ (b = true ↔ cgRel ag t)) ∧
    (∀ ag t, ∃ b : Bool, aInst.allows authorizer ag t c bg = .ok b ∧ (b = true ↔ auRel ag t)) ∧
    (∀ ag t, ∃ b : Bool, (∀ s, cfInst.conforms conformance ag t s bg = .ok b) ∧ (b = true ↔ cfRel ag t)) ∧
    (∀ cc p, ∃ b : Bool, (∀ s, cfInst.return_conforms conformance cc p s bg = .ok b) ∧ (b = true ↔ rcRel cc p))

/-- **Capacity assumption.** Every fired transition's `Vec`-capacity precondition (`StepPre`) holds at
    every reachable concrete state. Not discharged — there is no resource model (see module header). -/
def CapacityOK {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F) (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory) : Prop :=
  ∀ c a act, ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c →
    R c bg a → StepPre c bg a act

/-- **Forward simulation.** Under the capacity + oracle-fidelity assumptions, every reachable concrete
    state relates (under `R`) to a *reachable* abstract state whose oracle fields are the fixed
    interpretation. Proved by induction on `ReachableConcrete`: init refinement seeds the base case,
    `step_refines` advances the step (its side-conditions discharged from the two assumptions), and
    `absStep_reachable` lifts the abstract step into `Kav.Reachable`. -/
theorem reachable_concrete_safe {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory)
    (cgRel auRel cfRel : types.AgentId → types.ToolId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop)
    (hfid : OracleFidelity aInst cgInst cfInst authorizer content_gate conformance bg
      cgRel auRel cfRel rcRel)
    (hcap : CapacityOK aInst cgInst cfInst authorizer content_gate conformance bg)
    (c : state.KernelState)
    (hc : ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c) :
    ∃ a, R c bg a ∧ Kav.Reachable Tzimtzum.system a ∧
      a.content_gate_passes = cgRel ∧ a.authorizer_allows = auRel ∧ a.output_conforms = cfRel ∧
      a.return_conforms = rcRel := by
  induction hc with
  | init h =>
    obtain ⟨a0, hinit, hR, hcg, hau, hcf, hrc⟩ := init_refines bg cgRel auRel cfRel rcRel _ h
    exact ⟨a0, hR, Kav.Reachable.init hinit, hcg, hau, hcf, hrc⟩
  | @step c c' act ev hcpre hok ih =>
    obtain ⟨a, hRca, hreacha, hcg, hau, hcf, hrc⟩ := ih
    obtain ⟨hfcg, hfau, hfcf, hfrc⟩ := hfid c hcpre
    have hCg : CgAgree cgInst content_gate c bg a := by
      unfold CgAgree; intro ag t; rw [hcg]; exact hfcg ag t
    have hAu : AuAgree aInst authorizer c bg a := by
      unfold AuAgree; intro ag t; rw [hau]; exact hfau ag t
    have hCf : CfAgree cfInst conformance bg a := by
      unfold CfAgree; intro ag t; rw [hcf]; exact hfcf ag t
    have hRc : RcAgree cfInst conformance bg a := by
      unfold RcAgree; intro cc p; rw [hrc]; exact hfrc cc p
    have hPre : StepPre c bg a act := hcap c a act hcpre hRca
    obtain ⟨a', hg, hn, hRc'a'⟩ := step_refines aInst cgInst cfInst authorizer content_gate
      conformance c bg a act hRca hCg hAu hCf hRc hPre c' ev hok
    obtain ⟨hcg', hau', hcf', hrc'⟩ := absNext_oracle_frame a a' act hn
    exact ⟨a', hRc'a', absStep_reachable a a' act hreacha hg hn,
      hcg'.trans hcg, hau'.trans hau, hcf'.trans hcf, hrc'.trans hrc⟩

/-- **Implementation soundness (crown of the refinement).** Under the explicit capacity +
    oracle-fidelity assumptions, every reachable state of the extracted `argus-kernel` model relates to
    an abstract state satisfying the *full* TzimtzumV2 invariant bundle (10 safeties + 16 strengthening
    invariants) — obtained by composing the forward simulation with the sort-polymorphic Kav soundness
    `Tzimtzum.kav_soundP`. -/
theorem implementation_sound {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory)
    (cgRel auRel cfRel : types.AgentId → types.ToolId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop)
    (hfid : OracleFidelity aInst cgInst cfInst authorizer content_gate conformance bg
      cgRel auRel cfRel rcRel)
    (hcap : CapacityOK aInst cgInst cfInst authorizer content_gate conformance bg)
    (c : state.KernelState)
    (hc : ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c) :
    ∃ a, R c bg a ∧ Tzimtzum.allInv a := by
  obtain ⟨a, hR, hreach, _, _, _, _⟩ :=
    reachable_concrete_safe aInst cgInst cfInst authorizer content_gate conformance bg
      cgRel auRel cfRel rcRel hfid hcap c hc
  exact ⟨a, hR, Tzimtzum.kav_soundP a hreach⟩

end ArgusLean.Refinement

