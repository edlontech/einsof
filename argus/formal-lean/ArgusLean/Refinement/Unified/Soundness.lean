import ArgusLean.Refinement.Unified.Bundle
import ArgusLean.Refinement.Unified.InitRefinement
import Tzimtzum.Soundness.Bundle

/-! # Layer 2 — forward simulation + end-to-end soundness (C3)

The crown jewel, redone for V3 (task 14): every reachable state of the extracted `argus-kernel`
model satisfies the TzimtzumV3 safety bundle (`allInv`: 11 safeties + 15 strengthening
invariants over 16 actions). Composed from:

* **init refinement** (`init_refines`) + **`step_refines`** (Layer 1) — a forward simulation
  `reachable_concrete_safe`: every reachable concrete state relates (under `R`) to a *reachable*
  abstract state;
* **`Tzimtzum.kav_soundP`** (the sort-polymorphic Kav soundness, C0) — every reachable abstract
  state satisfies `allInv`. The soundness of the reached abstract state also feeds
  `in_flight_implies_used` back into the NEXT step (the `hFlightUsed` hypothesis the V3
  per-invocation gate proofs need) — the strengthening invariant earns its keep right here.

## The two honest assumptions

`implementation_sound` is stated with two explicit hypotheses that are *not* discharged, because
they cannot be without modelling resources or the (external, unverified) oracles:

* **`CapacityOK`** — the `Vec`-capacity bounds (`…length < Usize.max`) each transition needs,
  plus `InvokeStart`'s two per-invocation oracle-seam predictions (the abstract tool binding and
  the fresh invocation's attested-egress agreement — the classifier's per-call verdicts, design
  §5.2/§5.3). A `Vec` cannot grow past `usize::MAX` in practice, but proving it needs a resource
  model. Stated, not faked.
* **`OracleFidelity`** — the runtime `ContentGate` / `Authorizer` / `Conformance` oracles agree,
  at every reachable state, with the fixed abstract PER-INVOCATION interpretation
  (`cgRel` / `auRel` / `cfRel : InvocationId → Prop`; `rcRel` pairwise — design §5.2 "Oracle
  verdict keying"). Per the guest-model ADR the oracles are external and unverified; this is the
  interface contract the refinement assumes of them. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

set_option maxHeartbeats 4000000

/-- Lift one abstract step (`absActionOf cmd ev` firing from `a` to `a'`) to the reachability
    closure of the TzimtzumV3 system. -/
private abbrev sysActs : List (String × Kav.Action AbsState) :=
  (Tzimtzum.system : Kav.TransitionSystem AbsState).actions

private theorem mem_rt : ("register_tool", Kav.close1 Tzimtzum.register_tool) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_ut : ("unregister_tool", Kav.close1 Tzimtzum.unregister_tool) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_li : ("load_instruction", Kav.close2 Tzimtzum.load_instruction) ∈ sysActs := by
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
private theorem mem_ice :
    ("invoke_complete_endorsed", Kav.close2 Tzimtzum.invoke_complete_endorsed) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_icu :
    ("invoke_complete_unendorsed", Kav.close2 Tzimtzum.invoke_complete_unendorsed) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_re : ("return_endorsed", Kav.close4 Tzimtzum.return_endorsed) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_ru :
    ("return_unendorsed", Kav.close2 Tzimtzum.return_unendorsed) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_set :
    ("sentinel_elevate_taint", Kav.close2 Tzimtzum.sentinel_elevate_taint) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_sdi :
    ("sentinel_degrade_integrity", Kav.close2 Tzimtzum.sentinel_degrade_integrity) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_scb :
    ("sentinel_credit_budget", Kav.close2 Tzimtzum.sentinel_credit_budget) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]
private theorem mem_go : ("grant_override", Kav.close4 Tzimtzum.grant_override) ∈ sysActs := by
  simp [sysActs, Tzimtzum.system]

theorem absStep_reachable (a a' : AbsState) (cmd : KernelCmd) (ev : event.KernelAction)
    (hreach : Kav.Reachable Tzimtzum.system a)
    (hguard : (absActionOf cmd ev).guard a) (hnext : (absActionOf cmd ev).next a a') :
    Kav.Reachable Tzimtzum.system a' := by
  cases cmd with
  | RegisterTool tool =>
      exact Kav.Reachable.step mem_rt hreach ⟨tool, hguard⟩ ⟨tool, hguard, hnext⟩
  | UnregisterTool tool =>
      exact Kav.Reachable.step mem_ut hreach ⟨tool, hguard⟩ ⟨tool, hguard, hnext⟩
  | LoadInstruction agent instr =>
      exact Kav.Reachable.step mem_li hreach ⟨agent, instr, hguard⟩ ⟨agent, instr, hguard, hnext⟩
  | Delegate grantor grantee =>
      exact Kav.Reachable.step mem_del hreach ⟨grantor, grantee, hguard⟩
        ⟨grantor, grantee, hguard, hnext⟩
  | GrantCapability parent child cap =>
      exact Kav.Reachable.step mem_gc hreach ⟨parent, child, cap, hguard⟩
        ⟨parent, child, cap, hguard, hnext⟩
  | Revoke parent target =>
      exact Kav.Reachable.step mem_rev hreach ⟨parent, target, hguard⟩
        ⟨parent, target, hguard, hnext⟩
  | CascadeRevoke child parent =>
      exact Kav.Reachable.step mem_casc hreach ⟨child, parent, hguard⟩
        ⟨child, parent, hguard, hnext⟩
  | InvokeStart agent tool inv attested_egress =>
      exact Kav.Reachable.step mem_is hreach ⟨agent, tool, inv, hguard⟩
        ⟨agent, tool, inv, hguard, hnext⟩
  | InvokeComplete agent inv =>
      cases ev with
      | InvokeComplete a2 i2 b =>
          cases b with
          | true =>
              exact Kav.Reachable.step mem_ice hreach ⟨agent, inv, hguard⟩
                ⟨agent, inv, hguard, hnext⟩
          | false =>
              exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩
                ⟨agent, inv, hguard, hnext⟩
      | RegisterTool _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | UnregisterTool _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | LoadInstruction _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | Delegate _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | GrantCapability _ _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | Revoke _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | CascadeRevoke _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | InvokeStart _ _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | ReturnEndorsed _ _ _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | ReturnUnendorsed _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | SentinelElevateTaint _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | SentinelDegradeIntegrity _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | SentinelCreditBudget _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
      | GrantOverride _ _ _ _ =>
          exact Kav.Reachable.step mem_icu hreach ⟨agent, inv, hguard⟩ ⟨agent, inv, hguard, hnext⟩
  | ReturnEndorsed child parent clvl ilvl =>
      exact Kav.Reachable.step mem_re hreach ⟨child, parent, confA clvl, integA ilvl, hguard⟩
        ⟨child, parent, confA clvl, integA ilvl, hguard, hnext⟩
  | ReturnUnendorsed child parent =>
      exact Kav.Reachable.step mem_ru hreach ⟨child, parent, hguard⟩
        ⟨child, parent, hguard, hnext⟩
  | SentinelElevateTaint agent level =>
      exact Kav.Reachable.step mem_set hreach ⟨agent, confA level, hguard⟩
        ⟨agent, confA level, hguard, hnext⟩
  | SentinelDegradeIntegrity agent level =>
      exact Kav.Reachable.step mem_sdi hreach ⟨agent, integA level, hguard⟩
        ⟨agent, integA level, hguard, hnext⟩
  | SentinelCreditBudget agent amount =>
      exact Kav.Reachable.step mem_scb hreach ⟨agent, amount.val, hguard⟩
        ⟨agent, amount.val, hguard, hnext⟩
  | GrantOverride granter target tool level =>
      exact Kav.Reachable.step mem_go hreach ⟨granter, target, tool, confA level, hguard⟩
        ⟨granter, target, tool, confA level, hguard, hnext⟩

/-- The abstract per-invocation oracle fields are immutable background — every action frames
    them — so a step never changes `invocation_gate_passes` / `invocation_authorized` /
    `invocation_conforms` / `return_conforms`. Lets the fixed oracle interpretation persist
    across the forward-simulation induction. -/
theorem absNext_oracle_frame (a a' : AbsState) (cmd : KernelCmd) (ev : event.KernelAction)
    (hn : (absActionOf cmd ev).next a a') :
    a'.invocation_gate_passes = a.invocation_gate_passes ∧
    a'.invocation_authorized = a.invocation_authorized ∧
    a'.invocation_conforms = a.invocation_conforms ∧
    a'.return_conforms = a.return_conforms := by
  cases cmd <;>
    first
    | (simp only [absActionOf, Tzimtzum.register_tool, Tzimtzum.unregister_tool,
        Tzimtzum.load_instruction, Tzimtzum.delegate, Tzimtzum.grant_capability, Tzimtzum.revoke,
        Tzimtzum.cascade_revoke, Tzimtzum.invoke_start, Tzimtzum.return_endorsed,
        Tzimtzum.return_unendorsed, Tzimtzum.sentinel_elevate_taint,
        Tzimtzum.sentinel_degrade_integrity, Tzimtzum.sentinel_credit_budget,
        Tzimtzum.grant_override] at hn
       refine ⟨?_, ?_, ?_, ?_⟩ <;> tauto)
    | skip
  case InvokeComplete agent inv =>
    cases ev <;>
      first
      | (simp only [absActionOf, Tzimtzum.invoke_complete_unendorsed] at hn
         refine ⟨?_, ?_, ?_, ?_⟩ <;> tauto)
      | skip
    case InvokeComplete a2 i2 b =>
      cases b <;>
        (simp only [absActionOf, Tzimtzum.invoke_complete_endorsed,
          Tzimtzum.invoke_complete_unendorsed] at hn
         refine ⟨?_, ?_, ?_, ?_⟩ <;> tauto)

/-- Reachability closure of the extracted kernel: states reachable from `KernelState.initial` by
    any sequence of successful `kernelStep`s (under fixed oracle instances/params and background
    `bg`). -/
inductive ReachableConcrete {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F) (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory) : state.KernelState → Prop where
  | init {c : state.KernelState} (h : state.KernelState.initial = .ok c) :
      ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c
  | step {c c' : state.KernelState} {cmd : KernelCmd} {ev : event.KernelAction}
      (hc : ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c)
      (hok : kernelStep aInst cgInst cfInst authorizer content_gate conformance c bg cmd
        = .ok (.Ok (c', ev))) :
      ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c'

/-- **Oracle-fidelity assumption.** At every reachable concrete state the runtime oracles agree
    with the fixed abstract PER-INVOCATION interpretation (design §5.2 "Oracle verdict keying").
    The conformance verdicts are state-independent, as the kernel's are. -/
def OracleFidelity {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F) (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory)
    (cgRel auRel cfRel : types.InvocationId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop) : Prop :=
  ∀ c, ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c →
    (∀ ag t inv, ∃ b : Bool,
      cgInst.passes content_gate ag t inv c bg = .ok b ∧ (b = true ↔ cgRel inv)) ∧
    (∀ ag t inv, ∃ b : Bool,
      aInst.allows authorizer ag t inv c bg = .ok b ∧ (b = true ↔ auRel inv)) ∧
    (∀ ag t inv, ∃ b : Bool,
      (∀ s, cfInst.conforms conformance ag t inv s bg = .ok b) ∧ (b = true ↔ cfRel inv)) ∧
    (∀ cc p, ∃ b : Bool,
      (∀ s, cfInst.return_conforms conformance cc p s bg = .ok b) ∧ (b = true ↔ rcRel cc p))

/-- **Capacity assumption.** Every fired command's precondition (`StepPre`: the `Vec`-capacity
    bounds, plus `InvokeStart`'s per-invocation tool-binding and attested-egress predictions)
    holds at every reachable concrete state. Not discharged — there is no resource model, and the
    two predictions are the per-call half of the oracle seam (see module header). -/
def CapacityOK {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F) (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory) : Prop :=
  ∀ c a cmd, ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c →
    R c bg a → StepPre c bg a cmd

/-- **Forward simulation.** Under the capacity + oracle-fidelity assumptions, every reachable
    concrete state relates (under `R`) to a *reachable* abstract state whose per-invocation
    oracle fields are the fixed interpretation. Proved by induction on `ReachableConcrete`: init
    refinement seeds the base case, `step_refines` advances the step (its side-conditions
    discharged from the two assumptions plus `in_flight_implies_used` at the reachable abstract
    state, via `Tzimtzum.kav_soundP`), and `absStep_reachable` lifts the abstract step into
    `Kav.Reachable`. -/
theorem reachable_concrete_safe {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory)
    (cgRel auRel cfRel : types.InvocationId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (hfid : OracleFidelity aInst cgInst cfInst authorizer content_gate conformance bg
      cgRel auRel cfRel rcRel)
    (hcap : CapacityOK aInst cgInst cfInst authorizer content_gate conformance bg)
    (c : state.KernelState)
    (hc : ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c) :
    ∃ a, R c bg a ∧ Kav.Reachable Tzimtzum.system a ∧
      a.invocation_gate_passes = cgRel ∧ a.invocation_authorized = auRel ∧
      a.invocation_conforms = cfRel ∧ a.return_conforms = rcRel := by
  induction hc with
  | init h =>
    obtain ⟨a0, hinit, hR, hcg, hau, hcf, hrc⟩ := init_refines bg cgRel auRel cfRel rcRel egRel _ h
    exact ⟨a0, hR, Kav.Reachable.init hinit, hcg, hau, hcf, hrc⟩
  | @step c c' cmd ev hcpre hok ih =>
    obtain ⟨a, hRca, hreacha, hcg, hau, hcf, hrc⟩ := ih
    obtain ⟨hfcg, hfau, hfcf, hfrc⟩ := hfid c hcpre
    have hCg : CgAgree cgInst content_gate c bg a := by
      unfold CgAgree; intro ag t inv; rw [hcg]; exact hfcg ag t inv
    have hAu : AuAgree aInst authorizer c bg a := by
      unfold AuAgree; intro ag t inv; rw [hau]; exact hfau ag t inv
    have hCf : CfAgree cfInst conformance bg a := by
      unfold CfAgree; intro ag t inv; rw [hcf]; exact hfcf ag t inv
    have hRc : RcAgree cfInst conformance bg a := by
      unfold RcAgree; intro cc p; rw [hrc]; exact hfrc cc p
    have hFlightUsed : ∀ ag I, a.in_flight ag I → a.invocation_used I := by
      have hinv := Tzimtzum.kav_soundP a hreacha
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hPre : StepPre c bg a cmd := hcap c a cmd hcpre hRca
    obtain ⟨a', hg, hn, hRc'a'⟩ := step_refines aInst cgInst cfInst authorizer content_gate
      conformance c bg a cmd hRca hCg hAu hCf hRc hFlightUsed hPre c' ev hok
    obtain ⟨hcg', hau', hcf', hrc'⟩ := absNext_oracle_frame a a' cmd ev hn
    exact ⟨a', hRc'a', absStep_reachable a a' cmd ev hreacha hg hn,
      hcg'.trans hcg, hau'.trans hau, hcf'.trans hcf, hrc'.trans hrc⟩

/-- **Implementation soundness (crown of the refinement).** Under the explicit capacity +
    oracle-fidelity assumptions, every reachable state of the extracted `argus-kernel` model
    relates to an abstract state satisfying the *full* TzimtzumV3 invariant bundle (11 safeties +
    15 strengthening invariants over 16 actions) — obtained by composing the forward simulation
    with the sort-polymorphic Kav soundness `Tzimtzum.kav_soundP`. -/
theorem implementation_sound {A C F : Type}
    (aInst : traits.AuthorizerOracle A) (cgInst : traits.ContentGateOracle C)
    (cfInst : traits.ConformanceOracle F)
    (authorizer : A) (content_gate : C) (conformance : F)
    (bg : background.BackgroundTheory)
    (cgRel auRel cfRel : types.InvocationId → Prop)
    (rcRel : types.AgentId → types.AgentId → Prop)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (hfid : OracleFidelity aInst cgInst cfInst authorizer content_gate conformance bg
      cgRel auRel cfRel rcRel)
    (hcap : CapacityOK aInst cgInst cfInst authorizer content_gate conformance bg)
    (c : state.KernelState)
    (hc : ReachableConcrete aInst cgInst cfInst authorizer content_gate conformance bg c) :
    ∃ a, R c bg a ∧ Tzimtzum.allInv a := by
  obtain ⟨a, hR, hreach, _, _, _, _⟩ :=
    reachable_concrete_safe aInst cgInst cfInst authorizer content_gate conformance bg
      cgRel auRel cfRel rcRel egRel hfid hcap c hc
  exact ⟨a, hR, Tzimtzum.kav_soundP a hreach⟩

end ArgusLean.Refinement
