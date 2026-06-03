import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `return_unendorsed` preserves the unified `R`

Proved by **reuse** of `return_unendorsed_refines`: `Rretu` carries no budget clause and already reads
every field through `R`'s canonical views (`vmsMemLast` for the propagated `taint_levels` /
`gh_taint_received`, the get-style `vmLastEntry` parent edge), so it projects cleanly from `R` and its
output covers 11 of the unified conjuncts verbatim — no taint/gh view bridge is needed (unlike
`sentinel_elevate_taint`). The remaining conjuncts (the untouched fields + the three written maps' nodup
posts + the full metadata `wfInflight`) transport via the abstract frames (`hnext`), the concrete frames
+ nodup posts (`return_unendorsed_inv_full`), and `R.wfInflight`. The content gate is the one opaque
oracle (`cgOf`/`hcg`/`hcgA`, from `CgAgree` in the bundle). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Re-run of the `return_unendorsed` inversion exposing the concrete frames (every untouched map
    unchanged) and the `vmNodupKeys` posts for the three written maps (`taint_levels` /
    `gh_taint_received` via the `child_taint` extends, `override_used` via the `to_consume` extend). -/
theorem return_unendorsed_inv_full {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (child parent : types.AgentId)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate parent t st bg = .ok (cgOf t))
    (hcapLoop : vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintJoint : ∀ p ∈ st.taint_levels.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapTaintChild : vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapGhrE : st.gh_taint_received.entries.val.length < Usize.max)
    (hcapGhrJoint : ∀ p ∈ st.gh_taint_received.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_unendorsed cgInst st bg content_gate child parent
      = .ok (.Ok (st', ev))) :
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.invocation_tool = st.invocation_tool ∧ st'.tool_registered = st.tool_registered ∧
    st'.gh_taint_invoked = st.gh_taint_invoked ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧
    (vmNodupKeys st.taint_levels → vmNodupKeys st'.taint_levels) ∧
    (vmNodupKeys st.gh_taint_received → vmNodupKeys st'.gh_taint_received) ∧
    (vmNodupKeys st.override_used → vmNodupKeys st'.override_used) := by
  simp only [transitions.return_unendorsed] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨b, hbEq, hbIff⟩ :
      ∃ bb, core.option.Option.Insts.CoreCmpPartialEqOption.ne
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId) o (some parent) =
        .ok bb ∧ (bb = true ↔ o ≠ some parent) :=
    ⟨_, optionAgentId_ne_spec o (some parent), by simp⟩
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
  have hb : b = false := by cases b with | false => rfl | true => simp at hok
  simp only [hb, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hb2Eq] at hok; simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists
    (vecMapKVecSetSetNonempty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight child)
  rw [hb3Eq] at hok; simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨ct, hctEq, _hctMem, hctLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec st.taint_levels child)
  rw [hctEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨pf, hpfEq, _hpfMem, hpfLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight parent)
  rw [hpfEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨acc, hloopEq, _hDen, _hCon, _hNd, hLen⟩ := spec_imp_exists
    (returnUnendOuter_spec cgInst st bg content_gate parent cgOf hcg ct pf
      { denied := false, to_consume := vs }
      (by show vs.items.val.length + ct.items.val.length * pf.items.val.length ≤ Usize.max
          rw [hvsNil, hctLen, hpfLen]; simpa using hcapLoop)
      { denied := false, to_consume := vs } 0#usize
      (by simp) (by show vs.items.val.Nodup; rw [hvsNil]; exact List.nodup_nil)
      (by simp) (by simp) (by simp))
  rw [hloopEq] at hok; simp only [bind_tc_ok] at hok
  have hDenF : acc.denied = false := by
    cases hd : acc.denied with | false => rfl | true => simp [hd] at hok
  simp only [hDenF, reduceIte, Bool.false_eq_true] at hok
  have hAccLen : acc.to_consume.items.val.length ≤
      vmSetLen st.taint_levels child * vmSetLen st.in_flight parent := by
    have h := hLen; rw [hvsNil, hctLen, hpfLen] at h; simpa using h
  obtain ⟨b4, hb4Eq, _hb4Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.ConfLevel.Insts.CoreCloneClone
      types.ConfLevel.Insts.CoreCmpPartialEqConfLevel ct)
  rw [hb4Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm, vm1, hvmEq, hvmNd, hvm1Nd⟩ : ∃ vm vm1,
      (if b4 = true then Result.ok (st.taint_levels, st.gh_taint_received)
       else (do
         let ai ← types.AgentId.Insts.CoreCloneClone.clone parent
         let vm2 ← collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
           types.ConfLevel.Insts.CoreCmpPartialEqConfLevel st.taint_levels ai ct
         let vm3 ← collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
           types.ConfLevel.Insts.CoreCmpPartialEqConfLevel st.gh_taint_received ai ct
         ok (vm2, vm3))) = Result.ok (vm, vm1) ∧
      (vmNodupKeys st.taint_levels → vmNodupKeys vm) ∧
      (vmNodupKeys st.gh_taint_received → vmNodupKeys vm1) := by
    cases hb4 : b4 with
    | true => exact ⟨st.taint_levels, st.gh_taint_received, by rw [if_pos rfl], id, id⟩
    | false =>
      obtain ⟨vm2, hvm2Eq, hvm2Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels parent ct hcapTaintE
          (by intro p hp; rw [hctLen]; exact hcapTaintJoint p hp)
          (by rw [hctLen]; exact hcapTaintChild))
      obtain ⟨vm3, hvm3Eq, hvm3Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.gh_taint_received parent ct hcapGhrE
          (by intro p hp; rw [hctLen]; exact hcapGhrJoint p hp)
          (by rw [hctLen]; exact hcapTaintChild))
      refine ⟨vm2, vm3, ?_, hvm2Nd, hvm3Nd⟩
      simp only [Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok, hvm2Eq, hvm3Eq]
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  simp at hok
  obtain ⟨b5, hb5Eq, _hb5Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc.to_consume)
  rw [hb5Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨ou, houEq, houNd⟩ : ∃ ou,
      (if b5 = true then
        Result.ok (core.result.Result.Ok
          (({ st with taint_levels := vm, gh_taint_received := vm1 } : state.KernelState),
           event.KernelAction.ReturnUnendorsed child parent))
       else (do
         let vm2 ← collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
           types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used parent acc.to_consume
         ok (core.result.Result.Ok
           (({ st with taint_levels := vm, gh_taint_received := vm1, override_used := vm2 }
              : state.KernelState),
            event.KernelAction.ReturnUnendorsed child parent)))) =
      Result.ok (core.result.Result.Ok
        (({ st with taint_levels := vm, gh_taint_received := vm1, override_used := ou }
           : state.KernelState),
         event.KernelAction.ReturnUnendorsed child parent)) ∧
      (vmNodupKeys st.override_used → vmNodupKeys ou) := by
    cases hb5 : b5 with
    | true => exact ⟨st.override_used, by rw [if_pos rfl], id⟩
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; omega
      obtain ⟨vm', hvm'Eq, hvm'Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used parent acc.to_consume
          hcapOvE hcapJ (le_trans hAccLen hcapLoop))
      refine ⟨vm', ?_, hvm'Nd⟩
      simp only [Bool.false_eq_true, reduceIte, bind_tc_ok, hvm'Eq]
  rw [houEq] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvmNd, hvm1Nd, houNd⟩

/-- `return_unendorsed` preserves the unified `R`. -/
theorem return_unendorsed_preservesR {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (child parent : types.AgentId)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate parent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes parent t)
    (hR : R st bg a)
    (hcapLoop : vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintJoint : ∀ p ∈ st.taint_levels.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapTaintChild : vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapGhrE : st.gh_taint_received.entries.val.length < Usize.max)
    (hcapGhrJoint : ∀ p ∈ st.gh_taint_received.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_unendorsed cgInst st bg content_gate child parent
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.return_unendorsed child parent).guard a ∧
          (Tzimtzum.return_unendorsed child parent).next a a' ∧ R st' bg a' := by
  -- project `R → Rretu` (every view canonical; the binding-totality conjunct from `R.wfInflight`)
  have hRretu : Rretu st bg a := ⟨hR.active, hR.parent, hR.inflight, hR.taint, hR.ghReceived,
    hR.override, hR.toolEgress, hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool,
    fun ag I hmem => by obtain ⟨t, _, ht, _⟩ := hR.wfInflight ag I hmem; rw [ht]; exact Option.some_ne_none t⟩
  obtain ⟨a', hguard, hnext, hRretu'⟩ :=
    return_unendorsed_refines cgInst st bg content_gate a child parent cgOf hcg hcgA hRretu
      hcapLoop hcapTaintE hcapTaintJoint hcapTaintChild hcapGhrE hcapGhrJoint hcapOvE hcapOvJoint
      st' ev hok
  obtain ⟨hf_act, hf_par, hf_cap, hf_infl, hf_invt, hf_reg, hf_ghinv, hf_instr, hf_bud,
      hNdTaint, hNdGhr, hNdOver⟩ :=
    return_unendorsed_inv_full cgInst st bg content_gate child parent cgOf hcg hcapLoop hcapTaintE
      hcapTaintJoint hcapTaintChild hcapGhrE hcapGhrJoint hcapOvE hcapOvJoint st' ev hok
  obtain ⟨hRact', hRparent', hRinfl', hRtaint', hRghr', hRov', hReg', hAllow', hInsp', hOvr',
      hInvtool', _hRwf'⟩ := hRretu'
  simp only [Tzimtzum.return_unendorsed] at hnext
  obtain ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allow, ha_insp, ha_ovr, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ha_caprefresh⟩ := hnext
  refine ⟨a', hguard, ?_, ?_⟩
  · simp only [Tzimtzum.return_unendorsed]
    exact ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allow, ha_insp, ha_ovr, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ha_caprefresh⟩
  · refine ⟨by rw [ha_root]; exact hR.root, by rw [ha_capdecl]; exact hR.cap_declass,
      by rw [ha_caprefresh]; exact hR.cap_refresh, hRact',
      fun t => by rw [ha_reg, hf_reg]; exact hR.tool_reg t, hRparent',
      fun N Cc => by rw [ha_cap, hf_cap]; exact hR.cap N Cc,
      fun ag ins => by rw [ha_instr, hf_instr]; exact hR.instr ag ins, hRtaint', hRinfl',
      fun ag L => by rw [ha_ghinv, hf_ghinv]; exact hR.ghInvoked ag L, hRghr', hRov',
      fun G L hG => by rw [ha_bud, hf_bud]; rw [ha_active] at hG; exact hR.budget G L hG,
      fun t tmeta Cc h => by rw [ha_toolcap]; exact hR.toolCap t tmeta Cc h, hReg',
      fun t tmeta h => by rw [ha_floor]; exact hR.toolFloor t tmeta h,
      fun t tmeta h => by rw [ha_ob]; exact hR.toolBounded t tmeta h,
      fun t tmeta h => by rw [ha_iss]; exact hR.toolIssuer t tmeta h,
      fun i => by rw [ha_trust]; exact hR.trustedIss i,
      fun i issuer h => by rw [ha_instriss]; exact hR.instrIssuer i issuer h, hAllow', hInsp', hOvr',
      hInvtool', by rw [hf_par]; exact hR.ndParent, by rw [hf_cap]; exact hR.ndCap,
      by rw [hf_instr]; exact hR.ndInstr, hNdTaint hR.ndTaint, by rw [hf_infl]; exact hR.ndInflight,
      by rw [hf_ghinv]; exact hR.ndGhInvoked, hNdGhr hR.ndGhReceived, hNdOver hR.ndOverride,
      by rw [hf_bud]; exact hR.ndBudget, fun ag I hmem => ?_⟩
    -- wfInflight: in_flight + invocation_tool unchanged
    have hmem' : vmsMemLast st.in_flight ag I := by rw [← hf_infl]; exact hmem
    obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hmem'
    exact ⟨t, tmeta, by unfold invToolC; rw [hf_invt]; exact ht, htm⟩

end ArgusLean.Refinement
