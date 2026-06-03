import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `invoke_start` preserves the unified `R`

Proved by **reuse** of `invoke_start_refines` (the heaviest action: three-check gate + speculative
taint). `Rstart` carries no budget clause and reads every field through `R`'s canonical views, so it
projects directly from `R` (it is `R` minus the budget/declassify/issuer/instr fields, plus the named
root and the full metadata `wfInflight` — all of which `R` provides). Its output covers 15 of the
unified conjuncts verbatim (including `root` and `wfInflight`). The remaining conjuncts transport via the
abstract frames (`hnext`), the concrete frames + nodup posts (`invoke_start_inv_full`), and `R`. The
abstract binding prediction `hinvtool : a.invocation_tool inv = tool` and the two opaque oracles
(content gate / authorizer, as `cgOf`/`auOf` + agreements) are supplied by the bundle. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Re-run of the `invoke_start` inversion exposing the concrete frames (every untouched map unchanged)
    and the `vmNodupKeys` posts for the two written set-maps (`in_flight` via the insert, `override_used`
    via the conditional `extend_into`). `invocation_tool`'s nodup is not needed (`R` reads it last-match,
    one-directionally — no `ndInvocationTool` conjunct). -/
theorem invoke_start_inv_full {A C : Type} (aInst : traits.AuthorizerOracle A)
    (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (authorizer : A) (content_gate : C)
    (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (cgOf : types.ToolId → Bool) (auOf : Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hau : aInst.allows authorizer agent tool st bg = .ok auOf)
    (hcapFlow : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
      + vmSetLen st.in_flight agent + 1 ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1) ≤ Usize.max)
    (hcapInvT : st.invocation_tool.entries.val.length < Usize.max)
    (hcapInflE : st.in_flight.entries.val.length < Usize.max)
    (hcapInflS : ∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_start aInst cgInst st bg authorizer content_gate agent tool inv
      = .ok (.Ok (st', ev))) :
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.taint_levels = st.taint_levels ∧
    st'.tool_registered = st.tool_registered ∧ st'.gh_taint_invoked = st.gh_taint_invoked ∧
    st'.gh_taint_received = st.gh_taint_received ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧
    (vmNodupKeys st.in_flight → vmNodupKeys st'.in_flight) ∧
    (vmNodupKeys st.override_used → vmNodupKeys st'.override_used) := by
  simp only [transitions.invoke_start] at hok
  obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  obtain ⟨ai, haiEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [haiEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :
      ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq agent ai = .ok bb ∧ (bb = true ↔ agent = ai) :=
    ⟨_, agentId_eq_spec agent ai, by simp⟩
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  have hb1 : b1 = false := by cases b1 with | false => rfl | true => simp at hok
  simp only [hb1, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hb2Eq] at hok; simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists
    (containsKey_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ToolId.Insts.CoreCloneClone st.invocation_tool inv)
  rw [hb3Eq] at hok; simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨b4, hb4Eq, hb4Iff⟩ := spec_imp_exists
    (anyValueContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      invocationId_clone_spec st.in_flight inv)
  rw [hb4Eq] at hok; simp only [bind_tc_ok] at hok
  have hb4 : b4 = false := by cases b4 with | false => rfl | true => simp at hok
  simp only [hb4, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists (toolMetadata_spec bg tool)
  rw [hoEq] at hok; simp only [bind_tc_ok] at hok
  cases hmcase : o with
  | none => rw [hmcase] at hok; simp at hok
  | some m =>
  rw [hmcase] at hok; simp only at hok
  obtain ⟨mc, hmcEq, hmcIff⟩ := spec_imp_exists
    (invokeStartLoop0_spec st.agent_cap agent m.capabilities false 0#usize (by simp) (by simp))
  rw [hmcEq] at hok; simp only [bind_tc_ok] at hok
  have hmcF : mc = false := by cases mc with | false => rfl | true => simp at hok
  simp only [hmcF, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨spec_taint, hstEq, hstMem, hstLen⟩ := spec_imp_exists
    (specTaint_spec st agent bg (by have := hcapFlow; omega))
  rw [hstEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨acc, haccEq, hAccDen, hAccCon, hAccNd, hAccLen⟩ := spec_imp_exists
    (invokeStartLoop1_spec cgInst st bg content_gate agent tool m.egress (cgOf tool) (hcg tool)
      spec_taint { denied := false, to_consume := vs }
      (by show vs.items.val.length + spec_taint.items.val.length ≤ Usize.max
          rw [hvsNil]; simp only [List.length_nil, Nat.zero_add]
          have := hstLen; have := hcapFlow; omega)
      { denied := false, to_consume := vs } 0#usize (by simp)
      (by show vs.items.val.Nodup; rw [hvsNil]; exact List.nodup_nil)
      (by simp) (by simp) (by simp))
  rw [haccEq] at hok; simp only [bind_tc_ok] at hok
  have hAccLen' : acc.to_consume.items.val.length ≤
      vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent := by
    have h := hAccLen; rw [hvsNil] at h; simp only [List.length_nil, Nat.zero_add] at h
    exact le_trans h hstLen
  obtain ⟨agent_flights, hflEq, hflMem, hflLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight agent)
  rw [hflEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨acc1, hacc1Eq, hAcc1Den, hAcc1Con, hAcc1Nd, hAcc1Len⟩ := spec_imp_exists
    (invokeStartLoop2_spec cgInst st bg content_gate agent m.conf_floor cgOf
      (ovC bg agent m.conf_floor) (ocC st agent m.conf_floor) hcg
      (fun t => ovC_eq bg agent m.conf_floor t) (fun t => ocC_eq st agent m.conf_floor t)
      agent_flights acc
      (by rw [hflLen]; have := hAccLen'; have := hcapFlow; omega)
      acc 0#usize (by simp) hAccNd (by simp) (by simp) (by simp))
  rw [hacc1Eq] at hok; simp only [bind_tc_ok] at hok
  have hAcc1Len' : acc1.to_consume.items.val.length ≤
      vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent + vmSetLen st.in_flight agent := by
    have h := hAcc1Len; rw [hflLen] at h; have := hAccLen'; omega
  obtain ⟨acc2, hacc2Eq, hAcc2Den, hAcc2Con, hAcc2Nd⟩ := spec_imp_exists
    (gateEgress_spec cgInst bg content_gate agent tool st m.conf_floor m.egress
      (cgOf tool) (ovC bg agent m.conf_floor tool) (ocC st agent m.conf_floor tool)
      (hcg tool) (ovC_eq bg agent m.conf_floor tool) (ocC_eq st agent m.conf_floor tool)
      (flowModeC bg m.conf_floor) (flowMode_eq bg m.conf_floor) acc1
      (by have := hAcc1Len'; have := hcapFlow; omega) hAcc1Nd)
  rw [hacc2Eq] at hok; simp only [bind_tc_ok] at hok
  have hAcc2Len : acc2.to_consume.items.val.length ≤
      vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1 := by
    have hsub : acc2.to_consume.items.val ⊆
        acc1.to_consume.items.val ++ [gateConsumeKey tool m.conf_floor] := by
      intro x hx
      rcases (hAcc2Con x).mp hx with hxL | ⟨hxk, _⟩
      · exact List.mem_append_left _ hxL
      · exact List.mem_append_right _ (by rw [hxk]; exact List.mem_singleton.mpr rfl)
    have hle := (List.Nodup.subperm hAcc2Nd hsub).length_le
    rw [List.length_append, List.length_singleton] at hle
    have := hAcc1Len'; omega
  have hDenF : acc2.denied = false := by
    cases hd : acc2.denied with | false => rfl | true => simp [hd] at hok
  simp only [hDenF, reduceIte, Bool.false_eq_true] at hok
  rw [hau] at hok; simp only [bind_tc_ok] at hok
  have hauT : auOf = true := by cases auOf with | true => rfl | false => simp at hok
  simp only [hauT, reduceIte] at hok
  obtain ⟨b6, hb6Eq, hb6Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc2.to_consume)
  rw [hb6Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmNd⟩ : ∃ vm,
      (if b6 = true then Result.ok st.override_used
       else (do
         let ai1 ← types.AgentId.Insts.CoreCloneClone.clone agent
         collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
           types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used ai1
           acc2.to_consume)) = Result.ok vm ∧
      (vmNodupKeys st.override_used → vmNodupKeys vm) := by
    cases hb6 : b6 with
    | true => exact ⟨st.override_used, by rw [if_pos rfl], id⟩
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc2.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; have := hAcc2Len; omega
      obtain ⟨vm', hvm'Eq, hvm'Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used agent acc2.to_consume
          hcapOvE hcapJ (by have := hAcc2Len; have := hcapFlow; omega))
      exact ⟨vm', by rw [if_neg (by simp), agentId_clone_spec]; simp only [bind_tc_ok]; exact hvm'Eq,
        hvm'Nd⟩
  rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
  rw [invocationId_clone_spec, toolId_clone_spec] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, _⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ToolId.Insts.CoreCloneClone st.invocation_tool inv tool hcapInvT)
  rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
  rw [agentId_clone_spec] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm2, hvm2Eq, hvm2Nd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_eq_spec invocationId_clone_spec st.in_flight agent inv hcapInflE hcapInflS)
  rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => hvm2Nd h, fun h => hvmNd h⟩

/-- `invoke_start` preserves the unified `R`. -/
theorem invoke_start_preservesR {A C : Type} (aInst : traits.AuthorizerOracle A)
    (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (authorizer : A) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (cgOf : types.ToolId → Bool) (auOf : Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes agent t)
    (hau : aInst.allows authorizer agent tool st bg = .ok auOf)
    (hauA : auOf = true ↔ a.authorizer_allows agent tool)
    (hinvtool : a.invocation_tool inv = tool)
    (hR : R st bg a)
    (hcapFlow : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
      + vmSetLen st.in_flight agent + 1 ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1) ≤ Usize.max)
    (hcapInvT : st.invocation_tool.entries.val.length < Usize.max)
    (hcapInflE : st.in_flight.entries.val.length < Usize.max)
    (hcapInflS : ∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_start aInst cgInst st bg authorizer content_gate agent tool inv
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.invoke_start agent tool inv).guard a ∧
          (Tzimtzum.invoke_start agent tool inv).next a a' ∧ R st' bg a' := by
  -- project `R → Rstart` (every view canonical; root + full metadata `wfInflight` from `R`)
  have hRstart : Rstart st bg a := ⟨hR.root, hR.active, hR.tool_reg, hR.cap, hR.inflight, hR.taint,
    hR.override, hR.toolEgress, hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool,
    hR.toolFloor, hR.toolCap, hR.wfInflight⟩
  obtain ⟨a', hguard, hnext, hRstart'⟩ :=
    invoke_start_refines aInst cgInst st bg authorizer content_gate a agent tool inv cgOf auOf hcg
      hcgA hau hauA hinvtool hRstart hcapFlow hcapOvE hcapOvJoint hcapInvT hcapInflE hcapInflS st' ev hok
  obtain ⟨_hf_act, hf_par, hf_cap, hf_taint, _hf_reg, hf_ghinv, hf_ghrec, hf_instr, hf_bud,
      hNdInfl, hNdOver⟩ :=
    invoke_start_inv_full aInst cgInst st bg authorizer content_gate agent tool inv cgOf auOf hcg hau
      hcapFlow hcapOvE hcapOvJoint hcapInvT hcapInflE hcapInflS st' ev hok
  obtain ⟨hRroot', hRact', hRreg', hRcap', hRinfl', hRtaint', hRov', hReg', hAllow', hInsp', hOvr',
      hInvtool', hRfloor', hRtoolcap', hRwf'⟩ := hRstart'
  simp only [Tzimtzum.invoke_start] at hnext
  obtain ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allow, ha_insp, ha_ovr, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ha_caprefresh⟩ := hnext
  refine ⟨a', hguard, ?_, ?_⟩
  · simp only [Tzimtzum.invoke_start]
    exact ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allow, ha_insp, ha_ovr, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ha_caprefresh⟩
  · refine ⟨hRroot', by rw [ha_capdecl]; exact hR.cap_declass,
      by rw [ha_caprefresh]; exact hR.cap_refresh, hRact', hRreg',
      fun Cc P => by rw [ha_parent, hf_par]; exact hR.parent Cc P, hRcap',
      fun ag ins => by rw [ha_instr, hf_instr]; exact hR.instr ag ins, hRtaint', hRinfl',
      fun ag L => by rw [ha_ghinv, hf_ghinv]; exact hR.ghInvoked ag L,
      fun ag L => by rw [ha_ghrec, hf_ghrec]; exact hR.ghReceived ag L, hRov',
      fun G L hG => by rw [ha_bud, hf_bud]; rw [ha_active] at hG; exact hR.budget G L hG,
      hRtoolcap', hReg', hRfloor',
      fun t tmeta h => by rw [ha_ob]; exact hR.toolBounded t tmeta h,
      fun t tmeta h => by rw [ha_iss]; exact hR.toolIssuer t tmeta h,
      fun i => by rw [ha_trust]; exact hR.trustedIss i,
      fun i issuer h => by rw [ha_instriss]; exact hR.instrIssuer i issuer h, hAllow', hInsp', hOvr',
      hInvtool', by rw [hf_par]; exact hR.ndParent, by rw [hf_cap]; exact hR.ndCap,
      by rw [hf_instr]; exact hR.ndInstr, by rw [hf_taint]; exact hR.ndTaint, hNdInfl hR.ndInflight,
      by rw [hf_ghinv]; exact hR.ndGhInvoked, by rw [hf_ghrec]; exact hR.ndGhReceived,
      hNdOver hR.ndOverride, by rw [hf_bud]; exact hR.ndBudget, hRwf'⟩

end ArgusLean.Refinement
