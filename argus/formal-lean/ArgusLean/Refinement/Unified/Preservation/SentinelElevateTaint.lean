import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `sentinel_elevate_taint` preserves the unified `R`

Proved by **reuse** of `sentinel_elevate_taint_refines`: the slice relation `Rsent` carries no budget
clause, so it projects cleanly from `R` (the taint/gh `vmsMem` views bridge to `R`'s canonical
`vmsMemLast` via `R.ndTaint`/`R.ndGhInvoked`). We then upgrade the slice output `Rsent st' bg a'` to the
unified `R st' bg a'`: the covered fields (active / in_flight / override / egress / flow / invocation)
come straight from `Rsent'`, the taint/gh fields bridge back through the *output* nodup posts
(`sentinel_elevate_taint_inv_full`), and the untouched fields transport via the abstract frames
(`hnext`) + the concrete frames (`_inv_full`) + `R`. The content gate is the one opaque oracle, supplied
as `cgOf`/`hcg`/`hcgA` (extracted from `CgAgree` in the bundle). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Re-run of the `sentinel_elevate_taint` inversion exposing the concrete frames (every untouched map
    unchanged) and the `vmNodupKeys` posts for the three written maps (`taint_levels`/`gh_taint_invoked`
    via the inserts, `override_used` via the conditional `extend_into`). -/
theorem sentinel_elevate_taint_inv_full {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcapInvs : inFlightLen st agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + inFlightLen st agent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.invocation_tool = st.invocation_tool ∧ st'.tool_registered = st.tool_registered ∧
    st'.gh_taint_received = st.gh_taint_received ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧
    (vmNodupKeys st.taint_levels → vmNodupKeys st'.taint_levels) ∧
    (vmNodupKeys st.gh_taint_invoked → vmNodupKeys st'.gh_taint_invoked) ∧
    (vmNodupKeys st.override_used → vmNodupKeys st'.override_used) := by
  simp only [transitions.sentinel_elevate_taint] at hok
  obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨invs, hinvsEq, hinvsMem, hinvsLen⟩ := spec_imp_exists (getSetOrEmptyInFlight_spec st agent)
  rw [hinvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨⟨acc, mb⟩, hloopEq, hMb, hDen, hCon, _hNd, hLen⟩ := spec_imp_exists
    (sentinelLoop_spec cgInst st bg content_gate agent level cgOf (ovC bg agent level)
      (ocC st agent level) hcg (fun t => ovC_eq bg agent level t)
      (fun t => ocC_eq st agent level t) invs { denied := false, to_consume := vs } false
      (by show vs.items.val.length + invs.items.val.length ≤ Usize.max
          rw [hvsNil, hinvsLen]; simpa using hcapInvs)
      { denied := false, to_consume := vs } false 0#usize
      (by simp) (by show vs.items.val.Nodup; rw [hvsNil]; exact List.nodup_nil)
      (by simp) (by simp) (by simp) (by simp))
  rw [hloopEq] at hok; simp only [bind_tc_ok] at hok
  have hmbF : mb = false := by cases mb with | false => rfl | true => simp at hok
  have hDenF : acc.denied = false := by
    cases hd : acc.denied with | false => rfl | true => simp [hmbF, hd] at hok
  simp [hmbF, hDenF] at hok
  have hAccLen : acc.to_consume.items.val.length ≤ inFlightLen st agent := by
    have h : acc.to_consume.items.val.length ≤ vs.items.val.length + invs.items.val.length := hLen
    rw [hvsNil, hinvsLen] at h; simpa using h
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc.to_consume)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmNd⟩ : ∃ vm,
      (if b1 = true then Result.ok st.override_used
       else collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
         types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
         types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used agent
         acc.to_consume) = Result.ok vm ∧
      (vmNodupKeys st.override_used → vmNodupKeys vm) := by
    cases hb1 : b1 with
    | true => exact ⟨st.override_used, by rw [if_pos rfl], id⟩
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; omega
      obtain ⟨vm', hvm'Eq, hvm'Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used agent acc.to_consume
          hcapOvE hcapJ (le_trans hAccLen hcapInvs))
      exact ⟨vm', by rw [if_neg (by decide)]; exact hvm'Eq, hvm'Nd⟩
  rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, _hvm1Mem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent level hcapTaintE hcapTaintS)
  obtain ⟨vm1Nd, hvm1NdEq, hvm1Nd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent level hcapTaintE hcapTaintS)
  have hvv1 : vm1Nd = vm1 := Result.ok.inj (hvm1NdEq.symm.trans hvm1Eq)
  rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm2, hvm2Eq, _hvm2Mem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent level hcapGhE hcapGhS)
  obtain ⟨vm2Nd, hvm2NdEq, hvm2Nd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent level hcapGhE hcapGhS)
  have hvv2 : vm2Nd = vm2 := Result.ok.inj (hvm2NdEq.symm.trans hvm2Eq)
  rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => hvv1 ▸ hvm1Nd h,
    fun h => hvv2 ▸ hvm2Nd h, hvmNd⟩

/-- `sentinel_elevate_taint` preserves the unified `R`. -/
theorem sentinel_elevate_taint_preservesR {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes agent t)
    (hR : R st bg a)
    (hcapInvs : inFlightLen st agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + inFlightLen st agent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_elevate_taint agent (confA level)).guard a ∧
          (Tzimtzum.sentinel_elevate_taint agent (confA level)).next a a' ∧ R st' bg a' := by
  -- project `R → Rsent` (taint/gh `vmsMem` views via the input nodup bridges)
  have hRsent : Rsent st bg a := ⟨hR.active, hR.inflight,
    fun ag L => (hR.taint ag L).trans (vmsMem_iff_vmsMemLast st.taint_levels hR.ndTaint ag (confC L)).symm,
    fun ag L => (hR.ghInvoked ag L).trans
      (vmsMem_iff_vmsMemLast st.gh_taint_invoked hR.ndGhInvoked ag (confC L)).symm,
    hR.override, hR.toolEgress, hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool⟩
  obtain ⟨a', hguard, hnext, hRsent'⟩ :=
    sentinel_elevate_taint_refines cgInst st bg content_gate a agent level cgOf hcg hcgA hRsent
      hcapInvs hcapOvE hcapOvJoint hcapTaintE hcapTaintS hcapGhE hcapGhS st' ev hok
  obtain ⟨hf_act, hf_par, hf_cap, hf_infl, hf_invt, hf_reg, hf_ghrec, hf_instr, hf_bud,
      hNdTaint, hNdGh, hNdOver⟩ :=
    sentinel_elevate_taint_inv_full cgInst st bg content_gate agent level cgOf hcg hcapInvs hcapOvE
      hcapOvJoint hcapTaintE hcapTaintS hcapGhE hcapGhS st' ev hok
  obtain ⟨hRact', hRinfl', hRtaint', hRgh', hRov', hReg', hAllow', hInsp', hOvr', hInvtool'⟩ := hRsent'
  simp only [Tzimtzum.sentinel_elevate_taint] at hnext
  obtain ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allow, ha_insp, ha_ovr, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ha_caprefresh⟩ := hnext
  refine ⟨a', hguard, ?_, ?_⟩
  · simp only [Tzimtzum.sentinel_elevate_taint]
    exact ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allow, ha_insp, ha_ovr, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ha_caprefresh⟩
  · refine ⟨by rw [ha_root]; exact hR.root, by rw [ha_capdecl]; exact hR.cap_declass,
      by rw [ha_caprefresh]; exact hR.cap_refresh, hRact',
      fun t => by rw [ha_reg, hf_reg]; exact hR.tool_reg t,
      fun Cc P => by rw [ha_parent, hf_par]; exact hR.parent Cc P,
      fun N Cc => by rw [ha_cap, hf_cap]; exact hR.cap N Cc,
      fun ag ins => by rw [ha_instr, hf_instr]; exact hR.instr ag ins,
      fun ag L => (hRtaint' ag L).trans
        (vmsMem_iff_vmsMemLast st'.taint_levels (hNdTaint hR.ndTaint) ag (confC L)),
      hRinfl',
      fun ag L => (hRgh' ag L).trans
        (vmsMem_iff_vmsMemLast st'.gh_taint_invoked (hNdGh hR.ndGhInvoked) ag (confC L)),
      fun ag L => by rw [ha_ghrec, hf_ghrec]; exact hR.ghReceived ag L, hRov',
      fun G L hG => by rw [ha_bud, hf_bud]; rw [ha_active] at hG; exact hR.budget G L hG,
      fun t tmeta Cc h => by rw [ha_toolcap]; exact hR.toolCap t tmeta Cc h, hReg',
      fun t tmeta h => by rw [ha_floor]; exact hR.toolFloor t tmeta h,
      fun t tmeta h => by rw [ha_ob]; exact hR.toolBounded t tmeta h,
      fun t tmeta h => by rw [ha_iss]; exact hR.toolIssuer t tmeta h,
      fun i => by rw [ha_trust]; exact hR.trustedIss i,
      fun i issuer h => by rw [ha_instriss]; exact hR.instrIssuer i issuer h, hAllow', hInsp', hOvr',
      hInvtool', by rw [hf_par]; exact hR.ndParent, by rw [hf_cap]; exact hR.ndCap,
      by rw [hf_instr]; exact hR.ndInstr, hNdTaint hR.ndTaint, by rw [hf_infl]; exact hR.ndInflight,
      hNdGh hR.ndGhInvoked, by rw [hf_ghrec]; exact hR.ndGhReceived, hNdOver hR.ndOverride,
      by rw [hf_bud]; exact hR.ndBudget, fun ag I hmem => ?_⟩
    -- wfInflight: in_flight + invocation_tool unchanged
    have hmem' : vmsMemLast st.in_flight ag I := by rw [← hf_infl]; exact hmem
    obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hmem'
    exact ⟨t, tmeta, by unfold invToolC; rw [hf_invt]; exact ht, htm⟩

end ArgusLean.Refinement
