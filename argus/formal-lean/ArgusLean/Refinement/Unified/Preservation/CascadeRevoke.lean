import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `cascade_revoke` preserves the unified `R`

The twin of `revoke`: drops `child` from `agent_active`, `agent_parent`, `agent_cap`, and the six
`clear_agent_state` fields (all key-filters), differing only in the gate polarity (`prnt`
**inactive**) and the dropped agent. `agent_budget`/`invocation_used`/`invocation_egress` are left
framed, same rationale as `Revoke.lean`. Same machinery throughout. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- Comprehensive inversion: `cascade_revoke`'s structural frame plus the six-field
    `clear_agent_state` filter, with `tool_registered`/`invocation_tool`/`invocation_used`/
    `invocation_egress`/`agent_budget` all framed. -/
theorem cascade_revoke_inv_full
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (child prnt : types.AgentId)
    (hNodupP : vmNodupKeys st.agent_parent)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.cascade_revoke st bg child prnt = .ok (.Ok (st', ev))) :
    ∃ (rootVal : types.AgentId),
      vmLastEntry st.agent_parent.entries.val child = some (child, prnt) ∧
      ¬ vsMem st.agent_active prnt ∧ vsMem st.agent_active child ∧
      types.AgentId.root = .ok rootVal ∧ child ≠ rootVal ∧
      (∀ y, vsMem st'.agent_active y ↔ vsMem st.agent_active y ∧ y ≠ child) ∧
      st'.tool_registered = st.tool_registered ∧ st'.invocation_tool = st.invocation_tool ∧
      st'.invocation_used = st.invocation_used ∧ st'.invocation_egress = st.invocation_egress ∧
      st'.agent_budget = st.agent_budget ∧
      st'.agent_cap.entries.val = st.agent_cap.entries.val.filter (removeKept child) ∧
      st'.agent_parent.entries.val = st.agent_parent.entries.val.filter (removeKept child) ∧
      st'.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept child) ∧
      st'.integ_levels.entries.val = st.integ_levels.entries.val.filter (removeKept child) ∧
      st'.in_flight.entries.val = st.in_flight.entries.val.filter (removeKept child) ∧
      st'.agent_instruction.entries.val = st.agent_instruction.entries.val.filter (removeKept child) ∧
      st'.override_used.entries.val = st.override_used.entries.val.filter (removeKept child) ∧
      st'.flow_override.entries.val = st.flow_override.entries.val.filter (removeKept child) := by
  simp only [transitions.cascade_revoke] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b, hbEq, hbIff⟩ :
      ∃ bb, core.cmp.PartialEq.ne.trait_default (core.option.Option.Insts.CoreCmpPartialEqOption
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId)) o (some prnt) =
        .ok bb ∧ (bb = true ↔ o ≠ some prnt) :=
    ⟨_, optionAgentId_ne_spec o (some prnt), by simp⟩
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = false := by cases b with | false => rfl | true => simp at hok
  simp only [hb, reduceIte, Bool.false_eq_true] at hok
  have hoP : o = some prnt := by
    by_contra hc; have := hbIff.mpr hc; rw [hb] at this; simp at this
  have hlast : vmLastEntry st.agent_parent.entries.val child = some (child, prnt) := by
    have hoP' : (vmLastEntry st.agent_parent.entries.val child).map Prod.snd = some prnt := by
      rw [← ho]; exact hoP
    cases hL : vmLastEntry st.agent_parent.entries.val child with
    | none => rw [hL] at hoP'; simp at hoP'
    | some p =>
      have hp1 : p.1 = child := vmLastEntry_fst _ _ _ hL
      rw [hL, Option.map_some] at hoP'
      obtain ⟨x, y⟩ := p
      simp only [Option.some_inj] at hoP'
      simp_all
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active prnt)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = false := by cases b1 with | false => rfl | true => simp at hok
  simp only [hb1, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  obtain ⟨rootVal, hrootEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hrootEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b3, hb3Eq, hb3Iff⟩ :
      ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq child rootVal = .ok bb ∧
        (bb = true ↔ child = rootVal) :=
    ⟨_, agentId_eq_spec child rootVal, by simp⟩
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨vs, hvsEq, hvsMem⟩ :=
    spec_imp_exists (vecSetRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec agentId_clone_spec
      st.agent_active child)
  rw [hvsEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmChar⟩ :=
    spec_imp_exists (agentParentDropChild_spec st.agent_parent child hNodupP)
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, hvm1Char⟩ :=
    spec_imp_exists (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      (collections.VecSet.Insts.CoreCloneClone capability.CapKind.Insts.CoreCloneClone)
      st.agent_cap child)
  rw [hvm1Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨st1, hclearEq, hActiveF, hParentF, hCapF, hInvocF, hUsedF, hEgressF, hToolF, hBudgetF,
    hTaint, hInteg, hInflight, hInstr, hOverride, hClrFlow⟩ :=
    spec_imp_exists (clearAgentState_spec
      { st with agent_active := vs, agent_parent := vm, agent_cap := vm1 } child)
  rw [hclearEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _hev⟩ := hok
  subst hst
  exact ⟨rootVal, hlast, by rw [← hb1Iff]; simp [hb1], hb2Iff.mp hb2, hrootEq,
    (fun h => by simp [hb3Iff.mpr h] at hb3),
    (fun y => by rw [hActiveF]; exact hvsMem y), hToolF, hInvocF, hUsedF, hEgressF, hBudgetF,
    (by rw [hCapF]; exact hvm1Char), (by rw [hParentF]; exact hvmChar),
    hTaint, hInteg, hInflight, hInstr, hOverride, hClrFlow⟩

/-- `cascade_revoke` preserves the unified `R`. -/
theorem cascade_revoke_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (child prnt : types.AgentId)
    (hR : R st bg a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.cascade_revoke st bg child prnt = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.cascade_revoke child prnt).guard a ∧
          (Tzimtzum.cascade_revoke child prnt).next a a' ∧ R st' bg a' := by
  obtain ⟨rootVal, hParentEdge, hPrntInactive, hChildActive, hrootEq, hchildNe, hActive, hToolF,
      hInvocF, hUsedF, hEgressF, hBudgetF, hCap, hParent, hTaint, hInteg, hInflight, hInstr,
      hOverride, hClrFlow⟩ :=
    cascade_revoke_inv_full st bg child prnt hR.ndParent st' ev hok
  have hrootId : a.root_agent = rootVal := by rw [hR.root] at hrootEq; exact Result.ok.inj hrootEq
  refine ⟨{ a with
      agent_active := fun A => a.agent_active A ∧ A ≠ child
      agent_parent := fun C P => a.agent_parent C P ∧ C ≠ child
      agent_cap := fun N C => a.agent_cap N C ∧ N ≠ child
      agent_instruction := fun A I => a.agent_instruction A I ∧ A ≠ child
      taint_levels := fun A L => a.taint_levels A L ∧ A ≠ child
      integ_levels := fun A L => a.integ_levels A L ∧ A ≠ child
      in_flight := fun A I => a.in_flight A I ∧ A ≠ child
      override_used := fun A T L => a.override_used A T L ∧ A ≠ child
      flow_override := fun A T L => a.flow_override A T L ∧ A ≠ child }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.cascade_revoke]
    exact ⟨(hR.parent child prnt).mpr hParentEdge,
      fun h => hPrntInactive ((hR.active prnt).mp h),
      (hR.active child).mpr hChildActive, by rw [hrootId]; exact hchildNe⟩
  · -- next
    simp [Tzimtzum.cascade_revoke]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor,
      hR.toolIntegInspectFloor, hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss,
      hR.instrIssuer, hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; show (a.agent_active x ∧ x ≠ child) ↔ vsMem st'.agent_active x
      rw [hActive x, hR.active x]
    · intro t; show a.tool_registered t ↔ vsMem st'.tool_registered t
      rw [hToolF]; exact hR.tool_reg t
    · intro C P
      show (a.agent_parent C P ∧ C ≠ child) ↔ vmLastEntry st'.agent_parent.entries.val C = some (C, P)
      rw [hParent, vmLastEntry_filter_removeKept]
      by_cases hC : C = child
      · simp [hC]
      · rw [if_neg hC, ← hR.parent C P]; simp [hC]
    · intro N C
      show (a.agent_cap N C ∧ N ≠ child) ↔ vmsMemLast st'.agent_cap N C
      rw [← capMem_iff_vmsMemLast, capMem_filter_removeKept st'.agent_cap st.agent_cap child hCap N C,
        capMem_iff_vmsMemLast, ← hR.cap N C]
    · intro ag ins
      show (a.agent_instruction ag ins ∧ ag ≠ child) ↔ vmsMemLast st'.agent_instruction ag ins
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hInstr hR.ndInstr),
        vmsMem_filter_removeKept _ _ _ hInstr, vmsMem_iff_vmsMemLast _ hR.ndInstr, ← hR.instr]
    · intro ag L
      show (a.taint_levels ag L ∧ ag ≠ child) ↔ vmsMemLast st'.taint_levels ag (confC L)
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hTaint hR.ndTaint),
        vmsMem_filter_removeKept _ _ _ hTaint, vmsMem_iff_vmsMemLast _ hR.ndTaint, ← hR.taint]
    · -- integ
      intro ag L
      show (a.integ_levels ag L ∧ ag ≠ child) ↔ vmsMemLast st'.integ_levels ag (integC L)
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hInteg hR.ndInteg),
        vmsMem_filter_removeKept _ _ _ hInteg, vmsMem_iff_vmsMemLast _ hR.ndInteg, ← hR.integ]
    · intro ag inv
      show (a.in_flight ag inv ∧ ag ≠ child) ↔ vmsMemLast st'.in_flight ag inv
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hInflight hR.ndInflight),
        vmsMem_filter_removeKept _ _ _ hInflight, vmsMem_iff_vmsMemLast _ hR.ndInflight, ← hR.inflight]
    · intro ag t L
      show (a.override_used ag t L ∧ ag ≠ child) ↔
        vmsMemLast st'.override_used ag { tool := t, level := confC L }
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hOverride hR.ndOverride),
        vmsMem_filter_removeKept _ _ _ hOverride, vmsMem_iff_vmsMemLast _ hR.ndOverride, ← hR.override]
    · -- budget: fully framed (cascade_revoke never writes it, no active-guard needed)
      intro G; show a.agent_budget G = (budgetReadC st'.agent_budget G).val
      rw [hBudgetF]; exact hR.budget G
    · -- invUsed (global history, untouched)
      show RinvocationUsed st' a; rw [RinvocationUsed, hUsedF]; exact hR.invUsed
    · -- invEgress (global history, untouched)
      show RinvocationEgress st' a; rw [RinvocationEgress, hEgressF]; exact hR.invEgress
    · -- flowOverride
      intro ag t L
      show (a.flow_override ag t L ∧ ag ≠ child) ↔
        vmsMemLast st'.flow_override ag { tool := t, level := confC L }
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hClrFlow hR.ndFlowOverride),
        vmsMem_filter_removeKept _ _ _ hClrFlow, vmsMem_iff_vmsMemLast _ hR.ndFlowOverride, ← hR.flowOverride]
    · intro I t; show invToolC st' I = some t → a.invocation_tool I = t
      unfold invToolC; rw [hInvocF]; exact hR.invTool I t
    · show vmNodupKeys st'.agent_parent
      unfold vmNodupKeys; rw [hParent]; exact vmNodupKeys_filter _ child hR.ndParent
    · exact vmNodupKeysFilter hCap hR.ndCap
    · exact vmNodupKeysFilter hInstr hR.ndInstr
    · exact vmNodupKeysFilter hTaint hR.ndTaint
    · exact vmNodupKeysFilter hInteg hR.ndInteg
    · exact vmNodupKeysFilter hInflight hR.ndInflight
    · exact vmNodupKeysFilter hOverride hR.ndOverride
    · exact vmNodupKeysFilter hClrFlow hR.ndFlowOverride
    · -- ndBudget: framed
      show vmNodupKeys st'.agent_budget; rw [hBudgetF]; exact hR.ndBudget
    · intro ag I hmem
      have hmem' : vmsMemLast st.in_flight ag I := by
        obtain ⟨vs, hve, hv⟩ := hmem
        rw [hInflight, vmLastEntry_filter_removeKept] at hve
        by_cases hag : ag = child
        · rw [if_pos hag] at hve; exact absurd hve (by simp)
        · rw [if_neg hag] at hve; exact ⟨vs, hve, hv⟩
      obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hmem'
      exact ⟨t, tmeta, by unfold invToolC; rw [hInvocF]; exact ht, htm⟩

end ArgusLean.Refinement
