import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `delegate` preserves the unified `R`

`delegate grantor grantee` adds `grantee`: an `agent_active` insert, an `agent_parent` rebuild
(`agent_parent_drop_endpoint` + the fresh `(grantee, grantor)` edge), an empty-cap insert, a
`clear_agent_state` wipe of `grantee` from the six per-agent maps (`taint_levels`, `integ_levels`,
`in_flight`, `agent_instruction`, `override_used`, `flow_override` — the ghost maps are gone in V3),
and finally a direct `agent_budget` insert of `0#u8` for `grantee` (Campaign B: the grantee spawns at
budget 0, a plain function write, not part of `clear_agent_state`'s filter). Combines the filter
conversions (cleared fields), the empty-cap `vmLastEntry`/`nodup` insert, the
`parentPost_vmLast`/`parentPost_nodupKeys` rebuild, and the budget-insert `vmLastEntry`/`nodup`
pair (same shape as `debitBudget_full`/`creditBudget_full`, but a plain insert of the literal `0`
instead of a saturating op). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- Comprehensive inversion: the active/parent/cap rebuild, the `clear_agent_state` six-field wipe
    (with `tool_registered`/`invocation_tool`/`invocation_used`/`invocation_egress` framed), and the
    grantee's budget cell forced to `0` (get-style, all other agents' budgets framed). -/
theorem delegate_inv_full
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (grantor grantee : types.AgentId)
    (hcapA : st.agent_active.items.val.length < Usize.max)
    (hcapC : st.agent_cap.entries.val.length < Usize.max)
    (hcapP : st.agent_parent.entries.val.length < Usize.max)
    (hcapB : st.agent_budget.entries.val.length < Usize.max)
    (hNodupP : vmNodupKeys st.agent_parent)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.delegate st bg grantor grantee = .ok (.Ok (st', ev))) :
    ∃ (vs1 : collections.VecSet capability.CapKind) (rootVal : types.AgentId),
      vsMem st.agent_active grantor ∧ ¬ vsMem st.agent_active grantee ∧
      types.AgentId.root = .ok rootVal ∧ grantee ≠ rootVal ∧
      vs1.items.val = [] ∧
      st'.tool_registered = st.tool_registered ∧ st'.invocation_tool = st.invocation_tool ∧
      st'.invocation_used = st.invocation_used ∧ st'.invocation_egress = st.invocation_egress ∧
      (∀ y, vsMem st'.agent_active y ↔ vsMem st.agent_active y ∨ y = grantee) ∧
      (∀ j, vmLastEntry st'.agent_cap.entries.val j =
        if j = grantee then some (grantee, vs1) else vmLastEntry st.agent_cap.entries.val j) ∧
      (vmNodupKeys st.agent_cap → vmNodupKeys st'.agent_cap) ∧
      st'.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept grantee) ∧
      st'.integ_levels.entries.val = st.integ_levels.entries.val.filter (removeKept grantee) ∧
      st'.in_flight.entries.val = st.in_flight.entries.val.filter (removeKept grantee) ∧
      st'.agent_instruction.entries.val = st.agent_instruction.entries.val.filter (removeKept grantee) ∧
      st'.override_used.entries.val = st.override_used.entries.val.filter (removeKept grantee) ∧
      st'.flow_override.entries.val = st.flow_override.entries.val.filter (removeKept grantee) ∧
      st'.agent_parent.entries.val =
        st.agent_parent.entries.val.filter (parentKept grantee) ++ [(grantee, grantor)] ∧
      (∀ G, budgetReadC st'.agent_budget G =
        if G = grantee then (0#u8) else budgetReadC st.agent_budget G) ∧
      (vmNodupKeys st.agent_budget → vmNodupKeys st'.agent_budget) := by
  simp only [transitions.delegate] at hok
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantor)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = false := by cases b1 with | false => rfl | true => simp at hok
  simp only [hb1, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨rootVal, hrootEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hrootEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :
      ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq grantee rootVal = .ok bb ∧
        (bb = true ↔ grantee = rootVal) :=
    ⟨_, agentId_eq_spec grantee rootVal, by simp⟩
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = false := by cases b2 with | false => rfl | true => simp at hok
  simp only [hb2, reduceIte, Bool.false_eq_true] at hok
  simp only [agentId_clone_spec, bind_tc_ok] at hok
  obtain ⟨vs, hvsEq, hvsMem⟩ :=
    spec_imp_exists (vecSetInsert_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee hcapA)
  rw [hvsEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmChar⟩ := spec_imp_exists
    (agentParentDropEndpoint_spec st.agent_parent grantee hNodupP)
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  have hvmAbsent : ∀ p ∈ vm.entries.val, p.1 ≠ grantee := by
    rw [hvmChar]; intro p hp
    have hp' := List.mem_filter.mp hp
    simp only [parentKept, decide_eq_true_eq] at hp'
    exact hp'.2.1
  have hvmCap : vm.entries.val.length < Usize.max := by
    rw [hvmChar]; exact lt_of_le_of_lt (List.length_filter_le _ _) hcapP
  obtain ⟨vm1, hvm1Eq, hvm1Char⟩ := spec_imp_exists
    (vecMapInsert_append_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone vm grantee grantor hvmCap hvmAbsent)
  rw [hvm1Eq] at hok
  simp only [collections.VecSet.new, bind_tc_ok] at hok
  obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ :=
    spec_imp_exists (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec _ st.agent_cap grantee
      { items := alloc.vec.Vec.new capability.CapKind } hcapC)
  obtain ⟨vm2nd, hvm2ndEq, hvm2ndChar⟩ :=
    spec_imp_exists (vecMapInsert_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec _ st.agent_cap grantee
      { items := alloc.vec.Vec.new capability.CapKind } hcapC)
  have hvv : vm2nd = vm2 := Result.ok.inj (hvm2ndEq.symm.trans hvm2Eq)
  rw [hvm2Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨st1, hclearEq, hActiveF, hParentF, hCapF, hInvocF, hUsedF, hEgressF, hToolF, hBudgetF,
    hTaint, hInteg, hInflight, hInstr, hOverride, hClrFlow⟩ :=
    spec_imp_exists (clearAgentState_spec
      { st with agent_active := vs, agent_parent := vm1, agent_cap := vm2 } grantee)
  rw [hclearEq] at hok
  simp only [bind_tc_ok] at hok
  have hcapB1 : st1.agent_budget.entries.val.length < Usize.max := by rw [hBudgetF]; exact hcapB
  obtain ⟨vm3, hvm3Eq, hvm3Last⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec core.clone.CloneU8
      st1.agent_budget grantee (0#u8) hcapB1)
  obtain ⟨vm3nd, hvm3ndEq, hvm3ndChar⟩ := spec_imp_exists
    (vecMapInsert_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec core.clone.CloneU8
      st1.agent_budget grantee (0#u8) hcapB1)
  have hvv3 : vm3nd = vm3 := Result.ok.inj (hvm3ndEq.symm.trans hvm3Eq)
  rw [hvm3Eq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _hev⟩ := hok
  subst hst
  refine ⟨{ items := alloc.vec.Vec.new capability.CapKind }, rootVal, hbIff.mp hb,
    (by rw [← hb1Iff, hb1]; simp), hrootEq, (fun h => by simp [hb2Iff.mpr h] at hb2), rfl,
    hToolF, hInvocF, hUsedF, hEgressF,
    (fun y => by rw [hActiveF]; exact hvsMem y), (fun j => by rw [hCapF]; exact hvm2Mem j),
    (fun hnd => by rw [hCapF]; exact hvv ▸ hvm2ndChar hnd),
    hTaint, hInteg, hInflight, hInstr, hOverride, hClrFlow,
    (by rw [hParentF]; exact hvm1Char.trans (by rw [hvmChar])),
    (fun G => by
      show budgetReadC vm3 G = if G = grantee then (0#u8) else budgetReadC st.agent_budget G
      by_cases hG : G = grantee
      · have hr : budgetReadC vm3 G = (0#u8) := by unfold budgetReadC; rw [hvm3Last G, if_pos hG]
        rw [hr, if_pos hG]
      · have hr : budgetReadC vm3 G = budgetReadC st1.agent_budget G := by
          unfold budgetReadC; rw [hvm3Last G, if_neg hG]
        rw [hr, hBudgetF, if_neg hG]),
    (fun hnd => by
      show vmNodupKeys vm3
      have hnd1 : vmNodupKeys st1.agent_budget := by rw [hBudgetF]; exact hnd
      exact hvv3 ▸ hvm3ndChar hnd1)⟩

/-- `delegate` preserves the unified `R`. -/
theorem delegate_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (grantor grantee : types.AgentId)
    (hR : R st bg a)
    (hcapA : st.agent_active.items.val.length < Usize.max)
    (hcapC : st.agent_cap.entries.val.length < Usize.max)
    (hcapP : st.agent_parent.entries.val.length < Usize.max)
    (hcapB : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.delegate st bg grantor grantee = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.delegate grantor grantee).guard a ∧
          (Tzimtzum.delegate grantor grantee).next a a' ∧ R st' bg a' := by
  obtain ⟨vs1, rootVal, hgrantor, hgrantee, hrootEq, hgrne, hvs1empty, hToolF, hInvocF, hUsedF,
      hEgressF, hActive, hCap, hCapNd, hTaint, hInteg, hInflight, hInstr, hOverride, hClrFlow,
      hParent, hBudget, hBudgetNd⟩ :=
    delegate_inv_full st bg grantor grantee hcapA hcapC hcapP hcapB hR.ndParent st' ev hok
  have hrootId : a.root_agent = rootVal := by rw [hR.root] at hrootEq; exact Result.ok.inj hrootEq
  have hndP : (st.agent_parent.entries.val.map Prod.fst).Nodup := hR.ndParent
  refine ⟨{ a with
      agent_active := fun A => a.agent_active A ∨ A = grantee
      agent_parent := fun C P =>
        (C = grantee ∧ P = grantor) ∨ (a.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)
      agent_cap := fun N C => a.agent_cap N C ∧ N ≠ grantee
      agent_instruction := fun A I => a.agent_instruction A I ∧ A ≠ grantee
      taint_levels := fun A L => a.taint_levels A L ∧ A ≠ grantee
      integ_levels := fun A L => a.integ_levels A L ∧ A ≠ grantee
      agent_budget := fun G => if G = grantee then 0 else a.agent_budget G
      in_flight := fun A I => a.in_flight A I ∧ A ≠ grantee
      override_used := fun A T L => a.override_used A T L ∧ A ≠ grantee
      flow_override := fun A T L => a.flow_override A T L ∧ A ≠ grantee }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.delegate]
    exact ⟨(hR.active grantor).mpr hgrantor, fun h => hgrantee ((hR.active grantee).mp h),
      by rw [hrootId]; exact hgrne⟩
  · -- next: every conjunct is `rfl` except the classical-`ite` budget field (the spec's `ite`
    -- is elaborated against `Classical.propDecidable` at `AgentId`'s abstract type; our own
    -- literal re-elaborates against the concrete instance, so the two `ite` terms need a
    -- decidable-irrelevant case split instead of syntactic `rfl`).
    simp [Tzimtzum.delegate]
    funext G; by_cases hG : G = grantee <;> simp [hG]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor,
      hR.toolIntegInspectFloor, hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss,
      hR.instrIssuer, hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; show (a.agent_active x ∨ x = grantee) ↔ vsMem st'.agent_active x
      rw [hActive x, hR.active x]
    · intro t; show a.tool_registered t ↔ vsMem st'.tool_registered t
      rw [hToolF]; exact hR.tool_reg t
    · -- parent
      intro C P
      show ((C = grantee ∧ P = grantor) ∨ (a.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)) ↔
        vmLastEntry st'.agent_parent.entries.val C = some (C, P)
      rw [hParent, parentPost_vmLast _ grantee grantor C P hndP, ← hR.parent C P]
    · -- cap
      intro N C
      show (a.agent_cap N C ∧ N ≠ grantee) ↔ vmsMemLast st'.agent_cap N C
      rw [← capMem_iff_vmsMemLast]
      by_cases hN : N = grantee
      · have hc : capMem st'.agent_cap N C ↔ False := by
          simp only [capMem, hCap N, if_pos hN]; simp [hvs1empty]
        rw [hc]; simp [hN]
      · have hc : capMem st'.agent_cap N C ↔ capMem st.agent_cap N C := by
          simp only [capMem, hCap N, if_neg hN]
        rw [hc, capMem_iff_vmsMemLast, ← hR.cap N]; simp [hN]
    · intro ag ins
      show (a.agent_instruction ag ins ∧ ag ≠ grantee) ↔ vmsMemLast st'.agent_instruction ag ins
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hInstr hR.ndInstr),
        vmsMem_filter_removeKept _ _ _ hInstr, vmsMem_iff_vmsMemLast _ hR.ndInstr, ← hR.instr]
    · intro ag L
      show (a.taint_levels ag L ∧ ag ≠ grantee) ↔ vmsMemLast st'.taint_levels ag (confC L)
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hTaint hR.ndTaint),
        vmsMem_filter_removeKept _ _ _ hTaint, vmsMem_iff_vmsMemLast _ hR.ndTaint, ← hR.taint]
    · intro ag L
      show (a.integ_levels ag L ∧ ag ≠ grantee) ↔ vmsMemLast st'.integ_levels ag (integC L)
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hInteg hR.ndInteg),
        vmsMem_filter_removeKept _ _ _ hInteg, vmsMem_iff_vmsMemLast _ hR.ndInteg, ← hR.integ]
    · intro ag inv
      show (a.in_flight ag inv ∧ ag ≠ grantee) ↔ vmsMemLast st'.in_flight ag inv
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hInflight hR.ndInflight),
        vmsMem_filter_removeKept _ _ _ hInflight, vmsMem_iff_vmsMemLast _ hR.ndInflight, ← hR.inflight]
    · intro ag t L
      show (a.override_used ag t L ∧ ag ≠ grantee) ↔
        vmsMemLast st'.override_used ag { tool := t, level := confC L }
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hOverride hR.ndOverride),
        vmsMem_filter_removeKept _ _ _ hOverride, vmsMem_iff_vmsMemLast _ hR.ndOverride, ← hR.override]
    · -- budget: function equation, grantee ↦ 0 (spawn), everyone else framed — no active guard
      intro G
      show (if G = grantee then 0 else a.agent_budget G) = (budgetReadC st'.agent_budget G).val
      rw [hBudget G]
      by_cases hG : G = grantee
      · simp [hG]
      · simp [hG, ← hR.budget G]
    · -- invUsed (global history, untouched)
      show RinvocationUsed st' _; rw [RinvocationUsed, hUsedF]; exact hR.invUsed
    · -- invEgress (global history, untouched)
      show RinvocationEgress st' _; rw [RinvocationEgress, hEgressF]; exact hR.invEgress
    · -- flowOverride
      intro ag t L
      show (a.flow_override ag t L ∧ ag ≠ grantee) ↔
        vmsMemLast st'.flow_override ag { tool := t, level := confC L }
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hClrFlow hR.ndFlowOverride),
        vmsMem_filter_removeKept _ _ _ hClrFlow, vmsMem_iff_vmsMemLast _ hR.ndFlowOverride, ← hR.flowOverride]
    · -- invTool (frame)
      intro I t; show invToolC st' I = some t → a.invocation_tool I = t
      unfold invToolC; rw [hInvocF]; exact hR.invTool I t
    · -- ndParent (rebuild keeps keys unique)
      show vmNodupKeys st'.agent_parent
      unfold vmNodupKeys; rw [hParent]; exact parentPost_nodupKeys _ grantee grantor hndP
    · exact hCapNd hR.ndCap
    · exact vmNodupKeysFilter hInstr hR.ndInstr
    · exact vmNodupKeysFilter hTaint hR.ndTaint
    · exact vmNodupKeysFilter hInteg hR.ndInteg
    · exact vmNodupKeysFilter hInflight hR.ndInflight
    · exact vmNodupKeysFilter hOverride hR.ndOverride
    · exact vmNodupKeysFilter hClrFlow hR.ndFlowOverride
    · exact hBudgetNd hR.ndBudget
    · intro ag I hmem
      have hmem' : vmsMemLast st.in_flight ag I := by
        obtain ⟨vs, hve, hv⟩ := hmem
        rw [hInflight, vmLastEntry_filter_removeKept] at hve
        by_cases hag : ag = grantee
        · rw [if_pos hag] at hve; exact absurd hve (by simp)
        · rw [if_neg hag] at hve; exact ⟨vs, hve, hv⟩
      obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hmem'
      exact ⟨t, tmeta, by unfold invToolC; rw [hInvocF]; exact ht, htm⟩

end ArgusLean.Refinement
