import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `delegate` preserves the unified `R`

`delegate grantor grantee` adds `grantee`: an `agent_active` insert, an `agent_parent` rebuild
(`agent_parent_drop_endpoint` + the fresh `(grantee, grantor)` edge), an empty-cap insert, and a
`clear_agent_state` wipe of `grantee` from seven per-agent maps (so `grantee`'s budget reads back as
full `budget_capacity`). Combines all the prior machinery: the filter conversions (cleared fields), the empty-cap
`vmLastEntry`/`nodup` insert, the `parentPost_vmLast`/`parentPost_nodupKeys` rebuild, and the
absent-after-filter budget. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- Comprehensive inversion: `delegate_ok_inv` plus the `tool_registered` / `invocation_tool` frames and
    the `agent_cap` key-uniqueness post (the empty-cap insert preserves nodup). -/
theorem delegate_inv_full
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (grantor grantee : types.AgentId)
    (hcapA : st.agent_active.items.val.length < Usize.max)
    (hcapC : st.agent_cap.entries.val.length < Usize.max)
    (hcapP : st.agent_parent.entries.val.length < Usize.max)
    (hNodupP : vmNodupKeys st.agent_parent)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.delegate st bg grantor grantee = .ok (.Ok (st', ev))) :
    ∃ (vs1 : collections.VecSet capability.CapKind) (rootVal : types.AgentId),
      vsMem st.agent_active grantor ∧ ¬ vsMem st.agent_active grantee ∧
      types.AgentId.root = .ok rootVal ∧ grantee ≠ rootVal ∧
      vs1.items.val = [] ∧
      st'.tool_registered = st.tool_registered ∧ st'.invocation_tool = st.invocation_tool ∧
      (∀ y, vsMem st'.agent_active y ↔ vsMem st.agent_active y ∨ y = grantee) ∧
      (∀ j, vmLastEntry st'.agent_cap.entries.val j =
        if j = grantee then some (grantee, vs1) else vmLastEntry st.agent_cap.entries.val j) ∧
      (vmNodupKeys st.agent_cap → vmNodupKeys st'.agent_cap) ∧
      st'.taint_levels.entries.val = st.taint_levels.entries.val.filter (removeKept grantee) ∧
      st'.in_flight.entries.val = st.in_flight.entries.val.filter (removeKept grantee) ∧
      st'.gh_taint_invoked.entries.val = st.gh_taint_invoked.entries.val.filter (removeKept grantee) ∧
      st'.gh_taint_received.entries.val = st.gh_taint_received.entries.val.filter (removeKept grantee) ∧
      st'.agent_instruction.entries.val = st.agent_instruction.entries.val.filter (removeKept grantee) ∧
      st'.override_used.entries.val = st.override_used.entries.val.filter (removeKept grantee) ∧
      st'.flow_override.entries.val = st.flow_override.entries.val.filter (removeKept grantee) ∧
      st'.agent_budget.entries.val = st.agent_budget.entries.val.filter (removeKept grantee) ∧
      st'.agent_parent.entries.val =
        st.agent_parent.entries.val.filter (parentKept grantee) ++ [(grantee, grantor)] := by
  simp only [transitions.delegate] at hok
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantor)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee)
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
    spec_imp_exists (vecSetInsert_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantee hcapA)
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
    spec_imp_exists (vecMapInsert_vmLast_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec _ st.agent_cap grantee
      { items := alloc.vec.Vec.new capability.CapKind } hcapC)
  obtain ⟨vm2nd, hvm2ndEq, hvm2ndChar⟩ :=
    spec_imp_exists (vecMapInsert_nodup types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec _ st.agent_cap grantee
      { items := alloc.vec.Vec.new capability.CapKind } hcapC)
  have hvv : vm2nd = vm2 := Result.ok.inj (hvm2ndEq.symm.trans hvm2Eq)
  rw [hvm2Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨st1, hclearEq, hActiveF, hParentF, hCapF, hInvocF, hToolF, hTaint, hInflight,
    hGhInv, hGhRec, hInstr, hOverride, hClrFlow, hBudget⟩ :=
    spec_imp_exists (clearAgentState_spec
      { st with agent_active := vs, agent_parent := vm1, agent_cap := vm2 } grantee)
  rw [hclearEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hst, _hev⟩ := hok
  subst hst
  refine ⟨{ items := alloc.vec.Vec.new capability.CapKind }, rootVal, hbIff.mp hb,
    (by rw [← hb1Iff, hb1]; simp), hrootEq, (fun h => by simp [hb2Iff.mpr h] at hb2), rfl,
    hToolF, hInvocF,
    (fun y => by rw [hActiveF]; exact hvsMem y), (fun j => by rw [hCapF]; exact hvm2Mem j),
    (fun hnd => by rw [hCapF]; exact hvv ▸ hvm2ndChar hnd),
    hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hClrFlow, hBudget,
    (by rw [hParentF]; exact hvm1Char.trans (by rw [hvmChar]))⟩

/-- `delegate` preserves the unified `R`. -/
theorem delegate_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (grantor grantee : types.AgentId)
    (hR : R st bg a)
    (hcapA : st.agent_active.items.val.length < Usize.max)
    (hcapC : st.agent_cap.entries.val.length < Usize.max)
    (hcapP : st.agent_parent.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.delegate st bg grantor grantee = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.delegate grantor grantee).guard a ∧
          (Tzimtzum.delegate grantor grantee).next a a' ∧ R st' bg a' := by
  obtain ⟨vs1, rootVal, hgrantor, hgrantee, hrootEq, hgrne, hvs1empty, hToolF, hInvocF, hActive,
      hCap, hCapNd, hTaint, hInflight, hGhInv, hGhRec, hInstr, hOverride, hClrFlow, hBudget, hParent⟩ :=
    delegate_inv_full st bg grantor grantee hcapA hcapC hcapP hR.ndParent st' ev hok
  have hrootId : a.root_agent = rootVal := by rw [hR.root] at hrootEq; exact Result.ok.inj hrootEq
  have hndP : (st.agent_parent.entries.val.map Prod.fst).Nodup := hR.ndParent
  refine ⟨{ a with
      agent_active := fun A => a.agent_active A ∨ A = grantee
      agent_parent := fun C P =>
        (C = grantee ∧ P = grantor) ∨ (a.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)
      agent_cap := fun N C => a.agent_cap N C ∧ N ≠ grantee
      agent_instruction := fun A I => a.agent_instruction A I ∧ A ≠ grantee
      taint_levels := fun A L => a.taint_levels A L ∧ A ≠ grantee
      agent_budget := fun G L =>
        (G = grantee ∧ L = Tzimtzum.budget_capacity) ∨ (a.agent_budget G L ∧ G ≠ grantee)
      in_flight := fun A I => a.in_flight A I ∧ A ≠ grantee
      gh_taint_invoked := fun A L => a.gh_taint_invoked A L ∧ A ≠ grantee
      gh_taint_received := fun A L => a.gh_taint_received A L ∧ A ≠ grantee
      override_used := fun A T L => a.override_used A T L ∧ A ≠ grantee
      flow_override := fun A T L => a.flow_override A T L ∧ A ≠ grantee }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.delegate]
    exact ⟨(hR.active grantor).mpr hgrantor, fun h => hgrantee ((hR.active grantee).mp h),
      by rw [hrootId]; exact hgrne⟩
  · -- next
    simp [Tzimtzum.delegate]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer,
      hR.trustedIss, hR.instrIssuer, hR.flowAllows, hR.flowInspects, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro ag inv
      show (a.in_flight ag inv ∧ ag ≠ grantee) ↔ vmsMemLast st'.in_flight ag inv
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hInflight hR.ndInflight),
        vmsMem_filter_removeKept _ _ _ hInflight, vmsMem_iff_vmsMemLast _ hR.ndInflight, ← hR.inflight]
    · intro ag L
      show (a.gh_taint_invoked ag L ∧ ag ≠ grantee) ↔ vmsMemLast st'.gh_taint_invoked ag (confC L)
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hGhInv hR.ndGhInvoked),
        vmsMem_filter_removeKept _ _ _ hGhInv, vmsMem_iff_vmsMemLast _ hR.ndGhInvoked, ← hR.ghInvoked]
    · intro ag L
      show (a.gh_taint_received ag L ∧ ag ≠ grantee) ↔ vmsMemLast st'.gh_taint_received ag (confC L)
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hGhRec hR.ndGhReceived),
        vmsMem_filter_removeKept _ _ _ hGhRec, vmsMem_iff_vmsMemLast _ hR.ndGhReceived, ← hR.ghReceived]
    · intro ag t L
      show (a.override_used ag t L ∧ ag ≠ grantee) ↔
        vmsMemLast st'.override_used ag { tool := t, level := confC L }
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hOverride hR.ndOverride),
        vmsMem_filter_removeKept _ _ _ hOverride, vmsMem_iff_vmsMemLast _ hR.ndOverride, ← hR.override]
    · -- budget (grantee → full capacity via absent-after-filter; others filtered)
      intro G L hactiveG
      show ((G = grantee ∧ L = Tzimtzum.budget_capacity) ∨ (a.agent_budget G L ∧ G ≠ grantee)) ↔
        (budgetReadC st'.agent_budget G).val = L
      have hbr : budgetReadC st'.agent_budget G =
          if G = grantee then types.BUDGET_CAPACITY else budgetReadC st.agent_budget G := by
        unfold budgetReadC; rw [hBudget, vmLastEntry_filter_removeKept]
        by_cases hG : G = grantee <;> simp [hG]
      rw [hbr]
      by_cases hG : G = grantee
      · rw [if_pos hG]
        constructor
        · rintro (⟨_, hcap⟩ | ⟨_, hne⟩)
          · subst hcap; exact budgetCapacity_val
          · exact absurd hG hne
        · intro h; exact Or.inl ⟨hG, (budgetCapacity_val ▸ h).symm⟩
      · rw [if_neg hG]
        have hGact : a.agent_active G := hactiveG.resolve_right hG
        have hL : ((G = grantee ∧ L = Tzimtzum.budget_capacity) ∨ (a.agent_budget G L ∧ G ≠ grantee)) ↔
            a.agent_budget G L :=
          ⟨fun h => h.elim (fun hp => absurd hp.1 hG) (fun hp => hp.1), fun h => Or.inr ⟨h, hG⟩⟩
        rw [hL]; exact hR.budget G L hGact
    · -- flowOverride
      intro ag t L
      show (a.flow_override ag t L ∧ ag ≠ grantee) ↔
        vmsMemLast st'.flow_override ag { tool := t, level := confC L }
      rw [← vmsMem_iff_vmsMemLast _ (vmNodupKeysFilter hClrFlow hR.ndFlowOverride),
        vmsMem_filter_removeKept _ _ _ hClrFlow, vmsMem_iff_vmsMemLast _ hR.ndFlowOverride, ← hR.flowOverride]
    · intro I t; show invToolC st' I = some t → a.invocation_tool I = t
      unfold invToolC; rw [hInvocF]; exact hR.invTool I t
    · -- ndParent (rebuild keeps keys unique)
      show vmNodupKeys st'.agent_parent
      unfold vmNodupKeys; rw [hParent]; exact parentPost_nodupKeys _ grantee grantor hndP
    · exact hCapNd hR.ndCap
    · exact vmNodupKeysFilter hInstr hR.ndInstr
    · exact vmNodupKeysFilter hTaint hR.ndTaint
    · exact vmNodupKeysFilter hInflight hR.ndInflight
    · exact vmNodupKeysFilter hGhInv hR.ndGhInvoked
    · exact vmNodupKeysFilter hGhRec hR.ndGhReceived
    · exact vmNodupKeysFilter hOverride hR.ndOverride
    · exact vmNodupKeysFilter hClrFlow hR.ndFlowOverride
    · exact vmNodupKeysFilter hBudget hR.ndBudget
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
