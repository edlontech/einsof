import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `unregister_tool` preserves the unified `R`

New V3 action (design §5.6, task 13): a registered tool leaves the authorization surface,
guarded by "no in-flight invocation of the tool anywhere" (preserves `in_flight_registered`
spec-side). The kernel scans EVERY `in_flight` entry (including last-match-shadowed duplicates —
a superset of the live pairs, so the scan's verdict covers the spec's last-match quantifier), and
the write is a point-remove on `tool_registered`. Re-registration later is permitted. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 4000000

/-! ## Inner scan (one agent's flights) -/

/-- `unregister_tool_loop0_loop0` scans one flights set for an invocation bound to `tool`. -/
theorem unregisterInner_spec
    (vm1 : collections.VecMap types.InvocationId types.ToolId) (tool : types.ToolId)
    (flights : collections.VecSet types.InvocationId)
    (tif0 tif : Bool) (j : Usize)
    (hj : j.val ≤ flights.items.val.length)
    (htif : tif = true ↔ tif0 = true ∨
      ∃ I ∈ flights.items.val.take j.val,
        (vmLastEntry vm1.entries.val I).map Prod.snd = some tool) :
    transitions.unregister_tool_loop0_loop0 vm1 tool tif flights j ⦃ res =>
      res = true ↔ tif0 = true ∨
        ∃ I ∈ flights.items.val,
          (vmLastEntry vm1.entries.val I).map Prod.snd = some tool ⦄ := by
  unfold transitions.unregister_tool_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ flights.items.val.length ∧
      (p.1 = true ↔ tif0 = true ∨
        ∃ I ∈ flights.items.val.take p.2.val,
          (vmLastEntry vm1.entries.val I).map Prod.snd = some tool))
  · rintro ⟨tifL, jL⟩ ⟨hile, htifL⟩
    dsimp only at hile htifL ⊢
    simp only [transitions.unregister_tool_loop0_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : jL.val < flights.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec vm1 flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = jL.val + 1 →
          flights.items.val.take i2.val = flights.items.val.take (jL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ flights.items.val.take (jL.val + 1), P x) ↔
          (∃ x ∈ flights.items.val.take jL.val, P x) ∨ P flight_inv := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hflight_inv]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨flight_inv, Or.inr hflight_inv, hPi⟩
      cases hocase : o with
      | none =>
        have hnone : (vmLastEntry vm1.entries.val flight_inv).map Prod.snd = none := by
          rw [← ho]; exact hocase
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ j1_post, hext, htifL]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · rw [hnone] at hC; simp at hC
      | some flight_tool =>
        have hsome : (vmLastEntry vm1.entries.val flight_inv).map Prod.snd = some flight_tool := by
          rw [← ho]; exact hocase
        simp only [toolId_eq_spec, bind_tc_ok]
        cases heq : decide (flight_tool = tool) with
        | true =>
          have ht : flight_tool = tool := of_decide_eq_true heq
          simp only [heq, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi2 _ j1_post, hext]
          exact ⟨fun _ => Or.inr (Or.inr (by rw [hsome, ht])), fun _ => trivial⟩
        | false =>
          have ht : flight_tool ≠ tool := of_decide_eq_false heq
          simp only [heq, Bool.false_eq_true, reduceIte]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi2 _ j1_post, hext, htifL]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · rw [hsome, Option.some_inj] at hC; exact absurd hC ht
    case isFalse h =>
      have heq' : jL.val = flights.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at htifL ⊢
      exact htifL
  · exact ⟨hj, htif⟩

/-! ## Outer scan (every `in_flight` entry, positionally — a superset of the live pairs) -/

/-- `unregister_tool_loop0` scans every `in_flight` entry's set for an invocation bound to
    `tool`. -/
theorem unregisterOuter_spec
    (vm : collections.VecMap types.AgentId (collections.VecSet types.InvocationId))
    (vm1 : collections.VecMap types.InvocationId types.ToolId) (tool : types.ToolId)
    (tif0 tif : Bool) (i : Usize)
    (hi : i.val ≤ vm.entries.val.length)
    (htif : tif = true ↔ tif0 = true ∨
      ∃ p ∈ vm.entries.val.take i.val, ∃ I ∈ p.2.items.val,
        (vmLastEntry vm1.entries.val I).map Prod.snd = some tool) :
    transitions.unregister_tool_loop0 vm vm1 tool tif i ⦃ res =>
      res = true ↔ tif0 = true ∨
        ∃ p ∈ vm.entries.val, ∃ I ∈ p.2.items.val,
          (vmLastEntry vm1.entries.val I).map Prod.snd = some tool ⦄ := by
  unfold transitions.unregister_tool_loop0
  apply loop.spec_decr_nat
    (measure := fun p => vm.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ vm.entries.val.length ∧
      (p.1 = true ↔ tif0 = true ∨
        ∃ q ∈ vm.entries.val.take p.2.val, ∃ I ∈ q.2.items.val,
          (vmLastEntry vm1.entries.val I).map Prod.snd = some tool))
  · rintro ⟨tifL, iL⟩ ⟨hile, htifL⟩
    dsimp only at hile htifL ⊢
    simp only [transitions.unregister_tool_loop0.body, bind_tc_ok]
    have hlen : collections.VecMap.len types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId
        (collections.VecSet.Insts.CoreCloneClone types.InvocationId.Insts.CoreCloneClone) vm =
        .ok (alloc.vec.Vec.len vm.entries) := rfl
    rw [hlen]; simp only [bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < vm.entries.val.length := by scalar_tac
      obtain ⟨vs, hvsEq, hvs⟩ := spec_imp_exists
        (vecMapValAt_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId
          (collections.VecSet.Insts.CoreCloneClone types.InvocationId.Insts.CoreCloneClone)
          vm iL hlt)
      rw [hvsEq]; simp only [bind_tc_ok]
      rw [vecSetClone_spec types.InvocationId.Insts.CoreCloneClone invocationId_clone_spec vs]
      simp only [bind_tc_ok]
      obtain ⟨t2, ht2Eq, ht2Iff⟩ := spec_imp_exists
        (unregisterInner_spec vm1 tool vs tifL tifL 0#usize (by simp) (by simp))
      rw [ht2Eq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = iL.val + 1 →
          vm.entries.val.take i2.val = vm.entries.val.take (iL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.AgentId × collections.VecSet types.InvocationId → Prop),
          (∃ x ∈ vm.entries.val.take (iL.val + 1), P x) ↔
          (∃ x ∈ vm.entries.val.take iL.val, P x) ∨ P (vm.entries.val[iL.val]'hlt) := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨vm.entries.val[iL.val]'hlt, Or.inr rfl, hPi⟩
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi2 _ i2_post, hext, ht2Iff, htifL, hvs]
      constructor
      · rintro ((hA | hB) | hC)
        · exact Or.inl hA
        · exact Or.inr (Or.inl hB)
        · exact Or.inr (Or.inr hC)
      · rintro (hA | hB | hC)
        · exact Or.inl (Or.inl hA)
        · exact Or.inl (Or.inr hB)
        · exact Or.inr hC
    case isFalse h =>
      have heq' : iL.val = vm.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at htifL ⊢
      exact htifL
  · exact ⟨hi, htif⟩

/-- `unregister_tool` preserves the unified `R`. -/
theorem unregister_tool_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (tool : types.ToolId)
    (hR : R st bg a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.unregister_tool st bg tool = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.unregister_tool tool).guard a ∧
          (Tzimtzum.unregister_tool tool).next a a' ∧ R st' bg a' := by
  simp only [transitions.unregister_tool] at hok
  -- Gate: tool registered.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- The whole-map scan.
  obtain ⟨tif, htifEq, htifIff⟩ := spec_imp_exists
    (unregisterOuter_spec st.in_flight st.invocation_tool tool false false 0#usize
      (by simp) (by simp))
  rw [htifEq] at hok; simp only [bind_tc_ok] at hok
  have htif : tif = false := by cases tif with | false => rfl | true => simp at hok
  simp only [htif, reduceIte, Bool.false_eq_true] at hok
  have hNoTif : ¬ ∃ p ∈ st.in_flight.entries.val, ∃ I ∈ p.2.items.val,
      (vmLastEntry st.invocation_tool.entries.val I).map Prod.snd = some tool := by
    intro hc
    have := htifIff.mpr (Or.inr hc)
    rw [htif] at this; simp at this
  -- The point-remove.
  obtain ⟨vs', hvsEq, hvsMem⟩ := spec_imp_exists
    (vecSetRemove_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_ne_spec toolId_clone_spec
      st.tool_registered tool)
  rw [hvsEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  -- The no-in-flight guard: every live (last-match) pair is covered by the whole-entry scan.
  have hguard : ∀ (A : types.AgentId) (I : types.InvocationId),
      a.in_flight A I → a.invocation_tool I ≠ tool := by
    intro A I hIfl hc
    have hmem : vmsMemLast st.in_flight A I := (hR.inflight A I).mp hIfl
    obtain ⟨t, tm, ht, _⟩ := hR.wfInflight A I hmem
    have htEq : a.invocation_tool I = t := hR.invTool I t ht
    obtain ⟨vsI, hvsEntry, hIvs⟩ := hmem
    have hpmem : (A, vsI) ∈ st.in_flight.entries.val :=
      (List.mem_filter.mp (List.mem_of_getLast? hvsEntry)).1
    refine hNoTif ⟨(A, vsI), hpmem, I, hIvs, ?_⟩
    show invToolC st I = some tool
    rw [ht, ← htEq, hc]
  -- The abstract successor.
  refine ⟨{ a with
      tool_registered := fun T => a.tool_registered T ∧ T ≠ tool }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hR.tool_reg tool).mpr (hbIff.mp hb), hguard⟩
  · -- next
    simp [Tzimtzum.unregister_tool]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, fun t => ?_,
      hR.parent, hR.cap, hR.instr, hR.taint, hR.integ, hR.inflight, hR.override, hR.budget,
      hR.invUsed, hR.invEgress, hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor,
      hR.toolIntegInspectFloor, hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss,
      hR.instrIssuer, hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor,
      hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr, hR.ndTaint, hR.ndInteg,
      hR.ndInflight, hR.ndOverride, hR.ndFlowOverride, hR.ndBudget, hR.wfInflight⟩
    -- tool_registered (point-remove)
    show (a.tool_registered t ∧ t ≠ tool) ↔ vsMem vs' t
    rw [hvsMem t, hR.tool_reg t]

end ArgusLean.Refinement
