import ArgusLean.Refinement.Unified.Preservation.InvokeStart

/-! # Layer 1 — `sentinel_degrade_integrity` preserves the unified `R`

New V3 action (design §5.6, task 13): the platform reports ingestion at integrity `level`; the
kernel inserts it into the agent's `integ_levels`, gated against every in-flight tool's OWN
integrity floor (graduated, vouchable via the in-flight invocation's content-gate verdict, NO
override arm — endorsement is the only way up). Blocked degrade = the Warden must HOLD the
ingestion (platform obligation). The gate loop carries a `missing_binding` flag like
`sentinel_elevate_taint`'s; under `R.wfInflight` it is always false. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 4000000

/-- `le_integ` with the abstracted concrete level on the LEFT is the kernel's rank compare —
    the mirrored companion of `le_integ_integLeC` (file-local, as in the Return files). -/
private theorem le_integ_integLeC' (c : types.IntegLevel) (L : Tzimtzum.IntegLevel) :
    Tzimtzum.le_integ (integA c) L ↔ integLeC c (integC L) = true := by
  cases c <;> cases L <;> simp [Tzimtzum.le_integ, Tzimtzum.integRank, integA, integC, integLeC]

/-! ## The integ gate loop (over the agent's flights, with the missing-binding flag) -/

/-- `sentinel_degrade_integrity_loop` folds `integ_decision` at the fixed ingested `level` over
    the agent's in-flight invocations (each flight's OWN floor/inspect-floor), flagging any
    invocation with no tool binding; tools with no metadata are skipped. -/
theorem sentinelDegradeLoop_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.IntegLevel)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate agent t I st bg = .ok (cgOf t I))
    (in_flight_invs : collections.VecSet types.InvocationId)
    (denied0 denied mb0 mb : Bool) (fi : Usize)
    (hfi : fi.val ≤ in_flight_invs.items.val.length)
    (hmb : mb = true ↔ mb0 = true ∨
      ∃ inv ∈ in_flight_invs.items.val.take fi.val, invToolC st inv = none)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ inv ∈ in_flight_invs.items.val.take fi.val, ∃ t tmeta,
        invToolC st inv = some t ∧ toolMetaC bg t = some tmeta ∧
        ¬ (integLeC tmeta.integ_floor level = true
            ∨ (integLeC tmeta.integ_inspect_floor level = true ∧ cgOf t inv = true))) :
    transitions.sentinel_degrade_integrity_loop cgInst st.agent_active st.agent_parent
      st.agent_cap st.taint_levels st.integ_levels st.in_flight st.invocation_tool
      st.invocation_used st.invocation_egress st.tool_registered st.agent_instruction
      st.override_used st.flow_override st.agent_budget bg content_gate agent level denied mb
      in_flight_invs fi ⦃ res =>
      (res.1 = true ↔ denied0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val, ∃ t tmeta,
          invToolC st inv = some t ∧ toolMetaC bg t = some tmeta ∧
          ¬ (integLeC tmeta.integ_floor level = true
              ∨ (integLeC tmeta.integ_inspect_floor level = true ∧ cgOf t inv = true))) ∧
      (res.2 = true ↔ mb0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val, invToolC st inv = none) ⦄ := by
  unfold transitions.sentinel_degrade_integrity_loop
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => in_flight_invs.items.val.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ in_flight_invs.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val.take p.2.2.val, ∃ t tmeta,
          invToolC st inv = some t ∧ toolMetaC bg t = some tmeta ∧
          ¬ (integLeC tmeta.integ_floor level = true
              ∨ (integLeC tmeta.integ_inspect_floor level = true ∧ cgOf t inv = true))) ∧
      (p.2.1 = true ↔ mb0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val.take p.2.2.val, invToolC st inv = none))
  · rintro ⟨deniedL, mbL, fiL⟩ ⟨hile, hdenL, hmbL⟩
    dsimp only at hile hdenL hmbL ⊢
    simp only [transitions.sentinel_degrade_integrity_loop.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : fiL.val < in_flight_invs.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = fiL.val + 1 →
          in_flight_invs.items.val.take i2.val = in_flight_invs.items.val.take (fiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ in_flight_invs.items.val.take (fiL.val + 1), P x) ↔
          (∃ x ∈ in_flight_invs.items.val.take fiL.val, P x) ∨ P flight_inv := by
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
        have hnone : invToolC st flight_inv = none := by unfold invToolC; rw [← ho]; exact hocase
        have hnf : ¬ ∃ t tmeta, invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
            ¬ (integLeC tmeta.integ_floor level = true
                ∨ (integLeC tmeta.integ_inspect_floor level = true
                    ∧ cgOf t flight_inv = true)) := by
          rintro ⟨t, tmeta, ht, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ fi1_post, hext, hdenL]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC hnf
        · rw [hi2 _ fi1_post, hext]
          exact ⟨fun _ => Or.inr (Or.inr hnone), fun _ => trivial⟩
      | some flight_tool_id =>
        have hsomeInv : invToolC st flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        simp only []
        obtain ⟨o1, ho1Eq, ho1⟩ := spec_imp_exists (toolMetadata_spec bg flight_tool_id)
        rw [ho1Eq]; simp only [bind_tc_ok]
        cases hmcase : o1 with
        | none =>
          have hnm : toolMetaC bg flight_tool_id = none := by rw [← ho1]; exact hmcase
          have hnf : ¬ ∃ t tmeta, invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
              ¬ (integLeC tmeta.integ_floor level = true
                  ∨ (integLeC tmeta.integ_inspect_floor level = true
                      ∧ cgOf t flight_inv = true)) := by
            rintro ⟨t, tmeta, ht, hm, _⟩
            rw [hsomeInv, Option.some_inj] at ht; subst ht; rw [hnm] at hm; simp at hm
          simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
          · rw [hi2 _ fi1_post, hext, hdenL]
            constructor
            · rintro (hA | hB)
              · exact Or.inl hA
              · exact Or.inr (Or.inl hB)
            · rintro (hA | hB | hC)
              · exact Or.inl hA
              · exact Or.inr hB
              · exact absurd hC hnf
          · rw [hi2 _ fi1_post, hext, hmbL]
            constructor
            · rintro (hA | hB)
              · exact Or.inl hA
              · exact Or.inr (Or.inl hB)
            · rintro (hA | hB | hC)
              · exact Or.inl hA
              · exact Or.inr hB
              · rw [hsomeInv] at hC; simp at hC
        | some flight_meta =>
          have hm : toolMetaC bg flight_tool_id = some flight_meta := by rw [← ho1]; exact hmcase
          simp only []
          rw [hst]
          obtain ⟨id, hidEq, hidAllow, hidDeny⟩ := spec_imp_exists
            (integDecision_spec cgInst content_gate agent flight_tool_id flight_inv st bg
              flight_meta.integ_floor flight_meta.integ_inspect_floor level
              (cgOf flight_tool_id flight_inv) (hcg flight_tool_id flight_inv))
          rw [hidEq]
          have hPcur : (∃ t tmeta, invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
                ¬ (integLeC tmeta.integ_floor level = true
                    ∨ (integLeC tmeta.integ_inspect_floor level = true
                        ∧ cgOf t flight_inv = true))) ↔
              ¬ (integLeC flight_meta.integ_floor level = true
                  ∨ (integLeC flight_meta.integ_inspect_floor level = true
                      ∧ cgOf flight_tool_id flight_inv = true)) := by
            constructor
            · rintro ⟨t, tmeta, ht, hmm, hc⟩
              rw [hsomeInv, Option.some_inj] at ht; subst ht
              rw [hm, Option.some_inj] at hmm; subst hmm; exact hc
            · intro hc; exact ⟨flight_tool_id, flight_meta, hsomeInv, hm, hc⟩
          cases id with
          | Allowed =>
            have hnd : ¬ ¬ (integLeC flight_meta.integ_floor level = true
                ∨ (integLeC flight_meta.integ_inspect_floor level = true
                    ∧ cgOf flight_tool_id flight_inv = true)) := fun hc => hc (hidAllow.mp rfl)
            simp only [bind_tc_ok]
            step*
            refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
            · rw [hi2 _ fi1_post, hext, hPcur, hdenL]
              constructor
              · rintro (hA | hB)
                · exact Or.inl hA
                · exact Or.inr (Or.inl hB)
              · rintro (hA | hB | hC)
                · exact Or.inl hA
                · exact Or.inr hB
                · exact absurd hC hnd
            · rw [hi2 _ fi1_post, hext, hmbL]
              constructor
              · rintro (hA | hB)
                · exact Or.inl hA
                · exact Or.inr (Or.inl hB)
              · rintro (hA | hB | hC)
                · exact Or.inl hA
                · exact Or.inr hB
                · rw [hsomeInv] at hC; simp at hC
          | Denied =>
            have hd : ¬ (integLeC flight_meta.integ_floor level = true
                ∨ (integLeC flight_meta.integ_inspect_floor level = true
                    ∧ cgOf flight_tool_id flight_inv = true)) := hidDeny.mp rfl
            simp only [bind_tc_ok]
            step*
            refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
            · rw [hi2 _ fi1_post, hext]
              exact ⟨fun _ => Or.inr (Or.inr (hPcur.mpr hd)), fun _ => trivial⟩
            · rw [hi2 _ fi1_post, hext, hmbL]
              constructor
              · rintro (hA | hB)
                · exact Or.inl hA
                · exact Or.inr (Or.inl hB)
              · rintro (hA | hB | hC)
                · exact Or.inl hA
                · exact Or.inr hB
                · rw [hsomeInv] at hC; simp at hC
    case isFalse h =>
      have heq' : fiL.val = in_flight_invs.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL hmbL ⊢
      exact ⟨hdenL, hmbL⟩
  · exact ⟨hfi, hden, hmb⟩

set_option maxHeartbeats 8000000

/-- `sentinel_degrade_integrity` preserves the unified `R`. -/
theorem sentinel_degrade_integrity_preservesR {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (level : types.IntegLevel)
    (hR : R st bg a)
    (hCg : CgAgree cgInst content_gate st bg a)
    (hcapIntegE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIntegS : ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_degrade_integrity cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_degrade_integrity agent (integA level)).guard a ∧
          (Tzimtzum.sentinel_degrade_integrity agent (integA level)).next a a' ∧ R st' bg a' := by
  simp only [transitions.sentinel_degrade_integrity] at hok
  -- Gate: agent active.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- The agent's flights.
  obtain ⟨in_flight_invs, hifEq, hifMem, _⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight agent)
  rw [hifEq] at hok; simp only [bind_tc_ok] at hok
  -- The gate loop.
  obtain ⟨dm, hdmEq, hdmDen, hdmMb⟩ := spec_imp_exists
    (sentinelDegradeLoop_spec cgInst st bg content_gate agent level
      (fun t I => Classical.choose (hCg agent t I))
      (fun t I => (Classical.choose_spec (hCg agent t I)).1)
      in_flight_invs false false false false 0#usize (by simp) (by simp) (by simp))
  rw [hdmEq] at hok
  obtain ⟨denied, mb⟩ := dm
  simp only [bind_tc_ok] at hok
  dsimp only at hdmDen hdmMb hok
  have hmb : mb = false := by cases mb with | false => rfl | true => simp at hok
  simp only [hmb, reduceIte, Bool.false_eq_true] at hok
  have hd : denied = false := by cases denied with | false => rfl | true => simp at hok
  simp only [hd, reduceIte, Bool.false_eq_true] at hok
  -- The integ insert.
  rw [agentId_clone_spec] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vmI, hvmIEq, hvmIMem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_eq_spec integLevel_clone_spec st.integ_levels agent level
      hcapIntegE hcapIntegS)
  obtain ⟨vmINd, hvmINdEq, hvmINdNd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_eq_spec integLevel_clone_spec st.integ_levels agent level
      hcapIntegE hcapIntegS)
  have hvvI : vmINd = vmI := Result.ok.inj (hvmINdEq.symm.trans hvmIEq)
  rw [hvmIEq] at hok
  -- The stuck `let (integ_denied, missing_binding) := (false, false)` only collapses under full
  -- `simp` (the recurring tuple-let gotcha).
  simp only [bind_tc_ok] at hok
  simp at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  -- Abstract bridges + the gate guard.
  have hbind : ∀ I, vmsMemLast st.in_flight agent I →
      invToolC st I = some (a.invocation_tool I) := by
    intro I hI
    obtain ⟨t, tm, ht, _⟩ := hR.wfInflight agent I hI
    rw [hR.invTool I t ht]; exact ht
  have hcgv : ∀ t I, Classical.choose (hCg agent t I) = true ↔ a.invocation_gate_passes I :=
    fun t I => (Classical.choose_spec (hCg agent t I)).2
  have hNoDen : ¬ ∃ inv ∈ in_flight_invs.items.val, ∃ t tmeta,
      invToolC st inv = some t ∧ toolMetaC bg t = some tmeta ∧
      ¬ (integLeC tmeta.integ_floor level = true
          ∨ (integLeC tmeta.integ_inspect_floor level = true
              ∧ Classical.choose (hCg agent t inv) = true)) := by
    intro hc
    have := hdmDen.mpr (Or.inr hc)
    rw [hd] at this; simp at this
  have hguard : ∀ I,
      a.in_flight agent I →
        a.integ_allows (integA level) (a.invocation_tool I)
        ∨ (a.integ_inspects (integA level) (a.invocation_tool I)
            ∧ a.invocation_gate_passes I) := by
    intro I hIfl
    have hmem := (hR.inflight agent I).mp hIfl
    have hmemFl : I ∈ in_flight_invs.items.val := (hifMem I).mpr hmem
    obtain ⟨t, tm, htTool, htmMeta⟩ := hR.wfInflight agent I hmem
    have htI : a.invocation_tool I = t := by
      have h := htTool
      rw [hbind I hmem] at h; exact Option.some.inj h
    have hnd : integLeC tm.integ_floor level = true
        ∨ (integLeC tm.integ_inspect_floor level = true
            ∧ Classical.choose (hCg agent t I) = true) := by
      by_contra hc
      exact hNoDen ⟨I, hmemFl, t, tm, htTool, htmMeta, hc⟩
    rw [htI]
    have hFloorEqT : a.tool_integ_floor t = integA tm.integ_floor := hR.toolIntegFloor t tm htmMeta
    have hInspEqT : a.tool_integ_inspect_floor t = integA tm.integ_inspect_floor :=
      hR.toolIntegInspectFloor t tm htmMeta
    have hlevelC : integC (integA level) = level := by rw [integC_integA]
    rcases hnd with hA | ⟨hI', hcgvv⟩
    · exact Or.inl (by
        show Tzimtzum.le_integ (a.tool_integ_floor t) (integA level)
        rw [hFloorEqT, le_integ_integLeC', hlevelC]; exact hA)
    · exact Or.inr ⟨(by
        show Tzimtzum.le_integ (a.tool_integ_inspect_floor t) (integA level)
        rw [hInspEqT, le_integ_integLeC', hlevelC]; exact hI'), (hcgv t I).mp hcgvv⟩
  -- The abstract successor.
  refine ⟨{ a with
      integ_levels := fun A L => a.integ_levels A L ∨ (A = agent ∧ L = integA level) }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hR.active agent).mpr (hbIff.mp hb), hguard⟩
  · -- next
    simp [Tzimtzum.sentinel_degrade_integrity]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg,
      hR.parent, hR.cap, hR.instr, hR.taint, fun ag L => ?_, hR.inflight, hR.override, hR.budget,
      hR.invUsed, hR.invEgress, hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor,
      hR.toolIntegInspectFloor, hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss,
      hR.instrIssuer, hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor,
      hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr, hR.ndTaint,
      hvvI ▸ hvmINdNd hR.ndInteg, hR.ndInflight, hR.ndOverride, hR.ndFlowOverride, hR.ndBudget,
      hR.wfInflight⟩
    -- integ (point-insert at (agent, level))
    show (a.integ_levels ag L ∨ (ag = agent ∧ L = integA level))
      ↔ vmsMemLast vmI ag (integC L)
    rw [hvmIMem ag (integC L), hR.integ ag L]
    apply or_congr_right
    constructor
    · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [hL, integC_integA]⟩
    · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [← integA_integC L, hL]⟩

end ArgusLean.Refinement
