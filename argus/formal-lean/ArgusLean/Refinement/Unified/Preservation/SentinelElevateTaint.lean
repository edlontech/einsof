import ArgusLean.Refinement.Unified.Preservation.InvokeStart

/-! # Layer 1 — `sentinel_elevate_taint` preserves the unified `R`

V3 adaptation (design §5.6 row, task 12): the flow gate is restated over the agent's in-flight
invocations' ATTESTED egress (`invocation_egress`, per-invocation verdicts) with the vouch keyed
on the in-flight invocation (`invocation_gate_passes I`); override consumption is EAGER (an armed
`(agent, tool(I), l)` is marked used whenever the gate examined it, no denial conjunct); the ghost
clause is gone. The kernel's gate loop additionally tracks a `missing_binding` flag (an in-flight
invocation with no tool binding hard-errors) — under `R.wfInflight` that flag is always false, but
the inversion carries it so the success path discharges it structurally. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 4000000

/-! ## The gate loop (over the agent's flights, with the missing-binding flag) -/

/-- `sentinel_elevate_taint_loop0` folds `gate_egress` at the fixed `level` over the agent's
    in-flight invocations, flagging any invocation with no tool binding. -/
theorem sentinelGateLoop_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate agent t I st bg = .ok (cgOf t I))
    (ovOf ocOf : types.ToolId → Bool)
    (hov : ∀ t, state.KernelState.has_flow_override st agent t level = .ok (ovOf t))
    (hoc : ∀ t, state.KernelState.override_consumed st agent t level = .ok (ocOf t))
    (in_flight_invs : collections.VecSet types.InvocationId)
    (denied0 denied mb0 mb : Bool) (fi : Usize)
    (hfi : fi.val ≤ in_flight_invs.items.val.length)
    (hmb : mb = true ↔ mb0 = true ∨
      ∃ inv ∈ in_flight_invs.items.val.take fi.val, invToolC st inv = none)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ inv ∈ in_flight_invs.items.val.take fi.val, ∃ t, invToolC st inv = some t ∧
        ∃ E, vmsMemLast st.invocation_egress inv E ∧
          egressDenied (flowModeC bg level E) (cgOf t inv) (ovOf t) (ocOf t)) :
    transitions.sentinel_elevate_taint_loop0 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate agent level denied mb in_flight_invs fi
      ⦃ res =>
      (res.1 = true ↔ denied0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val, ∃ t, invToolC st inv = some t ∧
          ∃ E, vmsMemLast st.invocation_egress inv E ∧
            egressDenied (flowModeC bg level E) (cgOf t inv) (ovOf t) (ocOf t)) ∧
      (res.2 = true ↔ mb0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val, invToolC st inv = none) ⦄ := by
  unfold transitions.sentinel_elevate_taint_loop0
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => in_flight_invs.items.val.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ in_flight_invs.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val.take p.2.2.val, ∃ t, invToolC st inv = some t ∧
          ∃ E, vmsMemLast st.invocation_egress inv E ∧
            egressDenied (flowModeC bg level E) (cgOf t inv) (ovOf t) (ocOf t)) ∧
      (p.2.1 = true ↔ mb0 = true ∨
        ∃ inv ∈ in_flight_invs.items.val.take p.2.2.val, invToolC st inv = none))
  · rintro ⟨deniedL, mbL, fiL⟩ ⟨hile, hdenL, hmbL⟩
    dsimp only at hile hdenL hmbL ⊢
    simp only [transitions.sentinel_elevate_taint_loop0.body, collections.VecSet.len,
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
        have hnf : ¬ ∃ t, invToolC st flight_inv = some t ∧
            ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
              egressDenied (flowModeC bg level E) (cgOf t flight_inv) (ovOf t) (ocOf t) := by
          rintro ⟨t, ht, _⟩; rw [hnone] at ht; simp at ht
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
        have hsome : invToolC st flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        simp only []
        obtain ⟨flight_egress, hfeEq, hfeMem⟩ := spec_imp_exists
          (getSetOrEmpty_spec types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
            types.EgressKind.Insts.CoreCloneClone types.EgressKind.Insts.CoreCmpPartialEqEgressKind
            egressKind_clone_spec st.invocation_egress flight_inv)
        rw [hfeEq]; simp only [bind_tc_ok]
        rw [hst]
        obtain ⟨d2, hd2Eq, hd2Iff⟩ := spec_imp_exists
          (gateEgress_spec cgInst bg content_gate agent flight_tool_id flight_inv st level
            flight_egress (cgOf flight_tool_id flight_inv) (ovOf flight_tool_id)
            (ocOf flight_tool_id) (hcg flight_tool_id flight_inv) (hov flight_tool_id)
            (hoc flight_tool_id) (flowModeC bg level) (flowMode_eq bg level) deniedL)
        rw [hd2Eq]; simp only [bind_tc_ok]
        have hexPack : (∃ E ∈ flight_egress.items.val,
            egressDenied (flowModeC bg level E) (cgOf flight_tool_id flight_inv)
              (ovOf flight_tool_id) (ocOf flight_tool_id)) ↔
            (∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
              egressDenied (flowModeC bg level E) (cgOf flight_tool_id flight_inv)
                (ovOf flight_tool_id) (ocOf flight_tool_id)) := by
          constructor
          · rintro ⟨E, hE, hden⟩; exact ⟨E, (hfeMem E).mp hE, hden⟩
          · rintro ⟨E, hE, hden⟩; exact ⟨E, (hfeMem E).mpr hE, hden⟩
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ fi1_post, hext, hd2Iff, hexPack, hdenL]
          constructor
          · rintro ((hA1 | hA2) | hC)
            · exact Or.inl hA1
            · exact Or.inr (Or.inl hA2)
            · exact Or.inr (Or.inr ⟨flight_tool_id, hsome, hC⟩)
          · rintro (hA | hB | ⟨t, ht, hE⟩)
            · exact Or.inl (Or.inl hA)
            · exact Or.inl (Or.inr hB)
            · rw [hsome, Option.some_inj] at ht; subst ht; exact Or.inr hE
        · rw [hi2 _ fi1_post, hext, hmbL]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · rw [hsome] at hC; simp at hC
    case isFalse h =>
      have heq' : fiL.val = in_flight_invs.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL hmbL ⊢
      exact ⟨hdenL, hmbL⟩
  · exact ⟨hfi, hden, hmb⟩

/-! ## The eager consumption loop (over the agent's flights, at the single level) -/

/-- `sentinel_elevate_taint_loop1` inserts `{flight_tool_id, level}` for every in-flight
    invocation whose bound tool has an armed override at `level` — unconditional (eager
    consumption). Mirror of `invokeStartLoop7_spec`. -/
theorem sentinelConsLoop_spec
    (st : state.KernelState) (agent : types.AgentId) (level : types.ConfLevel)
    (in_flight_invs : collections.VecSet types.InvocationId)
    (to_consume0 to_consume : collections.VecSet types.OverrideKey) (ci : Usize)
    (hci : ci.val ≤ in_flight_invs.items.val.length)
    (hcap : to_consume0.items.val.length + in_flight_invs.items.val.length ≤ Usize.max)
    (hlen : to_consume.items.val.length ≤ to_consume0.items.val.length + ci.val)
    (hmem : ∀ k, vsMem to_consume k ↔ vsMem to_consume0 k ∨
      ∃ flight_inv ∈ in_flight_invs.items.val.take ci.val, ∃ t,
        invToolC st flight_inv = some t ∧
        k = ({ tool := t, level := level } : types.OverrideKey) ∧
        vmsMemLast st.flow_override agent { tool := t, level := level }) :
    transitions.sentinel_elevate_taint_loop1 st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget agent level in_flight_invs to_consume ci ⦃ res =>
      (∀ k, vsMem res k ↔ vsMem to_consume0 k ∨
        ∃ flight_inv ∈ in_flight_invs.items.val, ∃ t,
          invToolC st flight_inv = some t ∧
          k = ({ tool := t, level := level } : types.OverrideKey) ∧
          vmsMemLast st.flow_override agent { tool := t, level := level }) ∧
      res.items.val.length ≤ to_consume0.items.val.length + in_flight_invs.items.val.length ⦄ := by
  unfold transitions.sentinel_elevate_taint_loop1
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels,
      st.integ_levels, st.in_flight, st.invocation_tool, st.invocation_used,
      st.invocation_egress, st.tool_registered, st.agent_instruction, st.override_used,
      st.flow_override, st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => in_flight_invs.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ in_flight_invs.items.val.length ∧
      p.1.items.val.length ≤ to_consume0.items.val.length + p.2.val ∧
      (∀ k, vsMem p.1 k ↔ vsMem to_consume0 k ∨
        ∃ flight_inv ∈ in_flight_invs.items.val.take p.2.val, ∃ t,
          invToolC st flight_inv = some t ∧
          k = ({ tool := t, level := level } : types.OverrideKey) ∧
          vmsMemLast st.flow_override agent { tool := t, level := level }))
  · rintro ⟨tcL, ciL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL ⊢
    simp only [transitions.sentinel_elevate_taint_loop1.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : ciL.val < in_flight_invs.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = ciL.val + 1 →
          in_flight_invs.items.val.take i2.val = in_flight_invs.items.val.take (ciL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ in_flight_invs.items.val.take (ciL.val + 1), P x) ↔
          (∃ x ∈ in_flight_invs.items.val.take ciL.val, P x) ∨ P flight_inv := by
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
        have hnf : ∀ k, ¬ ∃ t, invToolC st flight_inv = some t ∧
            k = ({ tool := t, level := level } : types.OverrideKey) ∧
            vmsMemLast st.flow_override agent { tool := t, level := level } := by
          rintro k ⟨t, ht, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro k
        rw [hi2 _ ci1_post, hext, hmemL k]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC (hnf k)
      | some flight_tool_id =>
        have hsome : invToolC st flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        simp only []
        rw [hst]
        obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
          (hasFlowOverride_spec st agent flight_tool_id level)
        rw [hbEq]; simp only [bind_tc_ok]
        cases hbc : b with
        | true =>
          have hin : vmsMemLast st.flow_override agent
              { tool := flight_tool_id, level := level } := hbIff.mp hbc
          simp only [reduceIte]
          have hcapIns : tcL.items.val.length < Usize.max := by
            have := hlenL; have := hlt; have := hcap; omega
          obtain ⟨tc1, htc1Eq, htc1Mem, htc1Len⟩ := spec_imp_exists
            (vecSetInsertLen_spec types.OverrideKey.Insts.CoreCloneClone
              types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec tcL
              { tool := flight_tool_id, level := level } hcapIns)
          rw [htc1Eq]; simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, by omega, ?_, by scalar_tac⟩
          intro k
          rw [htc1Mem k, hi2 _ ci1_post, hext, hmemL k]
          constructor
          · rintro ((hA | hB) | hC)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
            · exact Or.inr (Or.inr ⟨flight_tool_id, hsome, hC, hin⟩)
          · rintro (hA | hB | ⟨t, ht, hk, hov⟩)
            · exact Or.inl (Or.inl hA)
            · exact Or.inl (Or.inr hB)
            · rw [hsome, Option.some_inj] at ht; subst ht
              exact Or.inr hk
        | false =>
          have hnin : ¬ vmsMemLast st.flow_override agent
              { tool := flight_tool_id, level := level } := by
            intro hc; have := hbIff.mpr hc; rw [hbc] at this; simp at this
          simp only [Bool.false_eq_true, reduceIte]
          step*
          refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
          intro k
          rw [hi2 _ ci1_post, hext, hmemL k]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | ⟨t, ht, hk, hov⟩)
            · exact Or.inl hA
            · exact Or.inr hB
            · rw [hsome, Option.some_inj] at ht; subst ht
              exact absurd hov (hk ▸ hnin)
    case isFalse h =>
      have heq' : ciL.val = in_flight_invs.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact ⟨hmemL, hlenL⟩
  · exact ⟨hci, hlen, hmem⟩

set_option maxHeartbeats 8000000

/-- `sentinel_elevate_taint` preserves the unified `R`. `hCg`/`hFlightUsed` play the same roles as
    in `invoke_start_preservesR`/`return_unendorsed_preservesR`. -/
theorem sentinel_elevate_taint_preservesR {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (level : types.ConfLevel)
    (hR : R st bg a)
    (hCg : CgAgree cgInst content_gate st bg a)
    (hFlightUsed : ∀ ag I, a.in_flight ag I → a.invocation_used I)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJ : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + vmSetLen st.in_flight agent ≤ Usize.max)
    (hcapCons : vmSetLen st.in_flight agent ≤ Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_elevate_taint agent (confA level)).guard a ∧
          (Tzimtzum.sentinel_elevate_taint agent (confA level)).next a a' ∧ R st' bg a' := by
  simp only [transitions.sentinel_elevate_taint] at hok
  -- Gate: agent active.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- The agent's flights.
  obtain ⟨in_flight_invs, hifEq, hifMem, hifLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight agent)
  rw [hifEq] at hok; simp only [bind_tc_ok] at hok
  -- The gate loop.
  obtain ⟨dm, hdmEq, hdmDen, hdmMb⟩ := spec_imp_exists
    (sentinelGateLoop_spec cgInst st bg content_gate agent level
      (fun t I => Classical.choose (hCg agent t I))
      (fun t I => (Classical.choose_spec (hCg agent t I)).1)
      (fun t => ovC st agent level t) (fun t => ocC st agent level t)
      (fun t => ovC_eq st agent level t) (fun t => ocC_eq st agent level t)
      in_flight_invs false false false false 0#usize (by simp) (by simp) (by simp))
  rw [hdmEq] at hok
  obtain ⟨denied, mb⟩ := dm
  simp only [bind_tc_ok] at hok
  dsimp only at hdmDen hdmMb hok
  have hmb : mb = false := by cases mb with | false => rfl | true => simp at hok
  simp only [hmb, reduceIte, Bool.false_eq_true] at hok
  have hd : denied = false := by cases denied with | false => rfl | true => simp at hok
  simp only [hd, reduceIte, Bool.false_eq_true] at hok
  -- The eager consumption loop.
  obtain ⟨tc0, htc0Eq, htc0Nil⟩ : ∃ tc0, collections.VecSet.new
      types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
      = Result.ok tc0 ∧ tc0.items.val = [] := ⟨_, rfl, rfl⟩
  rw [htc0Eq] at hok; simp only [bind_tc_ok] at hok
  have htc0Len : tc0.items.val.length = 0 := by rw [htc0Nil]; rfl
  obtain ⟨tc1, htc1Eq, htc1Mem, htc1Len⟩ := spec_imp_exists
    (sentinelConsLoop_spec st agent level in_flight_invs tc0 tc0 0#usize (by simp)
      (by rw [htc0Len, hifLen]; simpa using hcapCons) (by simp) (by simp))
  rw [htc1Eq] at hok; simp only [bind_tc_ok] at hok
  -- The conditional override_used write.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey tc1)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vmOv, hvmOvEq, hvmOvMem, hvmOvNd⟩ :
      ∃ vmOv, (if b1 = true then Result.ok st.override_used else (do
          let ai ← types.AgentId.Insts.CoreCloneClone.clone agent
          collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
            types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used ai tc1))
          = Result.ok vmOv ∧
        (∀ k v, vmsMemLast vmOv k v ↔
          vmsMemLast st.override_used k v ∨ (k = agent ∧ vsMem tc1 v)) ∧
        (vmNodupKeys st.override_used → vmNodupKeys vmOv) := by
    cases hb1c : b1 with
    | true =>
      refine ⟨st.override_used, by simp, fun k v => ?_, id⟩
      have hEmpty : tc1.items.val = [] := hb1Iff.mp hb1c
      simp [vsMem, hEmpty]
    | false =>
      simp only [Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok]
      obtain ⟨vmOv, hvmOvEq, hvmOvMem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone
          types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec
          overrideKey_clone_spec st.override_used agent tc1 hcapOvE
          (by intro p hp
              have h1 := hcapOvJ p hp
              have h2 := htc1Len
              rw [htc0Len, hifLen] at h2
              omega)
          (by have h2 := htc1Len; rw [htc0Len, hifLen] at h2; omega))
      obtain ⟨vmOvNd, hvmOvNdEq, hvmOvNdNd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone
          types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec
          overrideKey_clone_spec st.override_used agent tc1 hcapOvE
          (by intro p hp
              have h1 := hcapOvJ p hp
              have h2 := htc1Len
              rw [htc0Len, hifLen] at h2
              omega)
          (by have h2 := htc1Len; rw [htc0Len, hifLen] at h2; omega))
      have hvv : vmOvNd = vmOv := Result.ok.inj (hvmOvNdEq.symm.trans hvmOvEq)
      exact ⟨vmOv, hvmOvEq, hvmOvMem, hvv ▸ hvmOvNdNd⟩
  rw [hvmOvEq] at hok
  rw [agentId_clone_spec] at hok; simp only [bind_tc_ok] at hok
  -- The taint insert.
  obtain ⟨vmT, hvmTEq, hvmTMem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent level
      hcapTaintE hcapTaintS)
  obtain ⟨vmTNd, hvmTNdEq, hvmTNdNd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent level
      hcapTaintE hcapTaintS)
  have hvvT : vmTNd = vmT := Result.ok.inj (hvmTNdEq.symm.trans hvmTEq)
  rw [hvmTEq] at hok
  -- The stuck `let (denied, missing_binding) := (false, false)` only collapses under full `simp`
  -- (the recurring tuple-let gotcha).
  simp only [bind_tc_ok] at hok
  simp at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  -- Abstract bridges.
  have hbind : ∀ I, vmsMemLast st.in_flight agent I →
      invToolC st I = some (a.invocation_tool I) := by
    intro I hI
    obtain ⟨t, tm, ht, _⟩ := hR.wfInflight agent I hI
    rw [hR.invTool I t ht]; exact ht
  have ovC_iff : ∀ t, ovC st agent level t = true ↔
      vmsMemLast st.flow_override agent { tool := t, level := level } := fun t => by
    obtain ⟨bb, hbb, hbbIff⟩ := spec_imp_exists (hasFlowOverride_spec st agent t level)
    rw [ovC_eq st agent level t, Result.ok.injEq] at hbb
    rw [hbb]; exact hbbIff
  have ocC_iff : ∀ t, ocC st agent level t = true ↔
      vmsMemLast st.override_used agent { tool := t, level := level } := fun t => by
    obtain ⟨bb, hbb, hbbIff⟩ := spec_imp_exists (overrideConsumed_spec st agent t level)
    rw [ocC_eq st agent level t, Result.ok.injEq] at hbb
    rw [hbb]; exact hbbIff
  have hcgv : ∀ t I, Classical.choose (hCg agent t I) = true ↔ a.invocation_gate_passes I :=
    fun t I => (Classical.choose_spec (hCg agent t I)).2
  -- The gate guard.
  have hNoDen : ¬ ∃ inv ∈ in_flight_invs.items.val, ∃ t, invToolC st inv = some t ∧
      ∃ E, vmsMemLast st.invocation_egress inv E ∧
        egressDenied (flowModeC bg level E) (Classical.choose (hCg agent t inv))
          (ovC st agent level t) (ocC st agent level t) := by
    intro hc
    have := hdmDen.mpr (Or.inr hc)
    rw [hd] at this; simp at this
  have hguard : ∀ I E,
      a.in_flight agent I ∧ a.invocation_egress I E →
        a.flow_allows (confA level) E
        ∨ (a.flow_inspects (confA level) E ∧ a.invocation_gate_passes I)
        ∨ (a.flow_override agent (a.invocation_tool I) (confA level)
            ∧ ¬ a.override_used agent (a.invocation_tool I) (confA level)) := by
    rintro I E ⟨hIfl, hegr⟩
    have hmem := (hR.inflight agent I).mp hIfl
    have hmemFl : I ∈ in_flight_invs.items.val := (hifMem I).mpr hmem
    have hUsedI : a.invocation_used I := hFlightUsed agent I hIfl
    have hE : vmsMemLast st.invocation_egress I E := (hR.invEgress I hUsedI E).mp hegr
    obtain ⟨t, tm, htTool, _⟩ := hR.wfInflight agent I hmem
    have htI : a.invocation_tool I = t := by
      have h := htTool
      rw [hbind I hmem] at h; exact Option.some.inj h
    have hnd : ¬ egressDenied (flowModeC bg level E)
        (Classical.choose (hCg agent t I)) (ovC st agent level t) (ocC st agent level t) :=
      fun hc => hNoDen ⟨I, hmemFl, t, htTool, E, hE, hc⟩
    have hlevelC : confC (confA level) = level := by rw [confC_confA]
    rcases not_egressDenied_disj _ _ _ _ hnd with hA | ⟨hIns, hcgvv⟩ | ⟨hovv, hocv⟩
    · refine Or.inl ((hR.flowAllows (confA level) E).mpr ?_)
      rw [hlevelC]
      exact (flowModeC_allow_iff bg level E).mp hA
    · refine Or.inr (Or.inl ⟨(hR.flowInspects (confA level) E).mpr ?_, (hcgv t I).mp hcgvv⟩)
      rw [hlevelC]
      exact ((flowModeC_inspect_iff bg level E).mp hIns).2
    · rw [htI]
      refine Or.inr (Or.inr ⟨(hR.flowOverride agent t (confA level)).mpr ?_, ?_⟩)
      · rw [hlevelC]; exact (ovC_iff t).mp hovv
      · rw [hR.override agent t (confA level), hlevelC]
        intro hc
        have := (ocC_iff t).mpr hc
        rw [hocv] at this; simp at this
  -- The abstract successor.
  refine ⟨{ a with
      taint_levels := fun A L => a.taint_levels A L ∨ (A = agent ∧ L = confA level),
      override_used := fun A T L =>
        a.override_used A T L
        ∨ (A = agent ∧ L = confA level
            ∧ (∃ I, a.in_flight agent I ∧ T = a.invocation_tool I
               ∧ a.flow_override agent (a.invocation_tool I) (confA level))) }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hR.active agent).mpr (hbIff.mp hb), hguard⟩
  · -- next
    simp [Tzimtzum.sentinel_elevate_taint]
  · -- R st' bg a'
    have hOverrideIff : ∀ ag t L,
        (a.override_used ag t L
          ∨ (ag = agent ∧ L = confA level
              ∧ (∃ I, a.in_flight agent I ∧ t = a.invocation_tool I
                 ∧ a.flow_override agent (a.invocation_tool I) (confA level))))
        ↔ vmsMemLast vmOv ag { tool := t, level := confC L } := by
      intro ag t L
      rw [hvmOvMem ag { tool := t, level := confC L }, ← hR.override ag t L]
      apply or_congr_right
      constructor
      · rintro ⟨hag, hL, I, hIfl, htT, hflov⟩
        have hmem := (hR.inflight agent I).mp hIfl
        have hmemFl : I ∈ in_flight_invs.items.val := (hifMem I).mpr hmem
        obtain ⟨t', tm', htTool', _⟩ := hR.wfInflight agent I hmem
        have htI : a.invocation_tool I = t' := by
          have h := htTool'
          rw [hbind I hmem] at h; exact Option.some.inj h
        refine ⟨hag, ?_⟩
        rw [htc1Mem]
        refine Or.inr ⟨I, hmemFl, t', htTool',
          by rw [htT, htI, hL, confC_confA], ?_⟩
        rw [htI] at hflov
        have := (hR.flowOverride agent t' (confA level)).mp hflov
        rwa [confC_confA] at this
      · rintro ⟨hag, hC⟩
        rw [htc1Mem] at hC
        rcases hC with hC0 | ⟨flight_inv, hfl, t', htTool', hk, hov⟩
        · exact absurd hC0 (by simp [vsMem, htc0Nil])
        · rw [types.OverrideKey.mk.injEq] at hk
          obtain ⟨htk, hLk⟩ := hk
          have hmemFl : vmsMemLast st.in_flight agent flight_inv := (hifMem flight_inv).mp hfl
          have hIfl : a.in_flight agent flight_inv := (hR.inflight agent flight_inv).mpr hmemFl
          have htI : a.invocation_tool flight_inv = t' := by
            have h := htTool'
            rw [hbind flight_inv hmemFl] at h; exact Option.some.inj h
          refine ⟨hag, by rw [← confA_confC L, hLk], flight_inv, hIfl,
            by rw [htI]; exact htk, ?_⟩
          rw [htI, hR.flowOverride agent t' (confA level), confC_confA]
          exact hov
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg,
      hR.parent, hR.cap, hR.instr, fun ag L => ?_, hR.integ, hR.inflight,
      fun ag t L => hOverrideIff ag t L, hR.budget, hR.invUsed, hR.invEgress,
      hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor, hR.toolIntegInspectFloor,
      hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor, hR.flowOverride,
      hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr, hvvT ▸ hvmTNdNd hR.ndTaint, hR.ndInteg,
      hR.ndInflight, hvmOvNd hR.ndOverride, hR.ndFlowOverride, hR.ndBudget, hR.wfInflight⟩
    -- taint (point-insert at (agent, level))
    show (a.taint_levels ag L ∨ (ag = agent ∧ L = confA level))
      ↔ vmsMemLast vmT ag (confC L)
    rw [hvmTMem ag (confC L), hR.taint ag L]
    apply or_congr_right
    constructor
    · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [hL, confC_confA]⟩
    · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [← confA_confC L, hL]⟩

end ArgusLean.Refinement
