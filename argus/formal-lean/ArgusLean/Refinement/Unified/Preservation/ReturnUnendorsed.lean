import ArgusLean.Refinement.Unified.Preservation.InvokeStart

/-! # Layer 1 — `return_unendorsed` preserves the unified `R`

V3 rewrite (design §5.6 row, task 11): the parent inherits the child's conf taint set AND (new)
its integ set. The conf inheritance is flow-gated per (child level × parent in-flight invocation ×
that invocation's ATTESTED egress) — the gate now reads `invocation_egress` (per-invocation
verdicts) instead of the V2 static tool egress — with the vouch keyed on the in-flight invocation
(`invocation_gate_passes I`) and the usual single-use override arm. The integ inheritance is gated
against every parent in-flight tool's OWN integrity floor (graduated, vouchable, NO override arm).
Override consumption is EAGER (design §5.3): an armed `(parent, tool(I), L)` is marked used
whenever the gate examined it — no denial conjunct, mirroring `invoke_start`'s loops 6/7.

Structure: two gate loop pairs (outer over the child's set × inner over the parent's flights),
one consumption loop pair, then the two set inheritances (`extend_into`, skipped when the child's
set is empty) and the conditional `override_used` extension. Imports the `InvokeStart` module for
`not_egressDenied_disj` (the shared gate-disjunction splitter). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 4000000


/-! ## Conf gate: inner loop (per child taint level, over the parent's flights) -/

/-- `return_unendorsed_loop0_loop0` folds `gate_egress` at the fixed child `level`, one parent
    in-flight invocation at a time (looking up its bound tool and stored attested egress);
    unbound invocations leave `denied` unchanged. Mirror of `invokeStartLoop3_spec`. -/
theorem returnUnendConfInner_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (parent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate parent t I st bg = .ok (cgOf t I))
    (ovOf ocOf : types.ToolId → Bool)
    (hov : ∀ t, state.KernelState.has_flow_override st parent t level = .ok (ovOf t))
    (hoc : ∀ t, state.KernelState.override_consumed st parent t level = .ok (ocOf t))
    (parent_flights : collections.VecSet types.InvocationId) (denied0 denied : Bool) (fi : Usize)
    (hfi : fi.val ≤ parent_flights.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ flight_inv ∈ parent_flights.items.val.take fi.val, ∃ t, invToolC st flight_inv = some t ∧
        ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
          egressDenied (flowModeC bg level E) (cgOf t flight_inv) (ovOf t) (ocOf t)) :
    transitions.return_unendorsed_loop0_loop0 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate parent denied parent_flights level fi
      ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ parent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
          ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
            egressDenied (flowModeC bg level E) (cgOf t flight_inv) (ovOf t) (ocOf t) ⦄ := by
  unfold transitions.return_unendorsed_loop0_loop0
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => parent_flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ parent_flights.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ parent_flights.items.val.take p.2.val, ∃ t,
          invToolC st flight_inv = some t ∧
          ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
            egressDenied (flowModeC bg level E) (cgOf t flight_inv) (ovOf t) (ocOf t)))
  · rintro ⟨deniedL, fiL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.return_unendorsed_loop0_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : fiL.val < parent_flights.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = fiL.val + 1 →
          parent_flights.items.val.take i2.val = parent_flights.items.val.take (fiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ parent_flights.items.val.take (fiL.val + 1), P x) ↔
          (∃ x ∈ parent_flights.items.val.take fiL.val, P x) ∨ P flight_inv := by
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
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ fi1_post, hext, hdenL]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC hnf
      | some flight_tool_id =>
        have hsome : invToolC st flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        obtain ⟨flight_egress, hfeEq, hfeMem⟩ := spec_imp_exists
          (getSetOrEmpty_spec types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
            types.EgressKind.Insts.CoreCloneClone types.EgressKind.Insts.CoreCmpPartialEqEgressKind
            egressKind_clone_spec st.invocation_egress flight_inv)
        rw [hfeEq]; simp only [bind_tc_ok]
        rw [hst]
        obtain ⟨d2, hd2Eq, hd2Iff⟩ := spec_imp_exists
          (gateEgress_spec cgInst bg content_gate parent flight_tool_id flight_inv st level
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
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ fi1_post, hext, hd2Iff, hexPack, hdenL]
        constructor
        · rintro ((hA1 | hA2) | hC)
          · exact Or.inl hA1
          · exact Or.inr (Or.inl hA2)
          · exact Or.inr (Or.inr ⟨flight_tool_id, hsome, hC⟩)
        · rintro (hA | hB | ⟨t, ht, hE⟩)
          · exact Or.inl (Or.inl hA)
          · exact Or.inl (Or.inr hB)
          · rw [hsome, Option.some_inj] at ht; subst ht; exact Or.inr hE
    case isFalse h =>
      have heq' : fiL.val = parent_flights.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨hfi, hden⟩

/-! ## Conf gate: outer loop (over the child's taint levels) -/

/-- `return_unendorsed_loop0` folds the inner gate loop over every child taint level. -/
theorem returnUnendConfOuter_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (parent : types.AgentId)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate parent t I st bg = .ok (cgOf t I))
    (ovOf ocOf : types.ConfLevel → types.ToolId → Bool)
    (hov : ∀ L t, state.KernelState.has_flow_override st parent t L = .ok (ovOf L t))
    (hoc : ∀ L t, state.KernelState.override_consumed st parent t L = .ok (ocOf L t))
    (child_taint : collections.VecSet types.ConfLevel)
    (parent_flights : collections.VecSet types.InvocationId)
    (denied0 denied : Bool) (li : Usize)
    (hli : li.val ≤ child_taint.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ L ∈ child_taint.items.val.take li.val,
        ∃ flight_inv ∈ parent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
          ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
            egressDenied (flowModeC bg L E) (cgOf t flight_inv) (ovOf L t) (ocOf L t)) :
    transitions.return_unendorsed_loop0 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate parent child_taint denied parent_flights li
      ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ L ∈ child_taint.items.val,
          ∃ flight_inv ∈ parent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
            ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
              egressDenied (flowModeC bg L E) (cgOf t flight_inv) (ovOf L t) (ocOf L t) ⦄ := by
  unfold transitions.return_unendorsed_loop0
  apply loop.spec_decr_nat
    (measure := fun p => child_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ child_taint.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ L ∈ child_taint.items.val.take p.2.val,
          ∃ flight_inv ∈ parent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
            ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
              egressDenied (flowModeC bg L E) (cgOf t flight_inv) (ovOf L t) (ocOf L t)))
  · rintro ⟨deniedL, liL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.return_unendorsed_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : liL.val < child_taint.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      obtain ⟨d2, hd2Eq, hd2Iff⟩ := spec_imp_exists
        (returnUnendConfInner_spec cgInst st bg content_gate parent level cgOf hcg
          (ovOf level) (ocOf level) (hov level) (hoc level) parent_flights deniedL deniedL
          0#usize (by simp) (by simp))
      rw [hd2Eq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = liL.val + 1 →
          child_taint.items.val.take i2.val = child_taint.items.val.take (liL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.ConfLevel → Prop),
          (∃ x ∈ child_taint.items.val.take (liL.val + 1), P x) ↔
          (∃ x ∈ child_taint.items.val.take liL.val, P x) ∨ P level := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hlevel]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨level, Or.inr hlevel, hPi⟩
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi2 _ li1_post, hext, hd2Iff, hdenL]
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
      have heq' : liL.val = child_taint.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨hli, hden⟩

/-! ## Integ gate: inner loop (per child integ level, over the parent's flights) -/

/-- `return_unendorsed_loop1_loop0` folds `integ_decision` at the fixed child `level`, one parent
    in-flight invocation at a time (each flight's OWN floor/inspect-floor); unbound invocations or
    missing metadata leave `integ_denied` unchanged. Mirror of `invokeStartLoop5_spec`. -/
theorem returnUnendIntegInner_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (parent : types.AgentId) (level : types.IntegLevel)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate parent t I st bg = .ok (cgOf t I))
    (parent_flights : collections.VecSet types.InvocationId) (denied0 denied : Bool) (fi : Usize)
    (hfi : fi.val ≤ parent_flights.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ flight_inv ∈ parent_flights.items.val.take fi.val, ∃ t tmeta,
        invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
        ¬ (integLeC tmeta.integ_floor level = true
            ∨ (integLeC tmeta.integ_inspect_floor level = true ∧ cgOf t flight_inv = true))) :
    transitions.return_unendorsed_loop1_loop0 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate parent parent_flights denied level fi
      ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ parent_flights.items.val, ∃ t tmeta,
          invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
          ¬ (integLeC tmeta.integ_floor level = true
              ∨ (integLeC tmeta.integ_inspect_floor level = true ∧ cgOf t flight_inv = true)) ⦄ := by
  unfold transitions.return_unendorsed_loop1_loop0
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => parent_flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ parent_flights.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ parent_flights.items.val.take p.2.val, ∃ t tmeta,
          invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
          ¬ (integLeC tmeta.integ_floor level = true
              ∨ (integLeC tmeta.integ_inspect_floor level = true ∧ cgOf t flight_inv = true))))
  · rintro ⟨deniedL, fiL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.return_unendorsed_loop1_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : fiL.val < parent_flights.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = fiL.val + 1 →
          parent_flights.items.val.take i2.val = parent_flights.items.val.take (fiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ parent_flights.items.val.take (fiL.val + 1), P x) ↔
          (∃ x ∈ parent_flights.items.val.take fiL.val, P x) ∨ P flight_inv := by
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
                ∨ (integLeC tmeta.integ_inspect_floor level = true ∧ cgOf t flight_inv = true)) := by
          rintro ⟨t, tmeta, ht, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ fi1_post, hext, hdenL]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC hnf
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
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi2 _ fi1_post, hext, hdenL]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC hnf
        | some flight_meta =>
          have hm : toolMetaC bg flight_tool_id = some flight_meta := by rw [← ho1]; exact hmcase
          simp only []
          rw [hst]
          obtain ⟨id, hidEq, hidAllow, hidDeny⟩ := spec_imp_exists
            (integDecision_spec cgInst content_gate parent flight_tool_id flight_inv st bg
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
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            rw [hi2 _ fi1_post, hext, hPcur, hdenL]
            constructor
            · rintro (hA | hB)
              · exact Or.inl hA
              · exact Or.inr (Or.inl hB)
            · rintro (hA | hB | hC)
              · exact Or.inl hA
              · exact Or.inr hB
              · exact absurd hC hnd
          | Denied =>
            have hd : ¬ (integLeC flight_meta.integ_floor level = true
                ∨ (integLeC flight_meta.integ_inspect_floor level = true
                    ∧ cgOf flight_tool_id flight_inv = true)) := hidDeny.mp rfl
            simp only [bind_tc_ok]
            step*
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            rw [hi2 _ fi1_post, hext]
            exact ⟨fun _ => Or.inr (Or.inr (hPcur.mpr hd)), fun _ => trivial⟩
    case isFalse h =>
      have heq' : fiL.val = parent_flights.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨hfi, hden⟩

/-! ## Integ gate: outer loop (over the child's integ levels) -/

/-- `return_unendorsed_loop1` folds the inner integ gate loop over every child integ level. -/
theorem returnUnendIntegOuter_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (parent : types.AgentId)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate parent t I st bg = .ok (cgOf t I))
    (parent_flights : collections.VecSet types.InvocationId)
    (child_integ : collections.VecSet types.IntegLevel)
    (denied0 denied : Bool) (igi : Usize)
    (higi : igi.val ≤ child_integ.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ L ∈ child_integ.items.val.take igi.val,
        ∃ flight_inv ∈ parent_flights.items.val, ∃ t tmeta,
          invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
          ¬ (integLeC tmeta.integ_floor L = true
              ∨ (integLeC tmeta.integ_inspect_floor L = true ∧ cgOf t flight_inv = true))) :
    transitions.return_unendorsed_loop1 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate parent parent_flights child_integ denied
      igi ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ L ∈ child_integ.items.val,
          ∃ flight_inv ∈ parent_flights.items.val, ∃ t tmeta,
            invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
            ¬ (integLeC tmeta.integ_floor L = true
                ∨ (integLeC tmeta.integ_inspect_floor L = true ∧ cgOf t flight_inv = true)) ⦄ := by
  unfold transitions.return_unendorsed_loop1
  apply loop.spec_decr_nat
    (measure := fun p => child_integ.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ child_integ.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ L ∈ child_integ.items.val.take p.2.val,
          ∃ flight_inv ∈ parent_flights.items.val, ∃ t tmeta,
            invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
            ¬ (integLeC tmeta.integ_floor L = true
                ∨ (integLeC tmeta.integ_inspect_floor L = true ∧ cgOf t flight_inv = true))))
  · rintro ⟨deniedL, igiL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.return_unendorsed_loop1.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : igiL.val < child_integ.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      obtain ⟨d2, hd2Eq, hd2Iff⟩ := spec_imp_exists
        (returnUnendIntegInner_spec cgInst st bg content_gate parent level cgOf hcg
          parent_flights deniedL deniedL 0#usize (by simp) (by simp))
      rw [hd2Eq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = igiL.val + 1 →
          child_integ.items.val.take i2.val = child_integ.items.val.take (igiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.IntegLevel → Prop),
          (∃ x ∈ child_integ.items.val.take (igiL.val + 1), P x) ↔
          (∃ x ∈ child_integ.items.val.take igiL.val, P x) ∨ P level := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hlevel]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨level, Or.inr hlevel, hPi⟩
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi2 _ igi1_post, hext, hd2Iff, hdenL]
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
      have heq' : igiL.val = child_integ.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨higi, hden⟩

/-! ## Eager consumption: inner loop (per child taint level, over the parent's flights) -/

/-- `return_unendorsed_loop2_loop0` inserts `{flight_tool_id, level}` for every parent in-flight
    invocation whose bound tool has an armed override at the fixed child `level` — unconditional
    (eager consumption, no denial conjunct), mirroring `invokeStartLoop7_spec`. Stated over an
    arbitrary state `st2` because the kernel threads the ALREADY-UPDATED taint/integ maps through
    the loop's state fields (the loop only reads `invocation_tool` and `flow_override`). -/
theorem returnUnendConsInner_spec
    (st2 : state.KernelState) (parent : types.AgentId) (level : types.ConfLevel)
    (parent_flights : collections.VecSet types.InvocationId)
    (to_consume0 to_consume : collections.VecSet types.OverrideKey) (fi : Usize)
    (hfi : fi.val ≤ parent_flights.items.val.length)
    (hcap : to_consume0.items.val.length + parent_flights.items.val.length ≤ Usize.max)
    (hlen : to_consume.items.val.length ≤ to_consume0.items.val.length + fi.val)
    (hmem : ∀ k, vsMem to_consume k ↔ vsMem to_consume0 k ∨
      ∃ flight_inv ∈ parent_flights.items.val.take fi.val, ∃ t,
        invToolC st2 flight_inv = some t ∧
        k = ({ tool := t, level := level } : types.OverrideKey) ∧
        vmsMemLast st2.flow_override parent { tool := t, level := level }) :
    transitions.return_unendorsed_loop2_loop0 st2.agent_active st2.agent_parent st2.agent_cap
      st2.taint_levels st2.integ_levels st2.in_flight st2.invocation_tool st2.invocation_used
      st2.invocation_egress st2.tool_registered st2.agent_instruction st2.override_used
      st2.flow_override st2.agent_budget parent parent_flights to_consume level fi ⦃ res =>
      (∀ k, vsMem res k ↔ vsMem to_consume0 k ∨
        ∃ flight_inv ∈ parent_flights.items.val, ∃ t,
          invToolC st2 flight_inv = some t ∧
          k = ({ tool := t, level := level } : types.OverrideKey) ∧
          vmsMemLast st2.flow_override parent { tool := t, level := level }) ∧
      res.items.val.length ≤ to_consume0.items.val.length + parent_flights.items.val.length ⦄ := by
  unfold transitions.return_unendorsed_loop2_loop0
  have hst : ((⟨st2.agent_active, st2.agent_parent, st2.agent_cap, st2.taint_levels,
      st2.integ_levels, st2.in_flight, st2.invocation_tool, st2.invocation_used,
      st2.invocation_egress, st2.tool_registered, st2.agent_instruction, st2.override_used,
      st2.flow_override, st2.agent_budget⟩ : state.KernelState)) = st2 := by cases st2; rfl
  apply loop.spec_decr_nat
    (measure := fun p => parent_flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ parent_flights.items.val.length ∧
      p.1.items.val.length ≤ to_consume0.items.val.length + p.2.val ∧
      (∀ k, vsMem p.1 k ↔ vsMem to_consume0 k ∨
        ∃ flight_inv ∈ parent_flights.items.val.take p.2.val, ∃ t,
          invToolC st2 flight_inv = some t ∧
          k = ({ tool := t, level := level } : types.OverrideKey) ∧
          vmsMemLast st2.flow_override parent { tool := t, level := level }))
  · rintro ⟨tcL, fiL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL ⊢
    simp only [transitions.return_unendorsed_loop2_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : fiL.val < parent_flights.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st2.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = fiL.val + 1 →
          parent_flights.items.val.take i2.val = parent_flights.items.val.take (fiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ parent_flights.items.val.take (fiL.val + 1), P x) ↔
          (∃ x ∈ parent_flights.items.val.take fiL.val, P x) ∨ P flight_inv := by
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
        have hnone : invToolC st2 flight_inv = none := by unfold invToolC; rw [← ho]; exact hocase
        have hnf : ∀ k, ¬ ∃ t, invToolC st2 flight_inv = some t ∧
            k = ({ tool := t, level := level } : types.OverrideKey) ∧
            vmsMemLast st2.flow_override parent { tool := t, level := level } := by
          rintro k ⟨t, ht, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro k
        rw [hi2 _ fi1_post, hext, hmemL k]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC (hnf k)
      | some flight_tool_id =>
        have hsome : invToolC st2 flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        simp only []
        rw [hst]
        obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
          (hasFlowOverride_spec st2 parent flight_tool_id level)
        rw [hbEq]; simp only [bind_tc_ok]
        cases hbc : b with
        | true =>
          have hin : vmsMemLast st2.flow_override parent
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
          rw [htc1Mem k, hi2 _ fi1_post, hext, hmemL k]
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
          have hnin : ¬ vmsMemLast st2.flow_override parent
              { tool := flight_tool_id, level := level } := by
            intro hc; have := hbIff.mpr hc; rw [hbc] at this; simp at this
          simp only [Bool.false_eq_true, reduceIte]
          step*
          refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
          intro k
          rw [hi2 _ fi1_post, hext, hmemL k]
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
      have heq' : fiL.val = parent_flights.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact ⟨hmemL, hlenL⟩
  · exact ⟨hfi, hlen, hmem⟩

/-! ## Eager consumption: outer loop (over the child's taint levels) -/

/-- `return_unendorsed_loop2` folds the inner consumption loop over every child taint level. -/
theorem returnUnendConsOuter_spec
    (st2 : state.KernelState) (parent : types.AgentId)
    (child_taint : collections.VecSet types.ConfLevel)
    (parent_flights : collections.VecSet types.InvocationId)
    (to_consume0 to_consume : collections.VecSet types.OverrideKey) (ci : Usize)
    (hci : ci.val ≤ child_taint.items.val.length)
    (hcap : to_consume0.items.val.length
      + child_taint.items.val.length * parent_flights.items.val.length ≤ Usize.max)
    (hlen : to_consume.items.val.length
      ≤ to_consume0.items.val.length + ci.val * parent_flights.items.val.length)
    (hmem : ∀ k, vsMem to_consume k ↔ vsMem to_consume0 k ∨
      ∃ L ∈ child_taint.items.val.take ci.val,
        ∃ flight_inv ∈ parent_flights.items.val, ∃ t,
          invToolC st2 flight_inv = some t ∧
          k = ({ tool := t, level := L } : types.OverrideKey) ∧
          vmsMemLast st2.flow_override parent { tool := t, level := L }) :
    transitions.return_unendorsed_loop2 st2.agent_active st2.agent_parent st2.agent_cap
      st2.taint_levels st2.integ_levels st2.in_flight st2.invocation_tool st2.invocation_used
      st2.invocation_egress st2.tool_registered st2.agent_instruction st2.override_used
      st2.flow_override st2.agent_budget parent child_taint parent_flights to_consume ci ⦃ res =>
      (∀ k, vsMem res k ↔ vsMem to_consume0 k ∨
        ∃ L ∈ child_taint.items.val,
          ∃ flight_inv ∈ parent_flights.items.val, ∃ t,
            invToolC st2 flight_inv = some t ∧
            k = ({ tool := t, level := L } : types.OverrideKey) ∧
            vmsMemLast st2.flow_override parent { tool := t, level := L }) ∧
      res.items.val.length ≤ to_consume0.items.val.length
        + child_taint.items.val.length * parent_flights.items.val.length ⦄ := by
  unfold transitions.return_unendorsed_loop2
  apply loop.spec_decr_nat
    (measure := fun p => child_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ child_taint.items.val.length ∧
      p.1.items.val.length ≤ to_consume0.items.val.length
        + p.2.val * parent_flights.items.val.length ∧
      (∀ k, vsMem p.1 k ↔ vsMem to_consume0 k ∨
        ∃ L ∈ child_taint.items.val.take p.2.val,
          ∃ flight_inv ∈ parent_flights.items.val, ∃ t,
            invToolC st2 flight_inv = some t ∧
            k = ({ tool := t, level := L } : types.OverrideKey) ∧
            vmsMemLast st2.flow_override parent { tool := t, level := L }))
  · rintro ⟨tcL, ciL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL ⊢
    simp only [transitions.return_unendorsed_loop2.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : ciL.val < child_taint.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      obtain ⟨tc1, htc1Eq, htc1Mem, htc1Len⟩ := spec_imp_exists
        (returnUnendConsInner_spec st2 parent level parent_flights tcL tcL 0#usize (by simp)
          (by nlinarith [hlenL, hlt, hcap]) (by simp) (by simp))
      rw [htc1Eq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = ciL.val + 1 →
          child_taint.items.val.take i2.val = child_taint.items.val.take (ciL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.ConfLevel → Prop),
          (∃ x ∈ child_taint.items.val.take (ciL.val + 1), P x) ↔
          (∃ x ∈ child_taint.items.val.take ciL.val, P x) ∨ P level := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hlevel]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨level, Or.inr hlevel, hPi⟩
      step*
      refine ⟨by scalar_tac, by nlinarith [htc1Len, hlenL], ?_, by scalar_tac⟩
      intro k
      rw [htc1Mem k, hi2 _ ci1_post, hext, hmemL k]
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
      have heq' : ciL.val = child_taint.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact ⟨hmemL, hlenL⟩
  · exact ⟨hci, hlen, hmem⟩

set_option maxHeartbeats 8000000

/-- `return_unendorsed` preserves the unified `R`. The content-gate agreement enters as `hCg`
    (per-invocation `CgAgree`); `hFlightUsed` (the `in_flight_implies_used` strengthening
    invariant) routes the parent's in-flight egress reads through `R`'s used-only
    `RinvocationEgress`, exactly as in `invoke_start_preservesR`. -/
theorem return_unendorsed_preservesR {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (child parent : types.AgentId)
    (hR : R st bg a)
    (hCg : CgAgree cgInst content_gate st bg a)
    (hFlightUsed : ∀ ag I, a.in_flight ag I → a.invocation_used I)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintJ : ∀ p ∈ st.taint_levels.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapTaintO : vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapIntegE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIntegJ : ∀ p ∈ st.integ_levels.entries.val,
      p.2.items.val.length + vmSetLen st.integ_levels child ≤ Usize.max)
    (hcapIntegO : vmSetLen st.integ_levels child ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJ : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length
        + vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (hcapCons : vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_unendorsed cgInst st bg content_gate child parent
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.return_unendorsed child parent).guard a ∧
          (Tzimtzum.return_unendorsed child parent).next a a' ∧ R st' bg a' := by
  simp only [transitions.return_unendorsed] at hok
  -- Gate 1: parenthood.
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b, hbEq, hbIff⟩ :
      ∃ bb, core.cmp.PartialEq.ne.trait_default (core.option.Option.Insts.CoreCmpPartialEqOption
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId)) o (some parent) =
        .ok bb ∧ (bb = true ↔ o ≠ some parent) :=
    ⟨_, optionAgentId_ne_spec o (some parent), by simp⟩
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = false := by cases b with | false => rfl | true => simp at hok
  simp only [hb, reduceIte, Bool.false_eq_true] at hok
  have hoP : o = some parent := by
    by_contra hc; have := hbIff.mpr hc; rw [hb] at this; simp at this
  have hlast : vmLastEntry st.agent_parent.entries.val child = some (child, parent) := by
    have hoP' : (vmLastEntry st.agent_parent.entries.val child).map Prod.snd = some parent := by
      rw [← ho]; exact hoP
    cases hL : vmLastEntry st.agent_parent.entries.val child with
    | none => rw [hL] at hoP'; simp at hoP'
    | some p =>
      have hp1 : p.1 = child := vmLastEntry_fst _ _ _ hL
      rw [hL, Option.map_some] at hoP'
      obtain ⟨x, y⟩ := p
      simp only [Option.some_inj] at hoP'
      rw [show x = child from hp1, hoP']
  -- Gates 2/3: both active.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  -- Gate 4: child has nothing in flight.
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists
    (vecMapKVecSetSetNonempty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight child)
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  have hNoFlight : ∀ inv, ¬ vmsMemLast st.in_flight child inv := by
    intro inv hc
    have : b3 = true := hb3Iff.mpr ⟨inv, hc⟩
    rw [hb3] at this; simp at this
  -- The child's taint set + the parent's flights.
  obtain ⟨child_taint, hctEq, hctMem, hctLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec st.taint_levels child)
  rw [hctEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨parent_flights, hpfEq, hpfMem, hpfLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight parent)
  rw [hpfEq] at hok; simp only [bind_tc_ok] at hok
  -- The conf gate loop.
  obtain ⟨denied, hdEq, hdIff⟩ := spec_imp_exists
    (returnUnendConfOuter_spec cgInst st bg content_gate parent
      (fun t I => Classical.choose (hCg parent t I))
      (fun t I => (Classical.choose_spec (hCg parent t I)).1)
      (fun L t => ovC st parent L t) (fun L t => ocC st parent L t)
      (fun L t => ovC_eq st parent L t) (fun L t => ocC_eq st parent L t)
      child_taint parent_flights false false 0#usize (by simp) (by simp))
  rw [hdEq] at hok; simp only [bind_tc_ok] at hok
  have hd : denied = false := by cases denied with | false => rfl | true => simp at hok
  simp only [hd, reduceIte, Bool.false_eq_true] at hok
  -- The child's integ set + the integ gate loop.
  obtain ⟨child_integ, hciEq, hciMem, hciLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_clone_spec st.integ_levels child)
  rw [hciEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨integ_denied, hidEq, hidIff⟩ := spec_imp_exists
    (returnUnendIntegOuter_spec cgInst st bg content_gate parent
      (fun t I => Classical.choose (hCg parent t I))
      (fun t I => (Classical.choose_spec (hCg parent t I)).1)
      parent_flights child_integ false false 0#usize (by simp) (by simp))
  rw [hidEq] at hok; simp only [bind_tc_ok] at hok
  have hid : integ_denied = false := by
    cases integ_denied with | false => rfl | true => simp at hok
  simp only [hid, reduceIte, Bool.false_eq_true] at hok
  -- The taint inheritance (skipped when the child's set is empty).
  obtain ⟨b4, hb4Eq, hb4Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.ConfLevel.Insts.CoreCloneClone
      types.ConfLevel.Insts.CoreCmpPartialEqConfLevel child_taint)
  rw [hb4Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vmT, hvmTEq, hvmTMem, hvmTNd⟩ :
      ∃ vmT, (if b4 = true then Result.ok st.taint_levels else (do
          let ai ← types.AgentId.Insts.CoreCloneClone.clone parent
          collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
            types.ConfLevel.Insts.CoreCmpPartialEqConfLevel st.taint_levels ai child_taint))
          = Result.ok vmT ∧
        (∀ k v, vmsMemLast vmT k v ↔
          vmsMemLast st.taint_levels k v ∨ (k = parent ∧ vsMem child_taint v)) ∧
        (vmNodupKeys st.taint_levels → vmNodupKeys vmT) := by
    cases hb4c : b4 with
    | true =>
      refine ⟨st.taint_levels, by simp, fun k v => ?_, id⟩
      have hEmpty : child_taint.items.val = [] := hb4Iff.mp hb4c
      simp [vsMem, hEmpty]
    | false =>
      simp only [Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok]
      obtain ⟨vmT, hvmTEq, hvmTMem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels parent child_taint hcapTaintE
          (by intro p hp; have := hcapTaintJ p hp; rw [hctLen]; omega)
          (by rw [hctLen]; exact hcapTaintO))
      obtain ⟨vmTNd, hvmTNdEq, hvmTNdNd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels parent child_taint hcapTaintE
          (by intro p hp; have := hcapTaintJ p hp; rw [hctLen]; omega)
          (by rw [hctLen]; exact hcapTaintO))
      have hvv : vmTNd = vmT := Result.ok.inj (hvmTNdEq.symm.trans hvmTEq)
      exact ⟨vmT, hvmTEq, hvmTMem, hvv ▸ hvmTNdNd⟩
  rw [hvmTEq] at hok; simp only [bind_tc_ok] at hok
  -- The integ inheritance (skipped when the child's set is empty).
  obtain ⟨b5, hb5Eq, hb5Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.IntegLevel.Insts.CoreCloneClone
      types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel child_integ)
  rw [hb5Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vmI, hvmIEq, hvmIMem, hvmINd⟩ :
      ∃ vmI, (if b5 = true then Result.ok st.integ_levels else (do
          let ai ← types.AgentId.Insts.CoreCloneClone.clone parent
          collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId types.IntegLevel.Insts.CoreCloneClone
            types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel st.integ_levels ai child_integ))
          = Result.ok vmI ∧
        (∀ k v, vmsMemLast vmI k v ↔
          vmsMemLast st.integ_levels k v ∨ (k = parent ∧ vsMem child_integ v)) ∧
        (vmNodupKeys st.integ_levels → vmNodupKeys vmI) := by
    cases hb5c : b5 with
    | true =>
      refine ⟨st.integ_levels, by simp, fun k v => ?_, id⟩
      have hEmpty : child_integ.items.val = [] := hb5Iff.mp hb5c
      simp [vsMem, hEmpty]
    | false =>
      simp only [Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok]
      obtain ⟨vmI, hvmIEq, hvmIMem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels parent child_integ hcapIntegE
          (by intro p hp; have := hcapIntegJ p hp; rw [hciLen]; omega)
          (by rw [hciLen]; exact hcapIntegO))
      obtain ⟨vmINd, hvmINdEq, hvmINdNd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          integLevel_eq_spec integLevel_clone_spec st.integ_levels parent child_integ hcapIntegE
          (by intro p hp; have := hcapIntegJ p hp; rw [hciLen]; omega)
          (by rw [hciLen]; exact hcapIntegO))
      have hvv : vmINd = vmI := Result.ok.inj (hvmINdEq.symm.trans hvmIEq)
      exact ⟨vmI, hvmIEq, hvmIMem, hvv ▸ hvmINdNd⟩
  rw [hvmIEq] at hok; simp only [bind_tc_ok] at hok
  -- The eager consumption loop over the intermediate state.
  obtain ⟨tc0, htc0Eq, htc0Nil⟩ : ∃ tc0, collections.VecSet.new
      types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
      = Result.ok tc0 ∧ tc0.items.val = [] := ⟨_, rfl, rfl⟩
  rw [htc0Eq] at hok; simp only [bind_tc_ok] at hok
  have htc0Len : tc0.items.val.length = 0 := by rw [htc0Nil]; rfl
  have hst2InvTool : ({ st with taint_levels := vmT, integ_levels := vmI }
      : state.KernelState).invocation_tool = st.invocation_tool := rfl
  have hst2FlowOv : ({ st with taint_levels := vmT, integ_levels := vmI }
      : state.KernelState).flow_override = st.flow_override := rfl
  obtain ⟨tc1, htc1Eq, htc1Mem, htc1Len⟩ := spec_imp_exists
    (returnUnendConsOuter_spec { st with taint_levels := vmT, integ_levels := vmI } parent
      child_taint parent_flights tc0 tc0 0#usize (by simp)
      (by rw [htc0Len, hctLen, hpfLen]; simpa using hcapCons) (by simp) (by simp))
  rw [htc1Eq] at hok; simp only [bind_tc_ok] at hok
  -- The conditional override_used write.
  obtain ⟨b6, hb6Eq, hb6Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey tc1)
  rw [hb6Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨hFrames, hOvMem, hOvNd⟩ :
      (st'.taint_levels = vmT ∧ st'.integ_levels = vmI ∧ st'.agent_active = st.agent_active ∧
        st'.agent_parent = st.agent_parent ∧ st'.agent_cap = st.agent_cap ∧
        st'.in_flight = st.in_flight ∧ st'.invocation_tool = st.invocation_tool ∧
        st'.invocation_used = st.invocation_used ∧
        st'.invocation_egress = st.invocation_egress ∧
        st'.tool_registered = st.tool_registered ∧
        st'.agent_instruction = st.agent_instruction ∧
        st'.flow_override = st.flow_override ∧ st'.agent_budget = st.agent_budget) ∧
      (∀ k v, vmsMemLast st'.override_used k v ↔
        vmsMemLast st.override_used k v ∨ (k = parent ∧ vsMem tc1 v)) ∧
      (vmNodupKeys st.override_used → vmNodupKeys st'.override_used) := by
    cases hb6c : b6 with
    | true =>
      simp only [hb6c, reduceIte, Result.ok.injEq, core.result.Result.Ok.injEq,
        Prod.mk.injEq] at hok
      obtain ⟨hSt, _⟩ := hok
      subst hSt
      have hEmpty : tc1.items.val = [] := hb6Iff.mp hb6c
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun k v => by simp [vsMem, hEmpty], id⟩
    | false =>
      simp only [hb6c, Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok] at hok
      obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone
          types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec
          overrideKey_clone_spec st.override_used parent tc1 hcapOvE
          (by intro p hp
              have h1 := hcapOvJ p hp
              have h2 := htc1Len
              rw [htc0Len, hctLen, hpfLen] at h2
              omega)
          (by have h2 := htc1Len; rw [htc0Len, hctLen, hpfLen] at h2; omega))
      obtain ⟨vm2Nd, hvm2NdEq, hvm2NdNd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone
          types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec
          overrideKey_clone_spec st.override_used parent tc1 hcapOvE
          (by intro p hp
              have h1 := hcapOvJ p hp
              have h2 := htc1Len
              rw [htc0Len, hctLen, hpfLen] at h2
              omega)
          (by have h2 := htc1Len; rw [htc0Len, hctLen, hpfLen] at h2; omega))
      have hvv : vm2Nd = vm2 := Result.ok.inj (hvm2NdEq.symm.trans hvm2Eq)
      rw [hvm2Eq] at hok
      simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨hSt, _⟩ := hok
      subst hSt
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun k v => hvm2Mem k v, fun h => hvv ▸ hvm2NdNd h⟩
  obtain ⟨hTaintEq, hIntegEq, hAct, hPar, hCap, hInfl, hInvT, hInvU, hInvE, hToolReg, hAgInstr,
      hFlowOv, hBud⟩ := hFrames
  -- Abstract bridges.
  have hbind : ∀ I, vmsMemLast st.in_flight parent I →
      invToolC st I = some (a.invocation_tool I) := by
    intro I hI
    obtain ⟨t, tm, ht, _⟩ := hR.wfInflight parent I hI
    rw [hR.invTool I t ht]; exact ht
  have ovC_iff : ∀ L t, ovC st parent L t = true ↔
      vmsMemLast st.flow_override parent { tool := t, level := L } := fun L t => by
    obtain ⟨bb, hbb, hbbIff⟩ := spec_imp_exists (hasFlowOverride_spec st parent t L)
    rw [ovC_eq st parent L t, Result.ok.injEq] at hbb
    rw [hbb]; exact hbbIff
  have ocC_iff : ∀ L t, ocC st parent L t = true ↔
      vmsMemLast st.override_used parent { tool := t, level := L } := fun L t => by
    obtain ⟨bb, hbb, hbbIff⟩ := spec_imp_exists (overrideConsumed_spec st parent t L)
    rw [ocC_eq st parent L t, Result.ok.injEq] at hbb
    rw [hbb]; exact hbbIff
  have hcgv : ∀ t I, Classical.choose (hCg parent t I) = true ↔ a.invocation_gate_passes I :=
    fun t I => (Classical.choose_spec (hCg parent t I)).2
  -- The conf gate guard.
  have hNoDen : ¬ ∃ L ∈ child_taint.items.val,
      ∃ flight_inv ∈ parent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
        ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
          egressDenied (flowModeC bg L E) (Classical.choose (hCg parent t flight_inv))
            (ovC st parent L t) (ocC st parent L t) := by
    intro hc
    have := hdIff.mpr (Or.inr hc)
    rw [hd] at this; simp at this
  have hguardConf : ∀ L I E,
      a.taint_levels child L ∧ a.in_flight parent I ∧ a.invocation_egress I E →
        a.flow_allows L E
        ∨ (a.flow_inspects L E ∧ a.invocation_gate_passes I)
        ∨ (a.flow_override parent (a.invocation_tool I) L
            ∧ ¬ a.override_used parent (a.invocation_tool I) L) := by
    rintro L I E ⟨hT, hIfl, hegr⟩
    have hmem := (hR.inflight parent I).mp hIfl
    have hmemFl : I ∈ parent_flights.items.val := (hpfMem I).mpr hmem
    have hLmem : confC L ∈ child_taint.items.val :=
      (hctMem (confC L)).mpr ((hR.taint child L).mp hT)
    have hUsedI : a.invocation_used I := hFlightUsed parent I hIfl
    have hE : vmsMemLast st.invocation_egress I E := (hR.invEgress I hUsedI E).mp hegr
    obtain ⟨t, tm, htTool, _⟩ := hR.wfInflight parent I hmem
    have htI : a.invocation_tool I = t := by
      have h := htTool
      rw [hbind I hmem] at h; exact Option.some.inj h
    have hnd : ¬ egressDenied (flowModeC bg (confC L) E)
        (Classical.choose (hCg parent t I)) (ovC st parent (confC L) t)
        (ocC st parent (confC L) t) :=
      fun hc => hNoDen ⟨confC L, hLmem, I, hmemFl, t, htTool, E, hE, hc⟩
    rcases not_egressDenied_disj _ _ _ _ hnd with hA | ⟨hIns, hcgvv⟩ | ⟨hovv, hocv⟩
    · exact Or.inl ((hR.flowAllows L E).mpr ((flowModeC_allow_iff bg (confC L) E).mp hA))
    · exact Or.inr (Or.inl ⟨(hR.flowInspects L E).mpr
        ((flowModeC_inspect_iff bg (confC L) E).mp hIns).2, (hcgv t I).mp hcgvv⟩)
    · rw [htI]
      refine Or.inr (Or.inr ⟨(hR.flowOverride parent t L).mpr ((ovC_iff (confC L) t).mp hovv), ?_⟩)
      rw [hR.override parent t L]
      intro hc
      have := (ocC_iff (confC L) t).mpr hc
      rw [hocv] at this; simp at this
  -- The integ gate guard.
  have hNoInteg : ¬ ∃ L ∈ child_integ.items.val,
      ∃ flight_inv ∈ parent_flights.items.val, ∃ t tmeta,
        invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
        ¬ (integLeC tmeta.integ_floor L = true
            ∨ (integLeC tmeta.integ_inspect_floor L = true
                ∧ Classical.choose (hCg parent t flight_inv) = true)) := by
    intro hc
    have := hidIff.mpr (Or.inr hc)
    rw [hid] at this; simp at this
  have hguardInteg : ∀ L I,
      a.integ_levels child L ∧ a.in_flight parent I →
        a.integ_allows L (a.invocation_tool I)
        ∨ (a.integ_inspects L (a.invocation_tool I) ∧ a.invocation_gate_passes I) := by
    rintro L I ⟨hT, hIfl⟩
    have hmem := (hR.inflight parent I).mp hIfl
    have hmemFl : I ∈ parent_flights.items.val := (hpfMem I).mpr hmem
    have hLmem : integC L ∈ child_integ.items.val :=
      (hciMem (integC L)).mpr ((hR.integ child L).mp hT)
    obtain ⟨t, tm, htTool, htmMeta⟩ := hR.wfInflight parent I hmem
    have htI : a.invocation_tool I = t := by
      have h := htTool
      rw [hbind I hmem] at h; exact Option.some.inj h
    have hnd : integLeC tm.integ_floor (integC L) = true
        ∨ (integLeC tm.integ_inspect_floor (integC L) = true
            ∧ Classical.choose (hCg parent t I) = true) := by
      by_contra hc
      exact hNoInteg ⟨integC L, hLmem, I, hmemFl, t, tm, htTool, htmMeta, hc⟩
    rw [htI]
    have hFloorEqT : a.tool_integ_floor t = integA tm.integ_floor := hR.toolIntegFloor t tm htmMeta
    have hInspEqT : a.tool_integ_inspect_floor t = integA tm.integ_inspect_floor :=
      hR.toolIntegInspectFloor t tm htmMeta
    rcases hnd with hA | ⟨hI', hcgvv⟩
    · exact Or.inl (by
        show Tzimtzum.le_integ (a.tool_integ_floor t) L
        rw [hFloorEqT, le_integ_integLeC']; exact hA)
    · exact Or.inr ⟨(by
        show Tzimtzum.le_integ (a.tool_integ_inspect_floor t) L
        rw [hInspEqT, le_integ_integLeC']; exact hI'), (hcgv t I).mp hcgvv⟩
  -- The abstract successor.
  refine ⟨{ a with
      taint_levels := fun A L => a.taint_levels A L ∨ (A = parent ∧ a.taint_levels child L),
      integ_levels := fun A L => a.integ_levels A L ∨ (A = parent ∧ a.integ_levels child L),
      override_used := fun A T L =>
        a.override_used A T L
        ∨ (A = parent ∧ a.taint_levels child L
            ∧ (∃ I, a.in_flight parent I ∧ T = a.invocation_tool I
               ∧ a.flow_override parent (a.invocation_tool I) L)) }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hR.parent child parent).mpr hlast, (hR.active child).mpr (hb1Iff.mp hb1),
      (hR.active parent).mpr (hb2Iff.mp hb2),
      fun I hc => hNoFlight I ((hR.inflight child I).mp hc), hguardConf, hguardInteg⟩
  · -- next
    simp [Tzimtzum.return_unendorsed]
  · -- R st' bg a'
    have hOverrideIff : ∀ ag t L,
        (a.override_used ag t L
          ∨ (ag = parent ∧ a.taint_levels child L
              ∧ (∃ I, a.in_flight parent I ∧ t = a.invocation_tool I
                 ∧ a.flow_override parent (a.invocation_tool I) L)))
        ↔ vmsMemLast st'.override_used ag { tool := t, level := confC L } := by
      intro ag t L
      rw [hOvMem ag { tool := t, level := confC L }, ← hR.override ag t L]
      apply or_congr_right
      constructor
      · rintro ⟨hag, hT, I, hIfl, htT, hflov⟩
        have hmem := (hR.inflight parent I).mp hIfl
        have hmemFl : I ∈ parent_flights.items.val := (hpfMem I).mpr hmem
        obtain ⟨t', tm', htTool', _⟩ := hR.wfInflight parent I hmem
        have htI : a.invocation_tool I = t' := by
          have h := htTool'
          rw [hbind I hmem] at h; exact Option.some.inj h
        refine ⟨hag, ?_⟩
        rw [htc1Mem]
        refine Or.inr ⟨confC L, (hctMem (confC L)).mpr ((hR.taint child L).mp hT),
          I, hmemFl, t', ?_, by rw [htT, htI], ?_⟩
        · rw [show invToolC { st with taint_levels := vmT, integ_levels := vmI } I
              = invToolC st I from rfl]
          exact htTool'
        · show vmsMemLast ({ st with taint_levels := vmT, integ_levels := vmI }
              : state.KernelState).flow_override parent { tool := t', level := confC L }
          rw [htI] at hflov
          exact (hR.flowOverride parent t' L).mp hflov
      · rintro ⟨hag, hC⟩
        rw [htc1Mem] at hC
        rcases hC with hC0 | ⟨level, hlevel, flight_inv, hfl, t', htTool', hk, hov⟩
        · exact absurd hC0 (by simp [vsMem, htc0Nil])
        · rw [types.OverrideKey.mk.injEq] at hk
          obtain ⟨htk, hLk⟩ := hk
          rw [show invToolC { st with taint_levels := vmT, integ_levels := vmI } flight_inv
              = invToolC st flight_inv from rfl] at htTool'
          have hov' : vmsMemLast st.flow_override parent { tool := t', level := level } := hov
          have hmemFl : vmsMemLast st.in_flight parent flight_inv := (hpfMem flight_inv).mp hfl
          have hIfl : a.in_flight parent flight_inv := (hR.inflight parent flight_inv).mpr hmemFl
          have htI : a.invocation_tool flight_inv = t' := by
            have h := htTool'
            rw [hbind flight_inv hmemFl] at h; exact Option.some.inj h
          refine ⟨hag, (hR.taint child L).mpr (by rw [hLk]; exact (hctMem level).mp hlevel),
            flight_inv, hIfl, by rw [htI]; exact htk, ?_⟩
          rw [htI, hR.flowOverride parent t' L, hLk]
          exact hov'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov,
      fun x => by rw [hAct]; exact hR.active x,
      fun t => by rw [hToolReg]; exact hR.tool_reg t,
      fun Ch P => by rw [hPar]; exact hR.parent Ch P,
      fun N Cp => by rw [hCap]; exact hR.cap N Cp,
      fun ag ins => by rw [hAgInstr]; exact hR.instr ag ins,
      fun ag L => ?_, fun ag L => ?_,
      fun ag I => by rw [hInfl]; exact hR.inflight ag I,
      fun ag t L => hOverrideIff ag t L,
      fun G => by rw [hBud]; exact hR.budget G,
      fun I => by rw [hInvU]; exact hR.invUsed I,
      fun I hU E => by rw [hInvE]; exact hR.invEgress I hU E,
      hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor, hR.toolIntegInspectFloor,
      hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor,
      fun A T L => by rw [hFlowOv]; exact hR.flowOverride A T L,
      fun I t hI => hR.invTool I t (by rwa [show invToolC st' I = invToolC st I from by
        unfold invToolC; rw [hInvT]] at hI),
      by rw [hPar]; exact hR.ndParent, by rw [hCap]; exact hR.ndCap,
      by rw [hAgInstr]; exact hR.ndInstr,
      by rw [hTaintEq]; exact hvmTNd hR.ndTaint,
      by rw [hIntegEq]; exact hvmINd hR.ndInteg,
      by rw [hInfl]; exact hR.ndInflight, hOvNd hR.ndOverride,
      by rw [hFlowOv]; exact hR.ndFlowOverride,
      by rw [hBud]; exact hR.ndBudget, ?_⟩
    · -- taint (parent inherits the child's set)
      show (a.taint_levels ag L ∨ (ag = parent ∧ a.taint_levels child L))
        ↔ vmsMemLast st'.taint_levels ag (confC L)
      rw [hTaintEq, hvmTMem ag (confC L), hR.taint ag L]
      apply or_congr_right
      constructor
      · rintro ⟨hag, hT⟩; exact ⟨hag, (hctMem (confC L)).mpr ((hR.taint child L).mp hT)⟩
      · rintro ⟨hag, hT⟩; exact ⟨hag, (hR.taint child L).mpr ((hctMem (confC L)).mp hT)⟩
    · -- integ (parent inherits the child's set)
      show (a.integ_levels ag L ∨ (ag = parent ∧ a.integ_levels child L))
        ↔ vmsMemLast st'.integ_levels ag (integC L)
      rw [hIntegEq, hvmIMem ag (integC L), hR.integ ag L]
      apply or_congr_right
      constructor
      · rintro ⟨hag, hT⟩; exact ⟨hag, (hciMem (integC L)).mpr ((hR.integ child L).mp hT)⟩
      · rintro ⟨hag, hT⟩; exact ⟨hag, (hR.integ child L).mpr ((hciMem (integC L)).mp hT)⟩
    · -- wfInflight (in_flight and invocation_tool both framed)
      intro ag I hmemI
      rw [hInfl] at hmemI
      obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hmemI
      refine ⟨t, tmeta, ?_, htm⟩
      rw [show invToolC st' I = invToolC st I from by unfold invToolC; rw [hInvT]]
      exact ht

end ArgusLean.Refinement
