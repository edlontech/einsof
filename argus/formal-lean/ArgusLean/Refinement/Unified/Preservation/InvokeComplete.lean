import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — the `invoke_complete` split pair preserves the unified `R`

V3 rewrite (design §5.4 "invoke_complete shape", task 10): the kernel's single `invoke_complete`
with its `crossing_ok` `if/else` refines **two** spec actions with complementary total guards —
`invoke_complete_endorsed` (requires `crossing_ok`, point-clears in-flight, self-debits the
dimension-adjusted `crossing_weight`) and `invoke_complete_unendorsed` (requires `¬ crossing_ok`,
point-clears in-flight, inserts the tool's `conf_floor` into taint AND its `output_integ` into
integ, zero debit). The branch taken is visible in the event's `endorsed : Bool`, which is how the
two preservation theorems select their spec action from the same kernel run.

The crossing guard is the 5-conjunct `output_bounded ∧ invocation_conforms ∧ cap_declassify ∧
affordable crossing_weight ∧ (conf_helps ∨ integ_helps)` with the dimension-adjusted weight: pay
`declass_weight conf_floor` only if the conf insert would be new, `integ_weight output_integ` only
if the integ drop would be real. The conformance verdict is per-invocation (`CfAgree`-shaped `hcf`,
V3 rekeying); `R.wfInflight` rules out the kernel's defensive no-binding / no-metadata exits. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

private theorem declassWeight_le (L : Tzimtzum.ConfLevel) : Tzimtzum.declass_weight L ≤ 4 := by
  cases L <;> decide

private theorem integWeight_le (L : Tzimtzum.IntegLevel) : Tzimtzum.integ_weight L ≤ 4 := by
  cases L <;> decide

open Classical in
/-- The concrete dimension-adjusted crossing weight (design §5.4): the conf half is owed only if
    the agent does not already hold the tool's conf floor, the integ half only if it does not
    already hold the tool's output integrity. Mirror of the spec's `crossing_weight` over the
    kernel's last-match reads. -/
noncomputable def crossingWeightC (st : state.KernelState) (agent : types.AgentId)
    (tmeta : background.ToolMetadata) : Nat :=
  (if vmsMemLast st.taint_levels agent tmeta.conf_floor then 0
   else Tzimtzum.declass_weight (confA tmeta.conf_floor))
  + (if vmsMemLast st.integ_levels agent tmeta.output_integ then 0
     else Tzimtzum.integ_weight (integA tmeta.output_integ))

/-- The concrete crossing guard: the 5-conjunct `crossing_ok` over the kernel's reads (the
    conformance verdict enters as the oracle boolean `cf`). Mirror of the spec's `crossing_ok`. -/
def crossingOkC (st : state.KernelState) (agent : types.AgentId)
    (tmeta : background.ToolMetadata) (cf : Bool) : Prop :=
  tmeta.output_bounded = true ∧ cf = true ∧
    vmsMemLast st.agent_cap agent capability.CapKind.Declassify ∧
    crossingWeightC st agent tmeta ≤ (budgetReadC st.agent_budget agent).val ∧
    (¬ vmsMemLast st.taint_levels agent tmeta.conf_floor
     ∨ ¬ vmsMemLast st.integ_levels agent tmeta.output_integ)

/-- Comprehensive inversion: gates, the in-flight point-clear, and the two-branch outcome — the
    endorsed branch (event bool `true`, `crossingOkC`, weighted budget debit, taint/integ framed)
    or the unendorsed branch (event bool `false`, `¬ crossingOkC`, budget framed, both inserts
    exposed in the last-match view with their nodup posts). -/
theorem invoke_complete_inv_full {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (agent : types.AgentId) (inv : types.InvocationId)
    (cfOf : types.ToolId → Bool)
    (hcf : ∀ t s, cfInst.conforms conformance agent t inv s bg = .ok (cfOf t))
    (hWf : ∀ ag I, vmsMemLast st.in_flight ag I →
      ∃ t tmeta, invToolC st I = some t ∧ toolMetaC bg t = some tmeta)
    (hcapBudget : st.agent_budget.entries.val.length < Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIntegE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIntegS : ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_complete cfInst st bg conformance agent inv = .ok (.Ok (st', ev))) :
    vmsMemLast st.in_flight agent inv ∧
    vsMem st.agent_active agent ∧
    ∃ tool tmeta, invToolC st inv = some tool ∧ toolMetaC bg tool = some tmeta ∧
    (∀ k v, vmsMemLast st'.in_flight k v ↔ vmsMemLast st.in_flight k v ∧ ¬ (k = agent ∧ v = inv)) ∧
    (vmNodupKeys st.in_flight → vmNodupKeys st'.in_flight) ∧
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.invocation_tool = st.invocation_tool ∧
    st'.invocation_used = st.invocation_used ∧ st'.invocation_egress = st.invocation_egress ∧
    st'.tool_registered = st.tool_registered ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.override_used = st.override_used ∧ st'.flow_override = st.flow_override ∧
    ((ev = event.KernelAction.InvokeComplete agent inv true ∧
        crossingOkC st agent tmeta (cfOf tool) ∧
        st'.taint_levels = st.taint_levels ∧ st'.integ_levels = st.integ_levels ∧
        (∀ G, (budgetReadC st'.agent_budget G).val =
          if G = agent then
            (budgetReadC st.agent_budget agent).val - crossingWeightC st agent tmeta
          else (budgetReadC st.agent_budget G).val) ∧
        (vmNodupKeys st.agent_budget → vmNodupKeys st'.agent_budget))
     ∨ (ev = event.KernelAction.InvokeComplete agent inv false ∧
        ¬ crossingOkC st agent tmeta (cfOf tool) ∧
        st'.agent_budget = st.agent_budget ∧
        (∀ ag L', vmsMemLast st'.taint_levels ag L' ↔
          vmsMemLast st.taint_levels ag L' ∨ (ag = agent ∧ L' = tmeta.conf_floor)) ∧
        (vmNodupKeys st.taint_levels → vmNodupKeys st'.taint_levels) ∧
        (∀ ag L', vmsMemLast st'.integ_levels ag L' ↔
          vmsMemLast st.integ_levels ag L' ∨ (ag = agent ∧ L' = tmeta.output_integ)) ∧
        (vmNodupKeys st.integ_levels → vmNodupKeys st'.integ_levels))) := by
  simp only [transitions.invoke_complete] at hok
  -- Gate 1: `(agent, inv)` in-flight.
  obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
    (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_eq_spec invocationId_clone_spec st.in_flight agent inv)
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  have hInFlight : vmsMemLast st.in_flight agent inv := hbIff.mp hb
  -- Gate 2: `agent` active.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  have hActive : vsMem st.agent_active agent := hb1Iff.mp hb1
  -- `remove_from` point-clears `(agent, inv)` from `in_flight`; nodup post.
  obtain ⟨vm, hvmEq, hvmMem⟩ := spec_imp_exists
    (vecMapKVecSetRemoveFrom_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec agentId_clone_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_ne_spec invocationId_clone_spec st.in_flight agent inv)
  obtain ⟨vmNd, hvmNdEq, hvmNd⟩ := spec_imp_exists
    (vecMapKVecSetRemoveFrom_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec agentId_clone_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_ne_spec invocationId_clone_spec st.in_flight agent inv)
  have hvvNd : vmNd = vm := Result.ok.inj (hvmNdEq.symm.trans hvmEq)
  rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
  -- The bound tool of `inv` (`wfInflight` kills the defensive `none` exits).
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool inv)
  rw [hoEq] at hok; simp only [bind_tc_ok] at hok
  have hoInv : o = invToolC st inv := by rw [ho]; rfl
  obtain ⟨tool, tmeta, htool, htmeta⟩ := hWf agent inv hInFlight
  have hoTool : o = some tool := by rw [hoInv]; exact htool
  rw [hoTool] at hok
  dsimp only at hok
  obtain ⟨o1, ho1Eq, ho1⟩ := spec_imp_exists (toolMetadata_spec bg tool)
  rw [ho1Eq] at hok; simp only [bind_tc_ok] at hok
  have ho1tmeta : o1 = some tmeta := by rw [ho1]; exact htmeta
  rw [ho1tmeta] at hok
  simp only [bind_tc_ok] at hok
  -- Already-tainted / already-degraded reads (the two `helps` dimensions). The full `simp` also
  -- collapses the tuple-`let (conf_floor, output_bounded, output_integ)` (the V2 gotcha).
  obtain ⟨bt, hbtEq, hbtIff⟩ := spec_imp_exists
    (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent tmeta.conf_floor)
  obtain ⟨bi, hbiEq, hbiIff⟩ := spec_imp_exists
    (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_eq_spec integLevel_clone_spec st.integ_levels agent tmeta.output_integ)
  simp [hbtEq, hbiEq, bind_tc_ok] at hok
  -- The two weight halves (dimension-adjusted: owed only when the dimension helps).
  obtain ⟨wc, hwcEq, hwcVal⟩ :
      ∃ wc : Std.U8,
        (if bt = false then (do
            let i1 ← types.declass_weight tmeta.conf_floor
            Result.ok ((true : Bool), i1)) else Result.ok ((false : Bool), 0#u8))
          = Result.ok (!bt, wc) ∧
        wc.val = (if bt = true then 0 else Tzimtzum.declass_weight (confA tmeta.conf_floor)) := by
    cases bt with
    | true => exact ⟨0#u8, by simp, by simp⟩
    | false =>
      obtain ⟨w, hwEq, hwVal⟩ := declassWeight_spec (confA tmeta.conf_floor)
      rw [confC_confA] at hwEq
      exact ⟨w, by simp [hwEq], by simp [hwVal]⟩
  obtain ⟨wi, hwiEq, hwiVal⟩ :
      ∃ wi : Std.U8,
        (if bi = false then (do
            let i1 ← types.integ_weight tmeta.output_integ
            Result.ok ((true : Bool), i1)) else Result.ok ((false : Bool), 0#u8))
          = Result.ok (!bi, wi) ∧
        wi.val = (if bi = true then 0 else Tzimtzum.integ_weight (integA tmeta.output_integ)) := by
    cases bi with
    | true => exact ⟨0#u8, by simp, by simp⟩
    | false =>
      obtain ⟨w, hwEq, hwVal⟩ := integWeight_spec (integA tmeta.output_integ)
      rw [integC_integA] at hwEq
      exact ⟨w, by simp [hwEq], by simp [hwVal]⟩
  simp only [hwcEq, hwiEq, bind_tc_ok] at hok
  -- The summed weight (no overflow: both halves are ≤ 4).
  have hwcB : wc.val ≤ 4 := by
    rw [hwcVal]; split
    · omega
    · exact declassWeight_le (confA tmeta.conf_floor)
  have hwiB : wi.val ≤ 4 := by
    rw [hwiVal]; split
    · omega
    · exact integWeight_le (integA tmeta.output_integ)
  obtain ⟨wt, hwtEq, hwtVal⟩ := spec_imp_exists
    (U8.add_spec (x := wc) (y := wi) (by scalar_tac))
  have hCWval : wt.val = crossingWeightC st agent tmeta := by
    rw [hwtVal, hwcVal, hwiVal, crossingWeightC]
    congr 1
    · by_cases h : vmsMemLast st.taint_levels agent tmeta.conf_floor
      · rw [if_pos (hbtIff.mpr h), if_pos h]
      · rw [if_neg (fun hc => h (hbtIff.mp hc)), if_neg h]
    · by_cases h : vmsMemLast st.integ_levels agent tmeta.output_integ
      · rw [if_pos (hbiIff.mpr h), if_pos h]
      · rw [if_neg (fun hc => h (hbiIff.mp hc)), if_neg h]
  -- The crossing decision chain collapses to one boolean.
  obtain ⟨bcap, hcapEq, hcapIff⟩ := spec_imp_exists
    (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap agent capability.CapKind.Declassify)
  obtain ⟨baf, hafEq, hafIff⟩ := spec_imp_exists
    (affordable_spec { st with in_flight := vm } agent wt)
  have hbudgetEq : budgetReadC ({ st with in_flight := vm } : state.KernelState).agent_budget agent
      = budgetReadC st.agent_budget agent := rfl
  rw [hbudgetEq] at hafIff
  rw [hcf tool { st with in_flight := vm }] at hok
  simp [hwtEq, hcapEq, hafEq, bind_tc_ok] at hok
  have hCOval : (if tmeta.output_bounded = true then
        (if cfOf tool = true then
          (if bcap = true then
            (if baf = true then
              (if bt = false then (Result.ok true : Result Bool) else Result.ok (!bi))
              else Result.ok false)
            else Result.ok false)
          else Result.ok false)
        else Result.ok false)
      = Result.ok (tmeta.output_bounded && cfOf tool && bcap && baf && (!bt || !bi)) := by
    cases tmeta.output_bounded <;> cases cfOf tool <;> cases bcap <;> cases baf <;> cases bt
      <;> cases bi <;> simp
  rw [hCOval] at hok; simp only [bind_tc_ok] at hok
  have hCOiff : (tmeta.output_bounded && cfOf tool && bcap && baf && (!bt || !bi)) = true ↔
      crossingOkC st agent tmeta (cfOf tool) := by
    unfold crossingOkC
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_assoc]
    apply and_congr_right; intro _
    apply and_congr_right; intro _
    apply and_congr
    · exact hcapIff
    · apply and_congr
      · rw [hafIff]
        constructor
        · intro h; rw [← hCWval]; exact h
        · intro h
          show wt.val ≤ (budgetReadC st.agent_budget agent).val
          rw [hCWval]; exact h
      · apply or_congr
        · rw [← hbtIff]; simp
        · rw [← hbiIff]; simp
  cases hco : (tmeta.output_bounded && cfOf tool && bcap && baf && (!bt || !bi)) with
  | true =>
    simp only [hco, reduceIte] at hok
    obtain ⟨st1, hst1Eq, vmB, hStruct, hBudW, hBudNd⟩ :=
      spec_imp_exists (debitBudget_full { st with in_flight := vm } agent wt hcapBudget)
    rw [hst1Eq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, hEventEq⟩ := hok
    rw [hStruct] at hStateEq
    subst hStateEq
    refine ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, Or.inl ⟨hEventEq.symm, hCOiff.mp hco, rfl, rfl, ?_, ?_⟩⟩
    · intro k v; exact hvmMem k v
    · exact fun h => hvvNd ▸ hvmNd h
    · intro G
      have hbw := hBudW G
      rw [hbw]
      by_cases hG : G = agent
      · rw [if_pos hG, if_pos hG, saturatingSub_val, hCWval]
      · rw [if_neg hG, if_neg hG]
    · exact fun h => hBudNd h
  | false =>
    simp only [hco, Bool.false_eq_true, reduceIte] at hok
    obtain ⟨vm1, hvm1Eq, hvm1Mem⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.taint_levels agent tmeta.conf_floor
        hcapTaintE hcapTaintS)
    obtain ⟨vm1Nd, hvm1NdEq, hvm1Nd⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.taint_levels agent tmeta.conf_floor
        hcapTaintE hcapTaintS)
    have hvv1 : vm1Nd = vm1 := Result.ok.inj (hvm1NdEq.symm.trans hvm1Eq)
    rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        integLevel_eq_spec integLevel_clone_spec st.integ_levels agent tmeta.output_integ
        hcapIntegE hcapIntegS)
    obtain ⟨vm2Nd, hvm2NdEq, hvm2Nd⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
        integLevel_eq_spec integLevel_clone_spec st.integ_levels agent tmeta.output_integ
        hcapIntegE hcapIntegS)
    have hvv2 : vm2Nd = vm2 := Result.ok.inj (hvm2NdEq.symm.trans hvm2Eq)
    rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, hEventEq⟩ := hok
    subst hStateEq
    have hNotCo : ¬ crossingOkC st agent tmeta (cfOf tool) := by
      intro hce; have h := hCOiff.mpr hce; rw [hco] at h; exact absurd h (by decide)
    refine ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, Or.inr ⟨hEventEq.symm, hNotCo, rfl, ?_, ?_, ?_, ?_⟩⟩
    · intro k v; exact hvmMem k v
    · exact fun h => hvvNd ▸ hvmNd h
    · intro ag L'; exact hvm1Mem ag L'
    · exact fun h => hvv1 ▸ hvm1Nd h
    · intro ag L'; exact hvm2Mem ag L'
    · exact fun h => hvv2 ▸ hvm2Nd h

/-- The concrete crossing guard is the abstract one (given `R` and the tool binding): each of the
    five conjuncts crosses via its `R` view; the weight halves align dimension-by-dimension. -/
theorem crossingOk_abs_iff (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (agent : types.AgentId) (inv : types.InvocationId)
    (tool : types.ToolId) (tmeta : background.ToolMetadata) (cf : Bool)
    (hR : R st bg a)
    (htool : invToolC st inv = some tool) (htmeta : toolMetaC bg tool = some tmeta)
    (hcfA : cf = true ↔ a.invocation_conforms inv) :
    crossingOkC st agent tmeta cf ↔ Tzimtzum.crossing_ok a agent inv := by
  have htoolA : a.invocation_tool inv = tool := hR.invTool inv tool htool
  have hcfloorA : a.tool_conf_floor (a.invocation_tool inv) = confA tmeta.conf_floor := by
    rw [htoolA]; exact hR.toolFloor tool tmeta htmeta
  have hointegA : a.tool_output_integ (a.invocation_tool inv) = integA tmeta.output_integ := by
    rw [htoolA]; exact hR.toolOutputInteg tool tmeta htmeta
  have hConfHelps : Tzimtzum.conf_helps a agent inv ↔
      ¬ vmsMemLast st.taint_levels agent tmeta.conf_floor := by
    rw [Tzimtzum.conf_helps, hcfloorA, hR.taint agent (confA tmeta.conf_floor), confC_confA]
  have hIntegHelps : Tzimtzum.integ_helps a agent inv ↔
      ¬ vmsMemLast st.integ_levels agent tmeta.output_integ := by
    rw [Tzimtzum.integ_helps, hointegA, hR.integ agent (integA tmeta.output_integ), integC_integA]
  have hCW : Tzimtzum.crossing_weight a agent inv = crossingWeightC st agent tmeta := by
    rw [Tzimtzum.crossing_weight, crossingWeightC]
    congr 1
    · rw [hcfloorA]
      by_cases h : vmsMemLast st.taint_levels agent tmeta.conf_floor
      · rw [if_neg (fun hc => (hConfHelps.mp hc) h), if_pos h]
      · rw [if_pos (hConfHelps.mpr h), if_neg h]
    · rw [hointegA]
      by_cases h : vmsMemLast st.integ_levels agent tmeta.output_integ
      · rw [if_neg (fun hc => (hIntegHelps.mp hc) h), if_pos h]
      · rw [if_pos (hIntegHelps.mpr h), if_neg h]
  rw [crossingOkC, Tzimtzum.crossing_ok]
  apply and_congr
  · rw [htoolA]; exact (hR.toolBounded tool tmeta htmeta).symm
  · apply and_congr
    · exact hcfA
    · apply and_congr
      · rw [hR.cap agent a.cap_declassify, hR.cap_declass]
      · apply and_congr
        · rw [Tzimtzum.St.affordable, hCW, hR.budget agent]
        · exact (or_congr hConfHelps.symm hIntegHelps.symm).symm.symm

/-- The endorsed branch of the kernel's `invoke_complete` refines `invoke_complete_endorsed`
    (design §5.4): the event's `endorsed = true` selects the branch. -/
theorem invoke_complete_endorsed_preservesR {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (a : AbsState) (agent : types.AgentId) (inv : types.InvocationId)
    (cfOf : types.ToolId → Bool)
    (hcf : ∀ t s, cfInst.conforms conformance agent t inv s bg = .ok (cfOf t))
    (hcfA : ∀ t, cfOf t = true ↔ a.invocation_conforms inv)
    (hR : R st bg a)
    (hcapBudget : st.agent_budget.entries.val.length < Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIntegE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIntegS : ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState)
    (hok : transitions.invoke_complete cfInst st bg conformance agent inv
      = .ok (.Ok (st', event.KernelAction.InvokeComplete agent inv true))) :
    ∃ a', (Tzimtzum.invoke_complete_endorsed agent inv).guard a ∧
          (Tzimtzum.invoke_complete_endorsed agent inv).next a a' ∧ R st' bg a' := by
  obtain ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, hInFlightW, hInflNd, hAct, hPar, hCap,
      hInvT, hInvU, hInvE, hToolReg, hAgInstr, hOv, hFlowOv, hBranch⟩ :=
    invoke_complete_inv_full cfInst st bg conformance agent inv cfOf hcf hR.wfInflight hcapBudget
      hcapTaintE hcapTaintS hcapIntegE hcapIntegS st' _ hok
  rcases hBranch with ⟨_, hCo, hTaintEq, hIntegEq, hBudW, hBudNd⟩ |
    ⟨hEvEq, _, _, _, _, _, _⟩
  case inr =>
    -- The event says `endorsed = true`; the unendorsed branch is impossible.
    simp at hEvEq
  have hCoA : Tzimtzum.crossing_ok a agent inv :=
    (crossingOk_abs_iff st bg a agent inv tool tmeta (cfOf tool) hR htool htmeta (hcfA tool)).mp hCo
  have htoolA : a.invocation_tool inv = tool := hR.invTool inv tool htool
  have hCW : Tzimtzum.crossing_weight a agent inv = crossingWeightC st agent tmeta := by
    have hcfloorA : a.tool_conf_floor (a.invocation_tool inv) = confA tmeta.conf_floor := by
      rw [htoolA]; exact hR.toolFloor tool tmeta htmeta
    have hointegA : a.tool_output_integ (a.invocation_tool inv) = integA tmeta.output_integ := by
      rw [htoolA]; exact hR.toolOutputInteg tool tmeta htmeta
    have hConfHelps : Tzimtzum.conf_helps a agent inv ↔
        ¬ vmsMemLast st.taint_levels agent tmeta.conf_floor := by
      rw [Tzimtzum.conf_helps, hcfloorA, hR.taint agent (confA tmeta.conf_floor), confC_confA]
    have hIntegHelps : Tzimtzum.integ_helps a agent inv ↔
        ¬ vmsMemLast st.integ_levels agent tmeta.output_integ := by
      rw [Tzimtzum.integ_helps, hointegA, hR.integ agent (integA tmeta.output_integ), integC_integA]
    rw [Tzimtzum.crossing_weight, crossingWeightC]
    congr 1
    · rw [hcfloorA]
      by_cases h : vmsMemLast st.taint_levels agent tmeta.conf_floor
      · rw [if_neg (fun hc => (hConfHelps.mp hc) h), if_pos h]
      · rw [if_pos (hConfHelps.mpr h), if_neg h]
    · rw [hointegA]
      by_cases h : vmsMemLast st.integ_levels agent tmeta.output_integ
      · rw [if_neg (fun hc => (hIntegHelps.mp hc) h), if_pos h]
      · rw [if_pos (hIntegHelps.mpr h), if_neg h]
  have hWf' : ∀ ag I, vmsMemLast st'.in_flight ag I →
      ∃ t tmeta, invToolC st' I = some t ∧ toolMetaC bg t = some tmeta := by
    intro ag I hI
    have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
    rw [heq]
    exact hR.wfInflight ag I ((hInFlightW ag I).mp hI).1
  refine ⟨{ a with
      in_flight := fun A I => a.in_flight A I ∧ ¬ (A = agent ∧ I = inv),
      agent_budget := fun A =>
        if A = agent then a.agent_budget agent - Tzimtzum.crossing_weight a agent inv
        else a.agent_budget A }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hR.inflight agent inv).mpr hInFlight, (hR.active agent).mpr hActive, hCoA⟩
  · -- next
    simp [Tzimtzum.invoke_complete_endorsed]
    funext G
    by_cases hG : G = agent <;> simp [hG]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov,
      fun x => by rw [hAct]; exact hR.active x,
      fun t => by rw [hToolReg]; exact hR.tool_reg t,
      fun C P => by rw [hPar]; exact hR.parent C P,
      fun N C => by rw [hCap]; exact hR.cap N C,
      fun ag ins => by rw [hAgInstr]; exact hR.instr ag ins,
      fun ag L => by rw [hTaintEq]; exact hR.taint ag L,
      fun ag L => by rw [hIntegEq]; exact hR.integ ag L,
      fun ag I => ?_, fun ag t L => by rw [hOv]; exact hR.override ag t L, fun G => ?_,
      fun I => by rw [hInvU]; exact hR.invUsed I,
      fun I hU E => by rw [hInvE]; exact hR.invEgress I hU E,
      hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor, hR.toolIntegInspectFloor,
      hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor,
      fun A T L => by rw [hFlowOv]; exact hR.flowOverride A T L,
      fun I t hI => ?_,
      by rw [hPar]; exact hR.ndParent, by rw [hCap]; exact hR.ndCap,
      by rw [hAgInstr]; exact hR.ndInstr, by rw [hTaintEq]; exact hR.ndTaint,
      by rw [hIntegEq]; exact hR.ndInteg, hInflNd hR.ndInflight,
      by rw [hOv]; exact hR.ndOverride, by rw [hFlowOv]; exact hR.ndFlowOverride,
      hBudNd hR.ndBudget, hWf'⟩
    · -- in_flight (point-clear)
      show (a.in_flight ag I ∧ ¬ (ag = agent ∧ I = inv)) ↔ vmsMemLast st'.in_flight ag I
      rw [hInFlightW ag I, hR.inflight ag I]
    · -- budget (weighted self-debit; unconditional equation)
      show (if G = agent then a.agent_budget agent - Tzimtzum.crossing_weight a agent inv
          else a.agent_budget G) = (budgetReadC st'.agent_budget G).val
      rw [hBudW G]
      by_cases hG : G = agent
      · rw [if_pos hG, if_pos hG, hR.budget agent, hCW]
      · rw [if_neg hG, if_neg hG, hR.budget G]
    · -- invTool (framed)
      have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
      exact hR.invTool I t (heq ▸ hI)

/-- The unendorsed branch of the kernel's `invoke_complete` refines `invoke_complete_unendorsed`
    (design §5.4): the event's `endorsed = false` selects the branch; both taint dimensions
    degrade, no debit. -/
theorem invoke_complete_unendorsed_preservesR {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (a : AbsState) (agent : types.AgentId) (inv : types.InvocationId)
    (cfOf : types.ToolId → Bool)
    (hcf : ∀ t s, cfInst.conforms conformance agent t inv s bg = .ok (cfOf t))
    (hcfA : ∀ t, cfOf t = true ↔ a.invocation_conforms inv)
    (hR : R st bg a)
    (hcapBudget : st.agent_budget.entries.val.length < Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIntegE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIntegS : ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState)
    (hok : transitions.invoke_complete cfInst st bg conformance agent inv
      = .ok (.Ok (st', event.KernelAction.InvokeComplete agent inv false))) :
    ∃ a', (Tzimtzum.invoke_complete_unendorsed agent inv).guard a ∧
          (Tzimtzum.invoke_complete_unendorsed agent inv).next a a' ∧ R st' bg a' := by
  obtain ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, hInFlightW, hInflNd, hAct, hPar, hCap,
      hInvT, hInvU, hInvE, hToolReg, hAgInstr, hOv, hFlowOv, hBranch⟩ :=
    invoke_complete_inv_full cfInst st bg conformance agent inv cfOf hcf hR.wfInflight hcapBudget
      hcapTaintE hcapTaintS hcapIntegE hcapIntegS st' _ hok
  rcases hBranch with ⟨hEvEq, _, _, _, _, _⟩ |
    ⟨_, hNotCo, hBudEq, hTaintW, hTaintNd, hIntegW, hIntegNd⟩
  case inl =>
    -- The event says `endorsed = false`; the endorsed branch is impossible.
    simp at hEvEq
  have hNotCoA : ¬ Tzimtzum.crossing_ok a agent inv := fun hc =>
    hNotCo ((crossingOk_abs_iff st bg a agent inv tool tmeta (cfOf tool) hR htool htmeta
      (hcfA tool)).mpr hc)
  have htoolA : a.invocation_tool inv = tool := hR.invTool inv tool htool
  have hcfl : a.tool_conf_floor (a.invocation_tool inv) = confA tmeta.conf_floor := by
    rw [htoolA]; exact hR.toolFloor tool tmeta htmeta
  have hointg : a.tool_output_integ (a.invocation_tool inv) = integA tmeta.output_integ := by
    rw [htoolA]; exact hR.toolOutputInteg tool tmeta htmeta
  have hWf' : ∀ ag I, vmsMemLast st'.in_flight ag I →
      ∃ t tmeta, invToolC st' I = some t ∧ toolMetaC bg t = some tmeta := by
    intro ag I hI
    have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
    rw [heq]
    exact hR.wfInflight ag I ((hInFlightW ag I).mp hI).1
  refine ⟨{ a with
      in_flight := fun A I => a.in_flight A I ∧ ¬ (A = agent ∧ I = inv),
      taint_levels := fun A L => a.taint_levels A L ∨
        (A = agent ∧ a.tool_conf_floor (a.invocation_tool inv) = L),
      integ_levels := fun A L => a.integ_levels A L ∨
        (A = agent ∧ L = a.tool_output_integ (a.invocation_tool inv)) }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hR.inflight agent inv).mpr hInFlight, (hR.active agent).mpr hActive, hNotCoA⟩
  · -- next
    simp [Tzimtzum.invoke_complete_unendorsed]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov,
      fun x => by rw [hAct]; exact hR.active x,
      fun t => by rw [hToolReg]; exact hR.tool_reg t,
      fun C P => by rw [hPar]; exact hR.parent C P,
      fun N C => by rw [hCap]; exact hR.cap N C,
      fun ag ins => by rw [hAgInstr]; exact hR.instr ag ins,
      fun ag L => ?_, fun ag L => ?_,
      fun ag I => ?_, fun ag t L => by rw [hOv]; exact hR.override ag t L,
      fun G => by rw [hBudEq]; exact hR.budget G,
      fun I => by rw [hInvU]; exact hR.invUsed I,
      fun I hU E => by rw [hInvE]; exact hR.invEgress I hU E,
      hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor, hR.toolIntegInspectFloor,
      hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor,
      fun A T L => by rw [hFlowOv]; exact hR.flowOverride A T L,
      fun I t hI => ?_,
      by rw [hPar]; exact hR.ndParent, by rw [hCap]; exact hR.ndCap,
      by rw [hAgInstr]; exact hR.ndInstr, hTaintNd hR.ndTaint, hIntegNd hR.ndInteg,
      hInflNd hR.ndInflight, by rw [hOv]; exact hR.ndOverride,
      by rw [hFlowOv]; exact hR.ndFlowOverride,
      by rw [hBudEq]; exact hR.ndBudget, hWf'⟩
    · -- taint (insert the tool's conf floor on agent)
      show (a.taint_levels ag L ∨ (ag = agent ∧ a.tool_conf_floor (a.invocation_tool inv) = L))
        ↔ vmsMemLast st'.taint_levels ag (confC L)
      rw [hTaintW ag (confC L), hR.taint ag L, hcfl]
      apply or_congr_right
      constructor
      · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [← hL, confC_confA]⟩
      · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [← hL, confA_confC]⟩
    · -- integ (insert the tool's output integrity on agent)
      show (a.integ_levels ag L ∨ (ag = agent ∧ L = a.tool_output_integ (a.invocation_tool inv)))
        ↔ vmsMemLast st'.integ_levels ag (integC L)
      rw [hIntegW ag (integC L), hR.integ ag L, hointg]
      apply or_congr_right
      constructor
      · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [hL, integC_integA]⟩
      · rintro ⟨hag, hL⟩; exact ⟨hag, by rw [← hL, integA_integC]⟩
    · -- in_flight (point-clear)
      show (a.in_flight ag I ∧ ¬ (ag = agent ∧ I = inv)) ↔ vmsMemLast st'.in_flight ag I
      rw [hInFlightW ag I, hR.inflight ag I]
    · -- invTool (framed)
      have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
      exact hR.invTool I t (heq ▸ hI)

end ArgusLean.Refinement
