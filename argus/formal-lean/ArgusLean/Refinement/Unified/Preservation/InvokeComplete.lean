import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `invoke_complete` preserves the unified `R`

`invoke_complete` (Campaign B) is proved **directly** (not via reuse of a slice `_refines`): its budget
clause is *unguarded* over all agents, strictly stronger than `R`'s active-guarded budget — so
`R → Rslice` does not hold. We re-run the inversion exposing the *last-match* taint/gh views and the
nodup posts (`invoke_complete_inv_full`), construct the abstract successor explicitly (the weighted
self-debit on the endorsed path, the tool's `conf_floor` raise on the unendorsed path), and discharge
the guarded budget from `R.budget`.

The endorsed (zero-taint) condition is now the 4-conjunct `output_bounded ∧ output_conforms ∧
affordable (declass_weight floor) ∧ ¬ already-tainted-at-floor` (Campaign B: swapped `¬ exhausted`
for weighted affordability and added the no-debit-when-already-tainted guard). The `output_conforms`
call is the one opaque oracle (`hcf`); `R.wfInflight` rules out the kernel's defensive no-binding /
no-metadata exits. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- The endorsed (zero-taint) condition: the completed tool's output is bounded, the conformance oracle
    passes, the agent can afford the weighted declassification cost, and the agent is not already tainted
    at the tool's conf floor (re-tainting buys nothing, so it takes the unendorsed branch — no debit). -/
def completeEndorsed (st : state.KernelState) (agent : types.AgentId)
    (tmeta : background.ToolMetadata) (cf : Bool) : Prop :=
  tmeta.output_bounded = true ∧ cf = true ∧
    (Tzimtzum.declass_weight (confA tmeta.conf_floor)) ≤ (budgetReadC st.agent_budget agent).val ∧
    ¬ vmsMemLast st.taint_levels agent tmeta.conf_floor

/-- Comprehensive inversion: the `invoke_complete_ok_inv` frame, but with the taint/gh writes read off
    in the canonical last-match `vmsMemLast` view and every written map's `vmNodupKeys` post exposed
    (`in_flight` remove, the endorsed-path weighted budget debit, the unendorsed-path taint/gh inserts). -/
theorem invoke_complete_inv_full {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (agent : types.AgentId) (inv : types.InvocationId)
    (cfOf : types.ToolId → Bool)
    (hcf : ∀ t s, cfInst.conforms conformance agent t s bg = .ok (cfOf t))
    (hWf : ∀ ag I, vmsMemLast st.in_flight ag I →
      ∃ t tmeta, invToolC st I = some t ∧ toolMetaC bg t = some tmeta)
    (hcapBudget : st.agent_budget.entries.val.length < Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_complete cfInst st bg conformance agent inv = .ok (.Ok (st', ev))) :
    vmsMemLast st.in_flight agent inv ∧
    vsMem st.agent_active agent ∧
    ∃ tool tmeta, invToolC st inv = some tool ∧ toolMetaC bg tool = some tmeta ∧
    (∀ k v, vmsMemLast st'.in_flight k v ↔ vmsMemLast st.in_flight k v ∧ ¬ (k = agent ∧ v = inv)) ∧
    (vmNodupKeys st.in_flight → vmNodupKeys st'.in_flight) ∧
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.invocation_tool = st.invocation_tool ∧
    st'.tool_registered = st.tool_registered ∧ st'.gh_taint_received = st.gh_taint_received ∧
    st'.agent_instruction = st.agent_instruction ∧ st'.override_used = st.override_used ∧
    st'.flow_override = st.flow_override ∧
    ((completeEndorsed st agent tmeta (cfOf tool) ∧
        st'.taint_levels = st.taint_levels ∧ st'.gh_taint_invoked = st.gh_taint_invoked ∧
        (∀ G, (budgetReadC st'.agent_budget G).val =
          if G = agent then
            (budgetReadC st.agent_budget agent).val - Tzimtzum.declass_weight (confA tmeta.conf_floor)
          else (budgetReadC st.agent_budget G).val) ∧
        (vmNodupKeys st.agent_budget → vmNodupKeys st'.agent_budget))
     ∨ (¬ completeEndorsed st agent tmeta (cfOf tool) ∧
        st'.agent_budget = st.agent_budget ∧
        (∀ ag L', vmsMemLast st'.taint_levels ag L' ↔
          vmsMemLast st.taint_levels ag L' ∨ (ag = agent ∧ L' = tmeta.conf_floor)) ∧
        (vmNodupKeys st.taint_levels → vmNodupKeys st'.taint_levels) ∧
        (∀ ag L', vmsMemLast st'.gh_taint_invoked ag L' ↔
          vmsMemLast st.gh_taint_invoked ag L' ∨ (ag = agent ∧ L' = tmeta.conf_floor)) ∧
        (vmNodupKeys st.gh_taint_invoked → vmNodupKeys st'.gh_taint_invoked))) := by
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
  -- The bound tool of `inv`.
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
  -- Bind the declassification weight + the abstract weight value.
  obtain ⟨weight, hwEq, hwVal⟩ := declassWeight_spec (confA tmeta.conf_floor)
  rw [confC_confA] at hwEq
  -- Bind the already-tainted read.
  obtain ⟨bt, hbtEq, hbtIff⟩ := spec_imp_exists
    (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent tmeta.conf_floor)
  -- Affordability of the weighted debit on `{st with in_flight := vm}` (same budget as `st`).
  obtain ⟨baf, hafEq, hafIff⟩ := spec_imp_exists
    (affordable_spec { st with in_flight := vm } agent weight)
  have hbudgetEq : budgetReadC ({ st with in_flight := vm } : state.KernelState).agent_budget agent
      = budgetReadC st.agent_budget agent := rfl
  rw [hbudgetEq] at hafIff
  -- Collapse the tuple-`let (conf_floor, output_bounded)` (full `simp` — the gotcha) and substitute
  -- the conformance/weight/already-tainted/affordability reads.
  -- The tuple-`let (conf_floor, output_bounded)` only collapses under full `simp` (the gotcha); it
  -- also substitutes the conformance/weight/already-tainted/affordability reads.
  rw [hcf tool { st with in_flight := vm }] at hok
  simp only [hwEq, hbtEq, hafEq, bind_tc_ok] at hok
  simp [hwEq, hbtEq, hafEq] at hok
  -- The do-notation `zero_taint` collapses to a single boolean (full `simp`).
  have hZTval : (if tmeta.output_bounded = true then
        (if cfOf tool = true then (if baf then (Result.ok (! bt) : Result Bool) else Result.ok false)
          else Result.ok false) else Result.ok false)
      = Result.ok (tmeta.output_bounded && cfOf tool && baf && ! bt) := by
    cases tmeta.output_bounded <;> cases cfOf tool <;> cases baf <;> simp
  have hZTiff : (tmeta.output_bounded && cfOf tool && baf && ! bt) = true ↔
      completeEndorsed st agent tmeta (cfOf tool) := by
    unfold completeEndorsed
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', and_assoc,
      and_assoc]
    apply and_congr_right; intro _
    apply and_congr_right; intro _
    apply and_congr
    · rw [hafIff]
      constructor
      · intro h; rw [← hwVal]; exact h
      · intro h; have : weight.val ≤ (budgetReadC st.agent_budget agent).val := by rw [hwVal]; exact h
        exact this
    · rw [Bool.eq_false_iff]
      constructor
      · intro h hc; exact h (hbtIff.mpr hc)
      · intro h hc; exact h (hbtIff.mp hc)
  rw [hZTval] at hok; simp only [bind_tc_ok] at hok
  cases hzt0 : tmeta.output_bounded && cfOf tool && baf && ! bt with
  | true =>
    simp only [hzt0, reduceIte] at hok
    obtain ⟨st1, hst1Eq, vmB, hStruct, hBudW, hBudNd⟩ :=
      spec_imp_exists (debitBudget_full { st with in_flight := vm } agent weight hcapBudget)
    rw [hst1Eq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _⟩ := hok
    rw [hStruct] at hStateEq
    subst hStateEq
    refine ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, Or.inl ⟨hZTiff.mp hzt0, rfl, rfl, ?_, ?_⟩⟩
    · intro k v; exact hvmMem k v
    · exact fun h => hvvNd ▸ hvmNd h
    · intro G
      have hbw := hBudW G
      rw [hbudgetEq] at hbw
      rw [hbw]
      by_cases hG : G = agent
      · rw [if_pos hG, if_pos hG, saturatingSub_val, hwVal]
      · rw [if_neg hG, if_neg hG]
    · exact fun h => hBudNd h
  | false =>
    simp only [hzt0, Bool.false_eq_true, reduceIte] at hok
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
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent tmeta.conf_floor
        hcapGhE hcapGhS)
    obtain ⟨vm2Nd, hvm2NdEq, hvm2Nd⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent tmeta.conf_floor
        hcapGhE hcapGhS)
    have hvv2 : vm2Nd = vm2 := Result.ok.inj (hvm2NdEq.symm.trans hvm2Eq)
    rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _⟩ := hok
    subst hStateEq
    have hNotCe : ¬ completeEndorsed st agent tmeta (cfOf tool) := by
      intro hce; have h := hZTiff.mpr hce; rw [hzt0] at h; exact absurd h (by decide)
    refine ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, Or.inr ⟨hNotCe, rfl, ?_, ?_, ?_, ?_⟩⟩
    · intro k v; exact hvmMem k v
    · exact fun h => hvvNd ▸ hvmNd h
    · intro ag L'; exact hvm1Mem ag L'
    · exact fun h => hvv1 ▸ hvm1Nd h
    · intro ag L'; exact hvm2Mem ag L'
    · exact fun h => hvv2 ▸ hvm2Nd h

/-- `invoke_complete` preserves the unified `R`. -/
theorem invoke_complete_preservesR {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (a : AbsState) (agent : types.AgentId) (inv : types.InvocationId)
    (cfOf : types.ToolId → Bool)
    (hcf : ∀ t s, cfInst.conforms conformance agent t s bg = .ok (cfOf t))
    (hcfA : ∀ t, cfOf t = true ↔ a.output_conforms agent t)
    (hR : R st bg a)
    (hcapBudget : st.agent_budget.entries.val.length < Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_complete cfInst st bg conformance agent inv = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.invoke_complete agent inv).guard a ∧
          (Tzimtzum.invoke_complete agent inv).next a a' ∧ R st' bg a' := by
  obtain ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, hInFlightW, hInflNd, hAct, hPar, hCap, hInvT,
      hToolReg, hGhRecv, hAgInstr, hOv, hFlowOv, hBranch⟩ :=
    invoke_complete_inv_full cfInst st bg conformance agent inv cfOf hcf hR.wfInflight hcapBudget
      hcapTaintE hcapTaintS hcapGhE hcapGhS st' ev hok
  have htoolA : a.invocation_tool inv = tool := hR.invTool inv tool htool
  have hcfloorA : a.tool_conf_floor tool = confA tmeta.conf_floor := hR.toolFloor tool tmeta htmeta
  -- The abstract endorsed predicate, the 4-conjunct of the `invoke_complete` action body.
  have hCeIff : completeEndorsed st agent tmeta (cfOf tool) ↔
      (a.tool_output_bounded (a.invocation_tool inv) ∧ a.output_conforms agent (a.invocation_tool inv) ∧
        a.affordable agent (Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv))) ∧
        ¬ a.taint_levels agent (a.tool_conf_floor (a.invocation_tool inv))) := by
    rw [htoolA, hcfloorA, completeEndorsed]
    have hbudA : a.agent_budget agent (budgetReadC st.agent_budget agent).val :=
      (hR.budget agent _ ((hR.active agent).mpr hActive)).mpr rfl
    constructor
    · rintro ⟨hob, hcf', hafford, hnt⟩
      refine ⟨(hR.toolBounded tool tmeta htmeta).mpr hob, (hcfA tool).mp hcf', ?_, ?_⟩
      · exact ⟨(budgetReadC st.agent_budget agent).val, hbudA, hafford⟩
      · intro hc
        have := (hR.taint agent (confA tmeta.conf_floor)).mp hc
        rw [confC_confA] at this; exact hnt this
    · rintro ⟨hob, hcf', ⟨bv, hbv, hle⟩, hnt⟩
      refine ⟨(hR.toolBounded tool tmeta htmeta).mp hob, (hcfA tool).mpr hcf', ?_, ?_⟩
      · -- affordability: the unique budget value is `(budgetReadC …).val`
        have huniq : bv = (budgetReadC st.agent_budget agent).val := by
          have := (hR.budget agent bv ((hR.active agent).mpr hActive)).mp hbv; omega
        omega
      · intro hc
        apply hnt
        have : vmsMemLast st.taint_levels agent (confC (confA tmeta.conf_floor)) := by
          rw [confC_confA]; exact hc
        exact (hR.taint agent (confA tmeta.conf_floor)).mpr this
  -- the WF invariant transports along the frame (`invocation_tool` unchanged, `in_flight` shrinks)
  have hWf' : ∀ ag I, vmsMemLast st'.in_flight ag I →
      ∃ t tmeta, invToolC st' I = some t ∧ toolMetaC bg t = some tmeta := by
    intro ag I hI
    have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
    rw [heq]
    exact hR.wfInflight ag I ((hInFlightW ag I).mp hI).1
  refine ⟨{ a with
    in_flight := fun A I => a.in_flight A I ∧ ¬ (A = agent ∧ I = inv),
    taint_levels := fun A L => a.taint_levels A L ∨
      (A = agent ∧ ¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
          a.output_conforms agent (a.invocation_tool inv) ∧
          a.affordable agent (Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv))) ∧
          ¬ a.taint_levels agent (a.tool_conf_floor (a.invocation_tool inv))) ∧
        a.tool_conf_floor (a.invocation_tool inv) = L),
    gh_taint_invoked := fun A L => a.gh_taint_invoked A L ∨
      (A = agent ∧ ¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
          a.output_conforms agent (a.invocation_tool inv) ∧
          a.affordable agent (Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv))) ∧
          ¬ a.taint_levels agent (a.tool_conf_floor (a.invocation_tool inv))) ∧
        a.tool_conf_floor (a.invocation_tool inv) = L),
    agent_budget := fun A L =>
      (A = agent ∧
        (((a.tool_output_bounded (a.invocation_tool inv) ∧
            a.output_conforms agent (a.invocation_tool inv) ∧
            a.affordable agent (Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv))) ∧
            ¬ a.taint_levels agent (a.tool_conf_floor (a.invocation_tool inv))) ∧
          ∀ b, a.agent_budget agent b →
            L = b - Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv)))
          ∨ (¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
              a.output_conforms agent (a.invocation_tool inv) ∧
              a.affordable agent (Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv))) ∧
              ¬ a.taint_levels agent (a.tool_conf_floor (a.invocation_tool inv))) ∧ a.agent_budget agent L)))
      ∨ (A ≠ agent ∧ a.agent_budget A L) }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hR.inflight agent inv).mpr hInFlight, (hR.active agent).mpr hActive⟩
  · -- next
    simp [Tzimtzum.invoke_complete]
  · -- R st' bg a'
    rcases hBranch with ⟨hCe, hTaintEq, hGhEq, hBudW, hBudNd⟩ | ⟨hNotCe, hBudEq, hTaintW, hTaintNd, hGhW, hGhNd⟩
    · -- endorsed path
      have hAbs := hCeIff.mp hCe
      have hflrA : a.tool_conf_floor (a.invocation_tool inv) = confA tmeta.conf_floor := by
        rw [htoolA]; exact hcfloorA
      have hChain : ∀ L, a.agent_active agent →
          ((∀ b, a.agent_budget agent b →
              L = b - Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv)))
          ↔ (budgetReadC st.agent_budget agent).val
              - (Tzimtzum.declass_weight (confA tmeta.conf_floor)) = L) := by
        intro L hGact
        rw [hflrA]
        have hbudA : a.agent_budget agent (budgetReadC st.agent_budget agent).val :=
          (hR.budget agent _ hGact).mpr rfl
        constructor
        · intro h
          exact (h (budgetReadC st.agent_budget agent).val hbudA).symm
        · intro hread b hab
          have : (budgetReadC st.agent_budget agent).val = b := (hR.budget agent b hGact).mp hab
          omega
      refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, fun x => by rw [hAct]; exact hR.active x,
        fun t => by rw [hToolReg]; exact hR.tool_reg t, fun C P => by rw [hPar]; exact hR.parent C P,
        fun N C => by rw [hCap]; exact hR.cap N C, fun ag ins => by rw [hAgInstr]; exact hR.instr ag ins,
        fun ag L => ?_, fun ag I => ?_, fun ag L => ?_,
        fun ag L => by rw [hGhRecv]; exact hR.ghReceived ag L,
        fun ag t L => by rw [hOv]; exact hR.override ag t L, fun G L => ?_, hR.toolCap, hR.toolEgress,
        hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer, hR.flowAllows,
        hR.flowInspects, fun A T L => by rw [hFlowOv]; exact hR.flowOverride A T L, fun I t hI => ?_, by rw [hPar]; exact hR.ndParent,
        by rw [hCap]; exact hR.ndCap, by rw [hAgInstr]; exact hR.ndInstr,
        by rw [hTaintEq]; exact hR.ndTaint, hInflNd hR.ndInflight,
        by rw [hGhEq]; exact hR.ndGhInvoked,
        by rw [hGhRecv]; exact hR.ndGhReceived, by rw [hOv]; exact hR.ndOverride,
        by rw [hFlowOv]; exact hR.ndFlowOverride,
        hBudNd hR.ndBudget, hWf'⟩
      · -- taint (unchanged on endorsed; the abstract disjunct collapses)
        show (a.taint_levels ag L ∨ (ag = agent ∧ ¬ _ ∧ _)) ↔ vmsMemLast st'.taint_levels ag (confC L)
        rw [hTaintEq, hR.taint ag L]
        exact ⟨fun h => h.resolve_right (fun ⟨_, hn, _⟩ => hn hAbs), Or.inl⟩
      · -- in_flight (removal)
        show (a.in_flight ag I ∧ ¬ (ag = agent ∧ I = inv)) ↔ vmsMemLast st'.in_flight ag I
        rw [hInFlightW ag I, hR.inflight ag I]
      · -- gh_taint_invoked (unchanged)
        show (a.gh_taint_invoked ag L ∨ (ag = agent ∧ ¬ _ ∧ _)) ↔ vmsMemLast st'.gh_taint_invoked ag (confC L)
        rw [hGhEq, hR.ghInvoked ag L]
        exact ⟨fun h => h.resolve_right (fun ⟨_, hn, _⟩ => hn hAbs), Or.inl⟩
      · -- budget (guarded; weighted debit on agent)
        intro hactiveG
        show ((G = agent ∧ ((_ ∧ _) ∨ (¬ _ ∧ a.agent_budget agent L))) ∨ (G ≠ agent ∧ a.agent_budget G L))
          ↔ (budgetReadC st'.agent_budget G).val = L
        rw [hBudW G]
        by_cases hG : G = agent
        · subst G; rw [if_pos rfl]
          constructor
          · rintro (⟨_, ⟨_, hc⟩ | ⟨hn, _⟩⟩ | ⟨hne, _⟩)
            · exact (hChain L hactiveG).mp hc
            · exact absurd hAbs hn
            · exact absurd rfl hne
          · intro hread; exact Or.inl ⟨rfl, Or.inl ⟨hAbs, (hChain L hactiveG).mpr hread⟩⟩
        · rw [if_neg hG]
          have hGact : a.agent_active G := hactiveG
          constructor
          · rintro (⟨hag, _⟩ | ⟨_, hbud⟩)
            · exact absurd hag hG
            · exact (hR.budget G L hGact).mp hbud
          · intro hread; exact Or.inr ⟨hG, (hR.budget G L hGact).mpr hread⟩
      · have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
        exact hR.invTool I t (heq ▸ hI)
    · -- unendorsed path
      have hNotAbs : ¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
          a.output_conforms agent (a.invocation_tool inv) ∧
          a.affordable agent (Tzimtzum.declass_weight (a.tool_conf_floor (a.invocation_tool inv))) ∧
          ¬ a.taint_levels agent (a.tool_conf_floor (a.invocation_tool inv))) := fun h => hNotCe (hCeIff.mpr h)
      have hcfl : a.tool_conf_floor (a.invocation_tool inv) = confA tmeta.conf_floor := by
        rw [htoolA]; exact hcfloorA
      refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, fun x => by rw [hAct]; exact hR.active x,
        fun t => by rw [hToolReg]; exact hR.tool_reg t, fun C P => by rw [hPar]; exact hR.parent C P,
        fun N C => by rw [hCap]; exact hR.cap N C, fun ag ins => by rw [hAgInstr]; exact hR.instr ag ins,
        fun ag L => ?_, fun ag I => ?_, fun ag L => ?_,
        fun ag L => by rw [hGhRecv]; exact hR.ghReceived ag L,
        fun ag t L => by rw [hOv]; exact hR.override ag t L, fun G L => ?_, hR.toolCap, hR.toolEgress,
        hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer, hR.flowAllows,
        hR.flowInspects, fun A T L => by rw [hFlowOv]; exact hR.flowOverride A T L, fun I t hI => ?_, by rw [hPar]; exact hR.ndParent,
        by rw [hCap]; exact hR.ndCap, by rw [hAgInstr]; exact hR.ndInstr, hTaintNd hR.ndTaint,
        hInflNd hR.ndInflight, hGhNd hR.ndGhInvoked, by rw [hGhRecv]; exact hR.ndGhReceived,
        by rw [hOv]; exact hR.ndOverride, by rw [hFlowOv]; exact hR.ndFlowOverride,
        by rw [hBudEq]; exact hR.ndBudget, hWf'⟩
      · -- taint (insert tool's conf_floor on agent)
        show (a.taint_levels ag L ∨ (ag = agent ∧ ¬ _ ∧ a.tool_conf_floor (a.invocation_tool inv) = L))
          ↔ vmsMemLast st'.taint_levels ag (confC L)
        rw [hTaintW ag (confC L), hR.taint ag L, hcfl]
        apply or_congr_right
        constructor
        · rintro ⟨hag, _, hL⟩; exact ⟨hag, by rw [← hL, confC_confA]⟩
        · rintro ⟨hag, hL⟩; exact ⟨hag, hcfl ▸ hNotAbs, by rw [← hL, confA_confC]⟩
      · -- in_flight (removal)
        show (a.in_flight ag I ∧ ¬ (ag = agent ∧ I = inv)) ↔ vmsMemLast st'.in_flight ag I
        rw [hInFlightW ag I, hR.inflight ag I]
      · -- gh_taint_invoked (insert)
        show (a.gh_taint_invoked ag L ∨ (ag = agent ∧ ¬ _ ∧ a.tool_conf_floor (a.invocation_tool inv) = L))
          ↔ vmsMemLast st'.gh_taint_invoked ag (confC L)
        rw [hGhW ag (confC L), hR.ghInvoked ag L, hcfl]
        apply or_congr_right
        constructor
        · rintro ⟨hag, _, hL⟩; exact ⟨hag, by rw [← hL, confC_confA]⟩
        · rintro ⟨hag, hL⟩; exact ⟨hag, hcfl ▸ hNotAbs, by rw [← hL, confA_confC]⟩
      · -- budget (guarded; unchanged)
        intro hactiveG
        show ((G = agent ∧ ((_ ∧ _) ∨ (¬ _ ∧ a.agent_budget agent L))) ∨ (G ≠ agent ∧ a.agent_budget G L))
          ↔ (budgetReadC st'.agent_budget G).val = L
        rw [hBudEq]
        constructor
        · rintro (⟨hag, ⟨habs, _⟩ | ⟨_, hb⟩⟩ | ⟨_, hbud⟩)
          · exact absurd habs hNotAbs
          · rw [hag] at hactiveG ⊢; exact (hR.budget agent L hactiveG).mp hb
          · exact (hR.budget G L hactiveG).mp hbud
        · intro hread
          by_cases hG : G = agent
          · exact Or.inl ⟨hG, Or.inr ⟨hNotAbs, (hR.budget agent L (hG ▸ hactiveG)).mpr (hG ▸ hread)⟩⟩
          · exact Or.inr ⟨hG, (hR.budget G L hactiveG).mpr hread⟩
      · have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
        exact hR.invTool I t (heq ▸ hI)

end ArgusLean.Refinement
