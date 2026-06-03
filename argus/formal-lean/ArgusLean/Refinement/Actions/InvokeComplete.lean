import ArgusLean.Refinement.Actions.SentinelElevateTaint

/-! # Refinement — `invoke_complete`

`invoke_complete agent inv` point-clears `inv` from `agent`'s in-flight set, then on the **endorsed**
path (`output_bounded ∧ conforms ∧ ¬budget_exhausted`) self-debits `agent`'s budget, and on the
**unendorsed** path adds the completed tool's `conf_floor` to `agent`'s `taint_levels`/`gh_taint_invoked`.
No loops: the whole action branches on the single conformance gate.

It refines against `Rcomplete`, whose budget clause is the get-style `budgetReadC` convention (like
`Rret`), whose `in_flight` clause is the last-match `vmsMemLast` view (what `set_contains` reads and
`remove_from` writes), and which carries: the metadata correspondences (`tool_conf_floor`/
`tool_output_bounded` ↔ `ToolMetadata`) plus the well-formedness invariant that every in-flight
invocation is bound to a tool with metadata (maintained by `invoke_start`) — this rules out the kernel's
defensive "no binding"/"no metadata" early-exit paths under the gate. `output_conforms` is the one
opaque oracle (separate totality+agreement hypotheses, like the content gate). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## Extractor residual: `InvocationId.ne`

Same `PartialEq::ne` default-method residual as `agentId_ne_spec`; needed by the `VecSet.remove`
inside `remove_from` (the in-flight point-clear removes an `InvocationId`). -/

/-! ## `set_contains` — last-match characterisation

The existing `vecMapKVecSetSetContains_spec` only gives `b = true → vmsMem` (∃-entry). `set_contains`
actually reads the *live* (last) entry, so it is faithfully the **iff** with `vmsMemLast`. -/

/-! ## `remove_from` — last-match element removal

`remove_from self key elem` removes `elem` from the live (last) `key`-keyed set, framing every other
key. Last-match nested membership (`vmsMemLast`) — the `VecSet.remove` counterpart of `extend_into`'s
`union_with`. The find-last-index loop reuses the `lastMatchInv` machinery. -/

/-! ## State relation `Rcomplete` -/

/-- Oracle-agreement relation for `invoke_complete`. `in_flight` via the last-match `vmsMemLast` view
    (`set_contains` reads / `remove_from` writes it); `taint_levels`/`gh_taint_invoked` via the insert
    `vmsMem` view; `agent_budget` get-style (`budgetReadC`, like `Rret`); `invocation_tool`
    one-directional; the immutable `tool_conf_floor`/`tool_output_bounded` pinned to `ToolMetadata`; and
    the **well-formedness** invariant that every in-flight invocation is bound to a tool with metadata
    (so the kernel's defensive no-binding / no-metadata exits cannot fire under the in-flight gate). -/
def Rcomplete (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ ag I, a.in_flight ag I ↔ vmsMemLast st.in_flight ag I) ∧
  (∀ ag L, a.taint_levels ag L ↔ vmsMem st.taint_levels ag (confC L)) ∧
  (∀ ag L, a.gh_taint_invoked ag L ↔ vmsMem st.gh_taint_invoked ag (confC L)) ∧
  (∀ G L, a.agent_budget G L ↔ budgetReadC st.agent_budget G = budgetC L) ∧
  (∀ I t, invToolC st I = some t → a.invocation_tool I = t) ∧
  (∀ t tmeta, toolMetaC bg t = some tmeta → a.tool_conf_floor t = confA tmeta.conf_floor) ∧
  (∀ t tmeta, toolMetaC bg t = some tmeta → (a.tool_output_bounded t ↔ tmeta.output_bounded = true)) ∧
  (∀ ag I, vmsMemLast st.in_flight ag I →
    ∃ t tmeta, invToolC st I = some t ∧ toolMetaC bg t = some tmeta)

/-- The endorsed (zero-taint) condition: the completed tool's output is bounded, the conformance
    oracle passes, and the agent's budget is not exhausted. -/
def completeEndorsed (st : state.KernelState) (agent : types.AgentId)
    (tmeta : background.ToolMetadata) (cf : Bool) : Prop :=
  tmeta.output_bounded = true ∧ cf = true ∧
    budgetReadC st.agent_budget agent ≠ types.BudgetLevel.Exhausted

/-! ## Inversion -/

/-- Inversion lemma for a successful `invoke_complete` step. Peels the `set_contains` in-flight gate
    and the active gate, the `remove_from` point-clear of `(agent, inv)`, then — ruling out the kernel's
    defensive no-binding / no-metadata exits via `Rcomplete`'s well-formedness invariant (`hWf`) — reads
    the bound tool's metadata and branches on the `zero_taint` conformance gate
    (`completeEndorsed tmeta (cfOf tool)`): the endorsed path debits `agent`'s budget (taint unchanged);
    the unendorsed path inserts the tool's `conf_floor` into `taint_levels`/`gh_taint_invoked` (budget
    unchanged). `conforms` is the opaque oracle (`hcf`, modelled state-independent). -/
theorem invoke_complete_ok_inv {F : Type} (cfInst : traits.ConformanceOracle F)
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
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.invocation_tool = st.invocation_tool ∧
    st'.tool_registered = st.tool_registered ∧ st'.gh_taint_received = st.gh_taint_received ∧
    st'.agent_instruction = st.agent_instruction ∧ st'.override_used = st.override_used ∧
    ((completeEndorsed st agent tmeta (cfOf tool) ∧
        st'.taint_levels = st.taint_levels ∧ st'.gh_taint_invoked = st.gh_taint_invoked ∧
        (∀ G, budgetReadC st'.agent_budget G =
          if G = agent then debitC (budgetReadC st.agent_budget agent)
          else budgetReadC st.agent_budget G))
     ∨ (¬ completeEndorsed st agent tmeta (cfOf tool) ∧
        st'.agent_budget = st.agent_budget ∧
        (∀ ag L', vmsMem st'.taint_levels ag L' ↔
          vmsMem st.taint_levels ag L' ∨ (ag = agent ∧ L' = tmeta.conf_floor)) ∧
        (∀ ag L', vmsMem st'.gh_taint_invoked ag L' ↔
          vmsMem st.gh_taint_invoked ag L' ∨ (ag = agent ∧ L' = tmeta.conf_floor)))) := by
  simp only [transitions.invoke_complete] at hok
  -- Gate 1: `(agent, inv)` is in-flight (last-match `set_contains`).
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
  -- `remove_from` point-clears `(agent, inv)` from `in_flight`.
  obtain ⟨vm, hvmEq, hvmMem⟩ := spec_imp_exists
    (vecMapKVecSetRemoveFrom_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec agentId_clone_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_ne_spec invocationId_clone_spec st.in_flight agent inv)
  rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
  -- The bound tool of `inv` (last-match `invocation_tool`).
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
  -- the tool's metadata is `some tmeta` (well-formedness), so neither defensive exit fires
  obtain ⟨o1, ho1Eq, ho1⟩ := spec_imp_exists (toolMetadata_spec bg tool)
  rw [ho1Eq] at hok; simp only [bind_tc_ok] at hok
  have ho1tmeta : o1 = some tmeta := by rw [ho1]; exact htmeta
  rw [ho1tmeta] at hok
  simp only [bind_tc_ok] at hok
  -- conforms is the opaque oracle; budget_exhausted reads the (frame-unchanged) budget
  obtain ⟨bexh, hbexhEq, hbexhIff⟩ := spec_imp_exists
    (budgetExhausted_spec { st with in_flight := vm } agent)
  rw [hcf tool { st with in_flight := vm }, hbexhEq] at hok
  -- full `simp` collapses the `let (conf_floor, output_bounded) := (..)` tuple-`let` (substituting the
  -- projections) and reduces `decide ¬bexh` to `!bexh`; `simp only`/`dsimp`/`split` do not.
  simp at hok
  -- `budget_exhausted` reads the budget, which the `in_flight` point-clear leaves unchanged.
  have hbudgetEq : budgetReadC ({ st with in_flight := vm } : state.KernelState).agent_budget agent
      = budgetReadC st.agent_budget agent := rfl
  rw [hbudgetEq] at hbexhIff
  have hbf : bexh = false ↔ budgetReadC st.agent_budget agent ≠ types.BudgetLevel.Exhausted := by
    cases bexh <;> simp_all
  -- the `zero_taint` Bool is exactly the `completeEndorsed` decision.
  have hZTval : (if tmeta.output_bounded = true then
        (if cfOf tool = true then (Result.ok (!bexh) : Result Bool) else Result.ok false)
        else Result.ok false) = Result.ok (tmeta.output_bounded && cfOf tool && !bexh) := by
    cases tmeta.output_bounded <;> cases cfOf tool <;> simp
  have hZTiff : (tmeta.output_bounded && cfOf tool && !bexh) = true ↔
      completeEndorsed st agent tmeta (cfOf tool) := by
    unfold completeEndorsed
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', hbf, and_assoc]
  rw [hZTval] at hok; simp only [bind_tc_ok] at hok
  cases hzt0 : tmeta.output_bounded && cfOf tool && !bexh with
  | true =>
    -- endorsed path: debit `agent`'s budget; taint unchanged.
    simp only [hzt0, reduceIte] at hok
    obtain ⟨st1, hst1Eq, hAct, hPar, hCap, hFl, hTaint, hGhRecv, hOv, hGhInv, hAgInstr, hInvT, hToolReg,
        hBud⟩ := spec_imp_exists (debitBudget_spec { st with in_flight := vm } agent hcapBudget)
    rw [hst1Eq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _⟩ := hok
    subst hStateEq
    refine ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, ?_, hAct, hPar, hCap, hInvT, hToolReg,
      hGhRecv, hAgInstr, hOv, Or.inl ⟨hZTiff.mp hzt0, hTaint, hGhInv, ?_⟩⟩
    · intro k v; rw [hFl]; exact hvmMem k v
    · intro G; rw [hBud G]
  | false =>
    -- unendorsed path: insert the tool's `conf_floor` into `taint_levels`/`gh_taint_invoked`.
    simp only [hzt0, Bool.false_eq_true, reduceIte] at hok
    obtain ⟨vm1, hvm1Eq, hvm1Mem⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.taint_levels agent tmeta.conf_floor
        hcapTaintE hcapTaintS)
    rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
        confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent tmeta.conf_floor
        hcapGhE hcapGhS)
    rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _⟩ := hok
    subst hStateEq
    have hNotCe : ¬ completeEndorsed st agent tmeta (cfOf tool) := by
      intro hce; have h := hZTiff.mpr hce; rw [hzt0] at h; exact absurd h (by decide)
    refine ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inr ⟨hNotCe, rfl, hvm1Mem, hvm2Mem⟩⟩
    intro k v; exact hvmMem k v

/-! ## Forward simulation -/

/-- Forward simulation: a successful `invoke_complete` step is matched by the abstract action,
    preserving `Rcomplete`. The witness removes `(agent, inv)` from `in_flight` and, on the unendorsed
    path (`¬ completeEndorsed`), raises `agent`'s taint to the completed tool's `conf_floor`; on the
    endorsed path it debits the per-level budget. The abstract endorsed condition coincides with
    `completeEndorsed` via the metadata correspondences + `hcfA`; the budget debit reuses the
    `return_endorsed` lattice technique. `output_conforms` is the one opaque oracle (`hcf`/`hcfA`). -/
theorem invoke_complete_refines {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (a : AbsState) (agent : types.AgentId) (inv : types.InvocationId)
    (cfOf : types.ToolId → Bool)
    (hcf : ∀ t s, cfInst.conforms conformance agent t s bg = .ok (cfOf t))
    (hcfA : ∀ t, cfOf t = true ↔ a.output_conforms agent t)
    (hR : Rcomplete st bg a)
    (hcapBudget : st.agent_budget.entries.val.length < Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_complete cfInst st bg conformance agent inv = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.invoke_complete agent inv).guard a ∧
          (Tzimtzum.invoke_complete agent inv).next a a' ∧ Rcomplete st' bg a' := by
  obtain ⟨hRact, hRinfl, hRtaint, hRgh, hRbudget, hRinvtool, hRcfloor, hRtoolOb, hRwf⟩ := hR
  obtain ⟨hInFlight, hActive, tool, tmeta, htool, htmeta, hInFlightW, hAct, hPar, hCap, hInvT,
      hToolReg, hGhRecv, hAgInstr, hOv, hBranch⟩ :=
    invoke_complete_ok_inv cfInst st bg conformance agent inv cfOf hcf hRwf hcapBudget
      hcapTaintE hcapTaintS hcapGhE hcapGhS st' ev hok
  have htoolA : a.invocation_tool inv = tool := hRinvtool inv tool htool
  have hcfloorA : a.tool_conf_floor tool = confA tmeta.conf_floor := hRcfloor tool tmeta htmeta
  -- the abstract endorsed condition (over `a.invocation_tool inv`) coincides with `completeEndorsed`
  have hCeIff : completeEndorsed st agent tmeta (cfOf tool) ↔
      (a.tool_output_bounded (a.invocation_tool inv) ∧ a.output_conforms agent (a.invocation_tool inv) ∧
        ¬ a.agent_budget agent Tzimtzum.BudgetLevel.bl_exhausted) := by
    rw [htoolA, completeEndorsed]
    constructor
    · rintro ⟨hob, hcf', hbud⟩
      exact ⟨(hRtoolOb tool tmeta htmeta).mpr hob, (hcfA tool).mp hcf',
        fun hab => hbud ((hRbudget agent Tzimtzum.BudgetLevel.bl_exhausted).mp hab)⟩
    · rintro ⟨hob, hcf', hbud⟩
      exact ⟨(hRtoolOb tool tmeta htmeta).mp hob, (hcfA tool).mpr hcf',
        fun hexh => hbud ((hRbudget agent Tzimtzum.BudgetLevel.bl_exhausted).mpr hexh)⟩
  -- the WF invariant transports along the frame (`invocation_tool` unchanged, `in_flight` shrinks)
  have hWf' : ∀ ag I, vmsMemLast st'.in_flight ag I →
      ∃ t tmeta, invToolC st' I = some t ∧ toolMetaC bg t = some tmeta := by
    intro ag I hI
    have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
    rw [heq]
    exact hRwf ag I ((hInFlightW ag I).mp hI).1
  refine ⟨{ a with
    in_flight := fun A I => a.in_flight A I ∧ ¬ (A = agent ∧ I = inv),
    taint_levels := fun A L => a.taint_levels A L ∨
      (A = agent ∧ ¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
          a.output_conforms agent (a.invocation_tool inv) ∧
          ¬ a.agent_budget agent Tzimtzum.BudgetLevel.bl_exhausted) ∧
        a.tool_conf_floor (a.invocation_tool inv) = L),
    gh_taint_invoked := fun A L => a.gh_taint_invoked A L ∨
      (A = agent ∧ ¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
          a.output_conforms agent (a.invocation_tool inv) ∧
          ¬ a.agent_budget agent Tzimtzum.BudgetLevel.bl_exhausted) ∧
        a.tool_conf_floor (a.invocation_tool inv) = L),
    agent_budget := fun A L =>
      (A = agent ∧
        (((a.tool_output_bounded (a.invocation_tool inv) ∧
            a.output_conforms agent (a.invocation_tool inv) ∧
            ¬ a.agent_budget agent Tzimtzum.BudgetLevel.bl_exhausted) ∧
          ((a.agent_budget agent Tzimtzum.BudgetLevel.bl5 ∧ L = Tzimtzum.BudgetLevel.bl4)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl4 ∧ L = Tzimtzum.BudgetLevel.bl3)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl3 ∧ L = Tzimtzum.BudgetLevel.bl2)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl2 ∧ L = Tzimtzum.BudgetLevel.bl1)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl1 ∧ L = Tzimtzum.BudgetLevel.bl_exhausted)))
          ∨ (¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
              a.output_conforms agent (a.invocation_tool inv) ∧
              ¬ a.agent_budget agent Tzimtzum.BudgetLevel.bl_exhausted) ∧ a.agent_budget agent L)))
      ∨ (A ≠ agent ∧ a.agent_budget A L) }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hRinfl agent inv).mpr hInFlight, (hRact agent).mpr hActive⟩
  · -- next
    simp [Tzimtzum.invoke_complete]
  · -- Rcomplete st' bg a'
    rcases hBranch with ⟨hCe, hTaintEq, hGhEq, hBudW⟩ | ⟨hNotCe, hBudEq, hTaintW, hGhW⟩
    · -- endorsed path
      have hAbs := hCeIff.mp hCe
      have hne : budgetReadC st.agent_budget agent ≠ types.BudgetLevel.Exhausted :=
        fun h => hAbs.2.2 ((hRbudget agent Tzimtzum.BudgetLevel.bl_exhausted).mpr h)
      -- the budget debit chain coincides with `debitC` (valid because `agent` is not exhausted)
      have hChain : ∀ L,
          ((a.agent_budget agent Tzimtzum.BudgetLevel.bl5 ∧ L = Tzimtzum.BudgetLevel.bl4)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl4 ∧ L = Tzimtzum.BudgetLevel.bl3)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl3 ∧ L = Tzimtzum.BudgetLevel.bl2)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl2 ∧ L = Tzimtzum.BudgetLevel.bl1)
            ∨ (a.agent_budget agent Tzimtzum.BudgetLevel.bl1 ∧ L = Tzimtzum.BudgetLevel.bl_exhausted))
          ↔ debitC (budgetReadC st.agent_budget agent) = budgetC L := by
        intro L
        rw [hRbudget agent Tzimtzum.BudgetLevel.bl5, hRbudget agent Tzimtzum.BudgetLevel.bl4,
          hRbudget agent Tzimtzum.BudgetLevel.bl3, hRbudget agent Tzimtzum.BudgetLevel.bl2,
          hRbudget agent Tzimtzum.BudgetLevel.bl1]
        cases hcur : budgetReadC st.agent_budget agent <;> cases L <;> simp_all [debitC, budgetC]
      refine ⟨fun x => by rw [hAct]; exact hRact x, fun ag I => ?_, fun ag L => ?_, fun ag L => ?_,
        fun G L => ?_, fun I t hI => ?_, hRcfloor, hRtoolOb, hWf'⟩
      · show (a.in_flight ag I ∧ ¬ (ag = agent ∧ I = inv)) ↔ vmsMemLast st'.in_flight ag I
        rw [hInFlightW ag I, hRinfl ag I]
      · show (a.taint_levels ag L ∨ (ag = agent ∧ ¬ _ ∧ _)) ↔ vmsMem st'.taint_levels ag (confC L)
        rw [hTaintEq, hRtaint ag L]
        exact ⟨fun h => h.resolve_right (fun ⟨_, hn, _⟩ => hn hAbs), Or.inl⟩
      · show (a.gh_taint_invoked ag L ∨ (ag = agent ∧ ¬ _ ∧ _)) ↔ vmsMem st'.gh_taint_invoked ag (confC L)
        rw [hGhEq, hRgh ag L]
        exact ⟨fun h => h.resolve_right (fun ⟨_, hn, _⟩ => hn hAbs), Or.inl⟩
      · -- budget: debit on `agent`, frame elsewhere
        show ((G = agent ∧ ((_ ∧ _) ∨ (¬ _ ∧ a.agent_budget agent L))) ∨ (G ≠ agent ∧ a.agent_budget G L))
          ↔ budgetReadC st'.agent_budget G = budgetC L
        rw [hBudW G]
        by_cases hG : G = agent
        · subst hG
          rw [if_pos rfl]
          constructor
          · rintro (⟨_, ⟨_, hc⟩ | ⟨hn, _⟩⟩ | ⟨hne, _⟩)
            · exact (hChain L).mp hc
            · exact absurd hAbs hn
            · exact absurd rfl hne
          · intro hread; exact Or.inl ⟨rfl, Or.inl ⟨hAbs, (hChain L).mpr hread⟩⟩
        · rw [if_neg hG]
          constructor
          · rintro (⟨hag, _⟩ | ⟨_, hbud⟩)
            · exact absurd hag hG
            · exact (hRbudget G L).mp hbud
          · intro hread; exact Or.inr ⟨hG, (hRbudget G L).mpr hread⟩
      · have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
        exact hRinvtool I t (heq ▸ hI)
    · -- unendorsed path
      have hNotAbs : ¬ (a.tool_output_bounded (a.invocation_tool inv) ∧
          a.output_conforms agent (a.invocation_tool inv) ∧
          ¬ a.agent_budget agent Tzimtzum.BudgetLevel.bl_exhausted) := fun h => hNotCe (hCeIff.mpr h)
      have hcfl : a.tool_conf_floor (a.invocation_tool inv) = confA tmeta.conf_floor := by
        rw [htoolA]; exact hcfloorA
      refine ⟨fun x => by rw [hAct]; exact hRact x, fun ag I => ?_, fun ag L => ?_, fun ag L => ?_,
        fun G L => ?_, fun I t hI => ?_, hRcfloor, hRtoolOb, hWf'⟩
      · show (a.in_flight ag I ∧ ¬ (ag = agent ∧ I = inv)) ↔ vmsMemLast st'.in_flight ag I
        rw [hInFlightW ag I, hRinfl ag I]
      · show (a.taint_levels ag L ∨ (ag = agent ∧ ¬ _ ∧ a.tool_conf_floor (a.invocation_tool inv) = L))
          ↔ vmsMem st'.taint_levels ag (confC L)
        rw [hTaintW ag (confC L), hRtaint ag L, hcfl]
        apply or_congr_right
        constructor
        · rintro ⟨hag, _, hL⟩; exact ⟨hag, by rw [← hL, confC_confA]⟩
        · rintro ⟨hag, hL⟩; exact ⟨hag, hNotAbs, by rw [← hL, confA_confC]⟩
      · show (a.gh_taint_invoked ag L ∨ (ag = agent ∧ ¬ _ ∧ a.tool_conf_floor (a.invocation_tool inv) = L))
          ↔ vmsMem st'.gh_taint_invoked ag (confC L)
        rw [hGhW ag (confC L), hRgh ag L, hcfl]
        apply or_congr_right
        constructor
        · rintro ⟨hag, _, hL⟩; exact ⟨hag, by rw [← hL, confC_confA]⟩
        · rintro ⟨hag, hL⟩; exact ⟨hag, hNotAbs, by rw [← hL, confA_confC]⟩
      · show ((G = agent ∧ ((_ ∧ _) ∨ (¬ _ ∧ a.agent_budget agent L))) ∨ (G ≠ agent ∧ a.agent_budget G L))
          ↔ budgetReadC st'.agent_budget G = budgetC L
        rw [hBudEq]
        constructor
        · rintro (⟨hag, ⟨habs, _⟩ | ⟨_, hb⟩⟩ | ⟨_, hbud⟩)
          · exact absurd habs hNotAbs
          · rw [hag]; exact (hRbudget agent L).mp hb
          · exact (hRbudget G L).mp hbud
        · intro hread
          by_cases hG : G = agent
          · exact Or.inl ⟨hG, Or.inr ⟨hNotAbs, (hRbudget agent L).mpr (hG ▸ hread)⟩⟩
          · exact Or.inr ⟨hG, (hRbudget G L).mpr hread⟩
      · have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
        exact hRinvtool I t (heq ▸ hI)

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id residuals (via
-- `Collections`) plus `invocationId_ne_spec` (the `VecSet.remove` of an `InvocationId` inside
-- `remove_from`, `agentId_ne_spec` class). The conformance oracle is modelled as the opaque,
-- state-independent `hcf` (+ agreement `hcfA`), like the content gate; the metadata/`BudgetLevel` facts
-- are PROVED. No agent is added/removed and the root is never named — no `sorryAx`/`AgentId.root`. The
-- loop-free transition branches on the single `zero_taint` conformance gate (`completeEndorsed`); the
-- defensive no-binding / no-metadata exits are ruled out by `Rcomplete`'s well-formedness invariant.
#print axioms ArgusLean.Refinement.invoke_complete_ok_inv
#print axioms ArgusLean.Refinement.invoke_complete_refines
