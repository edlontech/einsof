import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `sentinel_elevate_taint` preserves the unified `R`

Proved by **reuse** of `sentinel_elevate_taint_refines`: the slice relation `Rsent` carries no budget
clause, so it projects cleanly from `R` (the taint/gh `vmsMem` views bridge to `R`'s canonical
`vmsMemLast` via `R.ndTaint`/`R.ndGhInvoked`). We then upgrade the slice output `Rsent st' bg a'` to the
unified `R st' bg a'`: the covered fields (active / in_flight / override / egress / flow / invocation)
come straight from `Rsent'`, the taint/gh fields bridge back through the *output* nodup posts
(`sentinel_elevate_taint_inv_full`), and the untouched fields transport via the abstract frames
(`hnext`) + the concrete frames (`_inv_full`) + `R`. The content gate is the one opaque oracle, supplied
as `cgOf`/`hcg`/`hcgA` (extracted from `CgAgree` in the bundle). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP
set_option Aeneas.Deprecated.progressWarning false

set_option maxHeartbeats 4000000

/-! ## The in-flight loop

The per-invocation flow-contribution predicates (`invToolC` / `egItems` / `invMissing` / `invDenied` /
`invConsumed`) and the pure `FlowMode` keystones live in `FlowOracle` (shared with
`return_unendorsed`); this file consumes them. -/

/-- Generalised loop spec for `sentinel_elevate_taint_loop`, relative to a fixed reference
    `(accStart, mbStart)`: after scanning the prefix `[0, fi)` of `invs` the running accumulator's
    `denied`/`to_consume`/`missing_binding` are exactly the reference extended by the per-invocation
    contributions over that prefix; `to_consume` stays `Nodup` and short of `Usize.max`. The per-tool
    oracle values are supplied as `cgOf`/`ovOf`/`ocOf` with their `= .ok` agreement hypotheses (only
    the content gate is opaque; `has_flow_override`/`override_consumed` callers discharge from the
    proven specs). The state args are `st`'s fields (the kernel always calls it that way). -/
theorem sentinelLoop_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf ovOf ocOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hov : ∀ t, state.KernelState.has_flow_override st agent t level = .ok (ovOf t))
    (hoc : ∀ t, state.KernelState.override_consumed st agent t level = .ok (ocOf t))
    (invs : collections.VecSet types.InvocationId)
    (accStart : transitions.GateAccum) (mbStart : Bool)
    (hcapS : accStart.to_consume.items.val.length + invs.items.val.length ≤ Usize.max)
    (acc : transitions.GateAccum) (mb : Bool) (fi : Usize)
    (hfi : fi.val ≤ invs.items.val.length)
    (hnd : acc.to_consume.items.val.Nodup)
    (hlen : acc.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + fi.val)
    (hmb : mb = true ↔ mbStart = true ∨ ∃ inv ∈ invs.items.val.take fi.val, invMissing st inv)
    (hden : acc.denied = true ↔ accStart.denied = true ∨
      ∃ inv ∈ invs.items.val.take fi.val, invDenied st bg level cgOf ovOf ocOf inv)
    (hcon : ∀ k, vsMem acc.to_consume k ↔ vsMem accStart.to_consume k ∨
      ∃ inv ∈ invs.items.val.take fi.val, invConsumed st bg level ovOf ocOf inv k) :
    transitions.sentinel_elevate_taint_loop cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.in_flight st.invocation_tool st.tool_registered st.gh_taint_invoked
      st.gh_taint_received st.agent_instruction st.override_used st.flow_override st.agent_budget
      bg content_gate agent level acc mb invs fi ⦃ res =>
      (res.2 = true ↔ mbStart = true ∨ ∃ inv ∈ invs.items.val, invMissing st inv) ∧
      (res.1.denied = true ↔ accStart.denied = true ∨
        ∃ inv ∈ invs.items.val, invDenied st bg level cgOf ovOf ocOf inv) ∧
      (∀ k, vsMem res.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ inv ∈ invs.items.val, invConsumed st bg level ovOf ocOf inv k) ∧
      res.1.to_consume.items.val.Nodup ∧
      res.1.to_consume.items.val.length ≤
        accStart.to_consume.items.val.length + invs.items.val.length ⦄ := by
  unfold transitions.sentinel_elevate_taint_loop
  apply loop.spec_decr_nat
    (measure := fun p => invs.items.val.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ invs.items.val.length ∧ p.1.to_consume.items.val.Nodup ∧
      p.1.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + p.2.2.val ∧
      (p.2.1 = true ↔ mbStart = true ∨
        ∃ inv ∈ invs.items.val.take p.2.2.val, invMissing st inv) ∧
      (p.1.denied = true ↔ accStart.denied = true ∨
        ∃ inv ∈ invs.items.val.take p.2.2.val, invDenied st bg level cgOf ovOf ocOf inv) ∧
      (∀ k, vsMem p.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ inv ∈ invs.items.val.take p.2.2.val, invConsumed st bg level ovOf ocOf inv k))
  · rintro ⟨accL, mbL, iL⟩ ⟨hile, hndL, hlenL, hmbL, hdenL, hconL⟩
    dsimp only at hile hndL hlenL hmbL hdenL hconL ⊢
    simp only [transitions.sentinel_elevate_taint_loop.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < invs.items.val.length := by scalar_tac
      step as ⟨inv, hinv⟩
      -- prefix-extension lemma for `∃ over take`
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ invs.items.val.take (iL.val + 1), P x) ↔
          (∃ x ∈ invs.items.val.take iL.val, P x) ∨ P inv := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hinv]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨inv, Or.inr hinv, hPi⟩
      have hi2 : ∀ (i2 : Usize), i2.val = iL.val + 1 →
          invs.items.val.take i2.val = invs.items.val.take (iL.val + 1) := fun i2 h2 => by rw [h2]
      -- read the bound tool (last-match `invocation_tool`)
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hoInv : o = invToolC st inv := by rw [ho]; rfl
      cases hocase : o with
      | none =>
        -- missing binding: acc unchanged, mb := true
        rw [hocase] at hoInv
        have hmiss : invMissing st inv := hoInv.symm
        have hndd : ¬ invDenied st bg level cgOf ovOf ocOf inv := not_invDenied_missing hmiss
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, hndL, by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ fi1_post]
          refine iff_of_true ?_ (Or.inr ((hext (invMissing st)).mpr (Or.inr hmiss)))
          trivial
        · rw [hi2 _ fi1_post, hext (invDenied st bg level cgOf ovOf ocOf), hdenL]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC hndd
        · intro k
          have hncc : ¬ invConsumed st bg level ovOf ocOf inv k := not_invConsumed_missing hmiss
          rw [hi2 _ fi1_post, hext (fun i => invConsumed st bg level ovOf ocOf i k), hconL k]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC hncc
      | some tool =>
        rw [hocase] at hoInv
        have hsome : invToolC st inv = some tool := hoInv.symm
        have hnmiss : ¬ invMissing st inv := by rw [invMissing, hsome]; simp
        simp only []
        obtain ⟨tmeta, hmetaEq, hmeta⟩ := spec_imp_exists (toolMetadata_spec bg tool)
        rw [hmetaEq]; simp only [bind_tc_ok]
        have hcapAcc : accL.to_consume.items.val.length < Usize.max := by
          have := hlenL; have := hlt; have := hcapS; omega
        -- the kernel rebuilds the state record from `st`'s fields; it is `st` (structure eta)
        have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels,
            st.in_flight, st.invocation_tool, st.tool_registered, st.gh_taint_invoked,
            st.gh_taint_received, st.agent_instruction, st.override_used, st.flow_override,
            st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
        -- The remaining body, once the egress set `eg` is fixed (`hegItems`). Proven inline per
        -- egress case (no shared WP `have` — restating the loop's `match`-post compiles to a
        -- different matcher than the goal's, so `exact` would fail on defeq).
        have htail : ∀ (eg : collections.VecSet types.EgressKind),
            eg.items.val = egItems bg tool →
            iL.val < invs.items.val.length →
            transitions.gate_egress cgInst bg content_gate agent tool st level eg accL ⦃ acc2 =>
              acc2.to_consume.items.val.Nodup ∧
              acc2.to_consume.items.val.length ≤
                accStart.to_consume.items.val.length + (iL.val + 1) ∧
              (acc2.denied = true ↔ accStart.denied = true ∨
                ∃ inv ∈ invs.items.val.take (iL.val + 1),
                  invDenied st bg level cgOf ovOf ocOf inv) ∧
              (∀ k, vsMem acc2.to_consume k ↔ vsMem accStart.to_consume k ∨
                ∃ inv ∈ invs.items.val.take (iL.val + 1),
                  invConsumed st bg level ovOf ocOf inv k) ⦄ := by
          intro eg hegItems hlt'
          obtain ⟨acc2, hacc2Eq, hDenied, hConsume, hNd2⟩ := spec_imp_exists
            (gateEgress_spec cgInst bg content_gate agent tool st level eg
              (cgOf tool) (ovOf tool) (ocOf tool) (hcg tool) (hov tool) (hoc tool)
              (flowModeC bg level) (flowMode_eq bg level) accL hcapAcc hndL)
          rw [hacc2Eq]; simp only [spec_ok]
          have hInvDen : invDenied st bg level cgOf ovOf ocOf inv ↔
              ∃ E ∈ eg.items.val,
                egressDenied (flowModeC bg level E) (cgOf tool) (ovOf tool) (ocOf tool) := by
            rw [invDenied, hegItems]
            constructor
            · rintro ⟨tool', htool', hE⟩; rw [hsome, Option.some_inj] at htool'; subst htool'; exact hE
            · intro hE; exact ⟨tool, hsome, hE⟩
          have hInvCon : ∀ k, invConsumed st bg level ovOf ocOf inv k ↔
              (k = gateConsumeKey tool level ∧ ∃ E ∈ eg.items.val,
                egressConsumed (flowModeC bg level E) (ovOf tool) (ocOf tool)) := by
            intro k; rw [invConsumed, hegItems]
            constructor
            · rintro ⟨tool', htool', hk, hE⟩
              rw [hsome, Option.some_inj] at htool'; subst htool'; exact ⟨hk, hE⟩
            · rintro ⟨hk, hE⟩; exact ⟨tool, hsome, hk, hE⟩
          refine ⟨hNd2, ?_, ?_, ?_⟩
          · have hsub : acc2.to_consume.items.val ⊆
                accL.to_consume.items.val ++ [gateConsumeKey tool level] := by
              intro x hx
              rcases (hConsume x).mp hx with hxL | ⟨hxk, _⟩
              · exact List.mem_append_left _ hxL
              · exact List.mem_append_right _ (by rw [hxk]; exact List.mem_singleton.mpr rfl)
            have hle := (List.Nodup.subperm hNd2 hsub).length_le
            rw [List.length_append, List.length_singleton] at hle
            omega
          · rw [hDenied, hext (invDenied st bg level cgOf ovOf ocOf), hdenL, hInvDen, or_assoc]
          · intro k
            rw [hConsume k, hext (fun i => invConsumed st bg level ovOf ocOf i k), hconL k,
              hInvCon k, or_assoc]
        -- discharge the egress `match` by cases, feeding the per-case egress set to `htail`
        cases htm : tmeta with
        | none =>
          simp only [collections.VecSet.new, bind_tc_ok]
          rw [hst]
          obtain ⟨acc2, hacc2Eq, hNd2, hlen2, hDen2, hCon2⟩ := spec_imp_exists
            (htail ⟨alloc.vec.Vec.new types.EgressKind⟩ (by simp [egItems, ← hmeta, htm]) hlt)
          rw [hacc2Eq]; simp only [bind_tc_ok]; step*
          exact ⟨by scalar_tac, hNd2,
            by rw [show fi1.val = iL.val + 1 from fi1_post]; exact hlen2,
            by rw [hi2 _ fi1_post, hext (invMissing st), hmbL]
               exact ⟨fun h => h.imp_right Or.inl, fun h => h.elim (fun hs => Or.inl hs)
                 (fun h => h.elim Or.inr (fun hc => absurd hc hnmiss))⟩,
            by rw [hi2 _ fi1_post]; exact hDen2,
            by intro k; rw [hi2 _ fi1_post]; exact hCon2 k, by scalar_tac⟩
        | some m =>
          simp only []
          rw [vecSetClone_spec types.EgressKind.Insts.CoreCloneClone egressKind_clone_spec m.egress]
          simp only [bind_tc_ok]
          rw [hst]
          obtain ⟨acc2, hacc2Eq, hNd2, hlen2, hDen2, hCon2⟩ := spec_imp_exists
            (htail m.egress (by simp [egItems, ← hmeta, htm]) hlt)
          rw [hacc2Eq]; simp only [bind_tc_ok]; step*
          exact ⟨by scalar_tac, hNd2,
            by rw [show fi1.val = iL.val + 1 from fi1_post]; exact hlen2,
            by rw [hi2 _ fi1_post, hext (invMissing st), hmbL]
               exact ⟨fun h => h.imp_right Or.inl, fun h => h.elim (fun hs => Or.inl hs)
                 (fun h => h.elim Or.inr (fun hc => absurd hc hnmiss))⟩,
            by rw [hi2 _ fi1_post]; exact hDen2,
            by intro k; rw [hi2 _ fi1_post]; exact hCon2 k, by scalar_tac⟩
    case isFalse h =>
      have heq' : iL.val = invs.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmbL hdenL hconL ⊢
      exact ⟨hmbL, hdenL, hconL, hndL, hlenL⟩
  · exact ⟨hfi, hnd, hlen, hmb, hden, hcon⟩

/-! ## In-flight set capacity helper

`get_set_or_empty st.in_flight agent` returns `agent`'s live in-flight set (the clone is the identity
for `InvocationId`), so its length is the closed form `inFlightLen` — used to phrase the loop /
`extend_into` capacity bounds in terms of `st` alone. -/

/-- `get_set_or_empty st.in_flight agent` membership is the last-match nested membership and its length
    is `inFlightLen`. The length-aware refinement of `getSetOrEmpty_spec` for `in_flight`. -/
theorem getSetOrEmptyInFlight_spec (st : state.KernelState) (agent : types.AgentId) :
    collections.VecMapKVecSet.get_set_or_empty
      types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
      types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId st.in_flight agent ⦃ invs =>
      (∀ v, vsMem invs v ↔ vmsMemLast st.in_flight agent v) ∧
      invs.items.val.length = inFlightLen st agent ⦄ := by
  unfold collections.VecMapKVecSet.get_set_or_empty inFlightLen
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      (collections.VecSet.Insts.CoreCloneClone types.InvocationId.Insts.CoreCloneClone)
      (vecSetClone_spec types.InvocationId.Insts.CoreCloneClone invocationId_clone_spec)
      st.in_flight agent)
  rw [hoEq]; simp only [bind_tc_ok]
  cases hL : vmLastEntry st.in_flight.entries.val agent with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho
    unfold collections.VecSet.new
    simp only [spec_ok]
    refine ⟨fun v => ?_, by trivial⟩
    simp only [vsMem, List.not_mem_nil, false_iff]
    rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
  | some p =>
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    have hp1 : p.1 = agent := vmLastEntry_fst _ _ _ hL
    have hLk : vmLastEntry st.in_flight.entries.val agent = some (agent, p.2) := by rw [hL, ← hp1]
    simp only [spec_ok]
    refine ⟨fun v => ?_, by trivial⟩
    constructor
    · intro hv; exact ⟨p.2, hLk, hv⟩
    · rintro ⟨vs, hvs, hv⟩
      rw [hLk, Option.some_inj, Prod.mk.injEq] at hvs
      obtain ⟨_, rfl⟩ := hvs; exact hv

/-! ## State relation `Rsent`

The oracle-agreement relation for `sentinel_elevate_taint`. Beyond the mutable fields it touches
(`agent_active` via `vsMem`; `in_flight` via the last-match `vmsMemLast` that `get_set_or_empty`
observes; the written `taint_levels`/`gh_taint_invoked` via the `vmsMem` insert view; `override_used`
via the last-match `vmsMemLast` that `override_consumed` reads and `extend_into` writes), it pins the
immutable flow oracles to their concrete reductions: `tool_egress` to the tool's egress list
(`egItems`), `flow_allows`/`flow_inspects` to the two `flowModeC` branches, `flow_override` to
membership of the override entry, and `invocation_tool` one-directionally (a concrete binding agrees
with the abstract function). `content_gate_passes` is the one opaque oracle — supplied separately. -/
def Rsent (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ ag I, a.in_flight ag I ↔ vmsMemLast st.in_flight ag I) ∧
  (∀ ag L, a.taint_levels ag L ↔ vmsMem st.taint_levels ag (confC L)) ∧
  (∀ ag L, a.gh_taint_invoked ag L ↔ vmsMem st.gh_taint_invoked ag (confC L)) ∧
  (∀ ag t L, a.override_used ag t L ↔
    vmsMemLast st.override_used ag { tool := t, level := confC L }) ∧
  (∀ T E, a.tool_egress T E ↔ E ∈ egItems bg T) ∧
  (∀ L E, a.flow_allows L E ↔ ceilAdmitsC bg.allow_ceiling (confC L) E = true) ∧
  (∀ L E, a.flow_inspects L E ↔ ceilAdmitsC bg.inspect_ceiling (confC L) E = true) ∧
  (∀ A T L, a.flow_override A T L ↔
    vmsMemLast st.flow_override A { tool := T, level := confC L }) ∧
  (∀ I t, invToolC st I = some t → a.invocation_tool I = t)

/-! ## Inversion -/

/-- Inversion lemma for a successful `sentinel_elevate_taint` step. Peels the active gate, runs the
    in-flight loop (`sentinelLoop_spec`), discharges the `missing_binding` / `denied` error gates, and
    reads off the three writes. The content gate is the supplied oracle `cgOf`; `has_flow_override` /
    `override_consumed` are the proven `ovC` / `ocC` reductions. Capacity bounds are phrased over `st`
    via `inFlightLen`. -/
theorem sentinel_elevate_taint_ok_inv {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcapInvs : inFlightLen st agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + inFlightLen st agent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    vsMem st.agent_active agent ∧
    (∀ inv, vmsMemLast st.in_flight agent inv → invToolC st inv ≠ none) ∧
    (∀ inv tool E, vmsMemLast st.in_flight agent inv → invToolC st inv = some tool →
      E ∈ egItems bg tool →
      ¬ egressDenied (flowModeC bg level E) (cgOf tool)
        (ovC st agent level tool) (ocC st agent level tool)) ∧
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.invocation_tool = st.invocation_tool ∧ st'.tool_registered = st.tool_registered ∧
    st'.gh_taint_received = st.gh_taint_received ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧ st'.flow_override = st.flow_override ∧
    (∀ ag L', vmsMem st'.taint_levels ag L' ↔
      vmsMem st.taint_levels ag L' ∨ (ag = agent ∧ L' = level)) ∧
    (∀ ag L', vmsMem st'.gh_taint_invoked ag L' ↔
      vmsMem st.gh_taint_invoked ag L' ∨ (ag = agent ∧ L' = level)) ∧
    (∀ ag key, vmsMemLast st'.override_used ag key ↔ vmsMemLast st.override_used ag key ∨
      (ag = agent ∧ ∃ inv, vmsMemLast st.in_flight agent inv ∧
        invConsumed st bg level (ovC st agent level) (ocC st agent level) inv key)) := by
  simp only [transitions.sentinel_elevate_taint] at hok
  obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  have hActive : vsMem st.agent_active agent := hbIff.mp hb
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨invs, hinvsEq, hinvsMem, hinvsLen⟩ := spec_imp_exists (getSetOrEmptyInFlight_spec st agent)
  rw [hinvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨⟨acc, mb⟩, hloopEq, hMb, hDen, hCon, _hNd, hLen⟩ := spec_imp_exists
    (sentinelLoop_spec cgInst st bg content_gate agent level cgOf (ovC st agent level)
      (ocC st agent level) hcg (fun t => ovC_eq st agent level t)
      (fun t => ocC_eq st agent level t) invs { denied := false, to_consume := vs } false
      (by show vs.items.val.length + invs.items.val.length ≤ Usize.max
          rw [hvsNil, hinvsLen]; simpa using hcapInvs)
      { denied := false, to_consume := vs } false 0#usize
      (by simp) (by show vs.items.val.Nodup; rw [hvsNil]; exact List.nodup_nil)
      (by simp) (by simp) (by simp) (by simp))
  rw [hloopEq] at hok; simp only [bind_tc_ok] at hok
  have hmbF : mb = false := by cases mb with | false => rfl | true => simp at hok
  have hDenF : acc.denied = false := by
    cases hd : acc.denied with | false => rfl | true => simp [hmbF, hd] at hok
  -- full `simp` is required to reduce the pattern-`let (acc, missing_binding) := (acc, false)`;
  -- it also discharges the two error gates and reduces the `clone agent` calls to `agent`.
  simp [hmbF, hDenF] at hok
  -- capacity for `extend_into`
  have hAccLen : acc.to_consume.items.val.length ≤ inFlightLen st agent := by
    have h : acc.to_consume.items.val.length ≤ vs.items.val.length + invs.items.val.length := hLen
    rw [hvsNil, hinvsLen] at h; simpa using h
  -- `is_empty acc.to_consume`
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc.to_consume)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  -- the `override_used` write, uniformly characterised across the `is_empty` branches
  obtain ⟨vm, hvmEq, hvmMem⟩ : ∃ vm,
      (if b1 = true then Result.ok st.override_used
       else collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
         types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
         types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used agent
         acc.to_consume) = Result.ok vm ∧
      (∀ ag key, vmsMemLast vm ag key ↔ vmsMemLast st.override_used ag key ∨
        (ag = agent ∧ vsMem acc.to_consume key)) := by
    cases hb1 : b1 with
    | true =>
      refine ⟨st.override_used, by rw [if_pos rfl], fun ag key => ?_⟩
      have hempty : acc.to_consume.items.val = [] := hb1Iff.mp hb1
      simp only [vsMem, hempty, List.not_mem_nil, and_false, or_false]
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; omega
      obtain ⟨vm', hvm'Eq, hvm'Mem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used agent acc.to_consume
          hcapOvE hcapJ (le_trans hAccLen hcapInvs))
      exact ⟨vm', by rw [if_neg (by decide)]; exact hvm'Eq, hvm'Mem⟩
  rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, hvm1Mem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent level hcapTaintE hcapTaintS)
  rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent level hcapGhE hcapGhS)
  rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  have hNoMiss : ∀ inv, vmsMemLast st.in_flight agent inv → invToolC st inv ≠ none := by
    intro inv hmem hc
    have hmt : mb = true := hMb.mpr (Or.inr ⟨inv, (hinvsMem inv).mpr hmem, hc⟩)
    simp [hmbF] at hmt
  have hNotDenied : ∀ inv tool E, vmsMemLast st.in_flight agent inv → invToolC st inv = some tool →
      E ∈ egItems bg tool →
      ¬ egressDenied (flowModeC bg level E) (cgOf tool)
        (ovC st agent level tool) (ocC st agent level tool) := by
    intro inv tool E hmem htool hE hden'
    have hd : acc.denied = true :=
      hDen.mpr (Or.inr ⟨inv, (hinvsMem inv).mpr hmem, tool, htool, E, hE, hden'⟩)
    simp [hDenF] at hd
  have hAcc : ∀ key, vsMem acc.to_consume key ↔ ∃ inv, vmsMemLast st.in_flight agent inv ∧
      invConsumed st bg level (ovC st agent level) (ocC st agent level) inv key := by
    intro key
    rw [hCon key]
    constructor
    · rintro (h | ⟨inv, hinv, hcons⟩)
      · simp [vsMem, hvsNil] at h
      · exact ⟨inv, (hinvsMem inv).mp hinv, hcons⟩
    · rintro ⟨inv, hmem, hcons⟩
      exact Or.inr ⟨inv, (hinvsMem inv).mpr hmem, hcons⟩
  subst hStateEq
  refine ⟨hActive, hNoMiss, hNotDenied, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hvm1Mem, hvm2Mem, ?_⟩
  intro ag key
  show vmsMemLast vm ag key ↔ vmsMemLast st.override_used ag key ∨
    (ag = agent ∧ ∃ inv, vmsMemLast st.in_flight agent inv ∧
      invConsumed st bg level (ovC st agent level) (ocC st agent level) inv key)
  rw [hvmMem ag key, hAcc key]

/-! ## Forward simulation -/

/-- Forward simulation: a successful `sentinel_elevate_taint` step is matched by the abstract action,
    preserving `Rsent`. The witness raises `agent`'s taint to `confA level`, records the elevation in
    `gh_taint_invoked`, and adds the single-use consumed overrides. The abstract guard is established
    from the concrete `denied = false` via the per-egress `not_egressDenied_disj`; the single-use
    `override_used` correspondence is the `egressConsumed_iff_abstractDenied` collapse, valid under the
    guard. The content gate is the one opaque oracle (`hcg` totality + `hcgA` agreement). -/
theorem sentinel_elevate_taint_refines {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes agent t)
    (hR : Rsent st bg a)
    (hcapInvs : inFlightLen st agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + inFlightLen st agent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_elevate_taint agent (confA level)).guard a ∧
          (Tzimtzum.sentinel_elevate_taint agent (confA level)).next a a' ∧ Rsent st' bg a' := by
  obtain ⟨hRact, hRinfl, hRtaint, hRgh, hRov, hReg, hRallow, hRinsp, hRovr, hRinvtool⟩ := hR
  obtain ⟨hActive, hNoMiss, hNotDenied, hAct, hPar, hCap, hFl, hInvT, hToolReg,
      hGhRecv, hAgInstr, hBudget, hFlowOv, hTaintW, hGhW, hOvW⟩ :=
    sentinel_elevate_taint_ok_inv cgInst st bg content_gate agent level cgOf hcg
      hcapInvs hcapOvE hcapOvJoint hcapTaintE hcapTaintS hcapGhE hcapGhS st' ev hok
  -- the level correspondence and the per-oracle agreement iffs
  have hLevelIff : ∀ L, (confC L = level) ↔ (L = confA level) := by
    intro L; constructor
    · intro h; rw [← h, confA_confC]
    · intro h; rw [h, confC_confA]
  have hovIff : ∀ t, ovC st agent level t = true ↔
      vmsMemLast st.flow_override agent { tool := t, level := level } := by
    intro t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (hasFlowOverride_spec st agent t level)
    rw [ovC_eq st agent level t, Result.ok.injEq] at hb
    rw [hb]; exact hbiff
  have hocIff : ∀ t, ocC st agent level t = true ↔
      vmsMemLast st.override_used agent { tool := t, level := level } := by
    intro t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (overrideConsumed_spec st agent t level)
    rw [ocC_eq st agent level t, Result.ok.injEq] at hb
    rw [hb]; exact hbiff
  -- band tests, in `flowModeC` terms via the mediating iffs. `flow_allows ↔ flowModeC = Allow`
  -- STILL holds; `flow_inspects ↔ flowModeC = Inspect` does NOT (inspect band may overlap allow band) —
  -- only the band membership survives, and we route everything through `hDenForm` (both directions hold).
  have hAllowIff : ∀ E, a.flow_allows (confA level) E ↔ flowModeC bg level E = background.FlowMode.Allow := by
    intro E; rw [hRallow (confA level) E, confC_confA, flowModeC_allow_iff]
  have hInspBand : ∀ E, a.flow_inspects (confA level) E ↔ ceilAdmitsC bg.inspect_ceiling level E = true := by
    intro E; rw [hRinsp (confA level) E, confC_confA]
  -- the abstract-denial form ⇔ the `flowModeC` denial form (both directions, despite the band overlap)
  have hDenForm : ∀ (E : types.EgressKind) (cg : Bool),
      ((flowModeC bg level E ≠ background.FlowMode.Allow ∧
        ¬ (flowModeC bg level E = background.FlowMode.Inspect ∧ cg = true))
      ↔ (¬ a.flow_allows (confA level) E ∧
          ¬ (a.flow_inspects (confA level) E ∧ cg = true))) := by
    intro E cg
    rw [hAllowIff E, hInspBand E]
    constructor
    · rintro ⟨hne, hni⟩
      refine ⟨hne, ?_⟩
      rintro ⟨hib, hcg⟩
      -- inspect band ∧ ¬allow band ⇒ flowModeC = Inspect, contradicting hni
      have hab : ceilAdmitsC bg.allow_ceiling level E = false := by
        by_contra hc
        exact hne ((flowModeC_allow_iff bg level E).mpr (by simp_all))
      exact hni ⟨(flowModeC_inspect_iff bg level E).mpr ⟨hab, hib⟩, hcg⟩
    · rintro ⟨hna, hni⟩
      refine ⟨hna, ?_⟩
      rintro ⟨hi, hcg⟩
      exact hni ⟨((flowModeC_inspect_iff bg level E).mp hi).2, hcg⟩
  -- success ⇒ every in-flight invocation is bound to its abstract tool
  have hbind : ∀ inv, vmsMemLast st.in_flight agent inv →
      invToolC st inv = some (a.invocation_tool inv) := by
    intro inv hmem
    cases hc : invToolC st inv with
    | none => exact absurd hc (hNoMiss inv hmem)
    | some t => rw [hRinvtool inv t hc]
  -- per-tool guard (from the concrete `not denied`), packaged for the matched in-flight tool
  have hguardOf : ∀ inv, vmsMemLast st.in_flight agent inv →
      ∀ E ∈ egItems bg (a.invocation_tool inv),
        ¬ egressDenied (flowModeC bg level E) (cgOf (a.invocation_tool inv))
          (ovC st agent level (a.invocation_tool inv)) (ocC st agent level (a.invocation_tool inv)) := by
    intro inv hmem E hE
    exact hNotDenied inv (a.invocation_tool inv) E hmem (hbind inv hmem) hE
  -- the single-use consume / abstract-denied equivalence, specialised to a matched in-flight tool
  have hConsEquiv : ∀ inv, vmsMemLast st.in_flight agent inv →
      ((∃ E ∈ egItems bg (a.invocation_tool inv),
          egressConsumed (flowModeC bg level E) (ovC st agent level (a.invocation_tool inv))
            (ocC st agent level (a.invocation_tool inv))) ↔
       (a.flow_override agent (a.invocation_tool inv) (confA level) ∧
        ∃ E, a.tool_egress (a.invocation_tool inv) E ∧ ¬ a.flow_allows (confA level) E ∧
          ¬ (a.flow_inspects (confA level) E ∧ a.content_gate_passes agent (a.invocation_tool inv)))) := by
    intro inv hmem
    rw [egressConsumed_iff_abstractDenied (egItems bg (a.invocation_tool inv)) (flowModeC bg level)
      (cgOf (a.invocation_tool inv)) (ovC st agent level (a.invocation_tool inv))
      (ocC st agent level (a.invocation_tool inv)) (hguardOf inv hmem)]
    apply and_congr
    · rw [hovIff (a.invocation_tool inv), hRovr agent (a.invocation_tool inv) (confA level),
        confC_confA]
    · constructor
      · rintro ⟨E, hE, hden⟩
        refine ⟨E, (hReg (a.invocation_tool inv) E).mpr hE, ?_⟩
        have := (hDenForm E (cgOf (a.invocation_tool inv))).mp hden
        rwa [hcgA (a.invocation_tool inv)] at this
      · rintro ⟨E, hEg, hden⟩
        refine ⟨E, (hReg (a.invocation_tool inv) E).mp hEg, ?_⟩
        rw [← hcgA (a.invocation_tool inv)] at hden
        exact (hDenForm E (cgOf (a.invocation_tool inv))).mpr hden
  -- the abstract guard
  have hguard : ∀ I E, a.in_flight agent I ∧ a.tool_egress (a.invocation_tool I) E →
      a.flow_allows (confA level) E
      ∨ (a.flow_inspects (confA level) E ∧ a.content_gate_passes agent (a.invocation_tool I))
      ∨ (a.flow_override agent (a.invocation_tool I) (confA level)
          ∧ ¬ a.override_used agent (a.invocation_tool I) (confA level)) := by
    rintro I E ⟨hIfl, hEg⟩
    have hmem : vmsMemLast st.in_flight agent I := (hRinfl agent I).mp hIfl
    have hEItem : E ∈ egItems bg (a.invocation_tool I) := (hReg (a.invocation_tool I) E).mp hEg
    have hnd := hNotDenied I (a.invocation_tool I) E hmem (hbind I hmem) hEItem
    rcases not_egressDenied_disj (flowModeC bg level E) (cgOf (a.invocation_tool I))
      (ovC st agent level (a.invocation_tool I)) (ocC st agent level (a.invocation_tool I)) hnd
      with hA | ⟨hI, hcgv⟩ | ⟨hovv, hocv⟩
    · exact Or.inl ((hAllowIff E).mpr hA)
    · exact Or.inr (Or.inl ⟨(hInspBand E).mpr ((flowModeC_inspect_iff bg level E).mp hI).2,
        (hcgA (a.invocation_tool I)).mp hcgv⟩)
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hRovr agent (a.invocation_tool I) (confA level), confC_confA]
        exact (hovIff (a.invocation_tool I)).mp hovv
      · rw [hRov agent (a.invocation_tool I) (confA level), confC_confA]
        intro hc
        have := (hocIff (a.invocation_tool I)).mpr hc
        rw [hocv] at this; simp at this
  refine ⟨{ a with
    taint_levels := fun A L => a.taint_levels A L ∨ (A = agent ∧ L = confA level),
    gh_taint_invoked := fun A L => a.gh_taint_invoked A L ∨ (A = agent ∧ L = confA level),
    override_used := fun A T L => a.override_used A T L ∨
      (A = agent ∧ L = confA level ∧ ∃ I, a.in_flight agent I ∧ T = a.invocation_tool I ∧
        a.flow_override agent (a.invocation_tool I) (confA level) ∧
        ∃ E, a.tool_egress (a.invocation_tool I) E ∧ ¬ a.flow_allows (confA level) E ∧
          ¬ (a.flow_inspects (confA level) E ∧ a.content_gate_passes agent (a.invocation_tool I))) },
    ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hRact agent).mpr hActive, hguard⟩
  · -- next
    simp [Tzimtzum.sentinel_elevate_taint]
  · -- Rsent st' bg a'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; rw [hAct]; exact hRact x
    · intro ag I; rw [hFl]; exact hRinfl ag I
    · intro ag L
      show (a.taint_levels ag L ∨ (ag = agent ∧ L = confA level)) ↔
        vmsMem st'.taint_levels ag (confC L)
      rw [hTaintW ag (confC L), hRtaint ag L, hLevelIff L]
    · intro ag L
      show (a.gh_taint_invoked ag L ∨ (ag = agent ∧ L = confA level)) ↔
        vmsMem st'.gh_taint_invoked ag (confC L)
      rw [hGhW ag (confC L), hRgh ag L, hLevelIff L]
    · intro ag t L
      show (a.override_used ag t L ∨ (ag = agent ∧ L = confA level ∧ ∃ I,
          a.in_flight agent I ∧ t = a.invocation_tool I ∧
          a.flow_override agent (a.invocation_tool I) (confA level) ∧
          ∃ E, a.tool_egress (a.invocation_tool I) E ∧ ¬ a.flow_allows (confA level) E ∧
            ¬ (a.flow_inspects (confA level) E ∧ a.content_gate_passes agent (a.invocation_tool I))))
        ↔ vmsMemLast st'.override_used ag { tool := t, level := confC L }
      rw [hOvW ag { tool := t, level := confC L }, hRov ag t L]
      apply or_congr_right
      apply and_congr_right
      intro hag; subst ag
      constructor
      · rintro ⟨hLl, I, hIfl, htI, hovr, hegr⟩
        have hmem : vmsMemLast st.in_flight agent I := (hRinfl agent I).mp hIfl
        refine ⟨I, hmem, a.invocation_tool I, hbind I hmem, ?_, ?_⟩
        · simp only [gateConsumeKey, types.OverrideKey.mk.injEq]
          exact ⟨htI, (hLevelIff L).mpr hLl⟩
        · exact (hConsEquiv I hmem).mpr ⟨hovr, hegr⟩
      · rintro ⟨inv, hmem, tool', htool', hkey, hcons⟩
        rw [hbind inv hmem, Option.some.injEq] at htool'
        subst htool'
        simp only [gateConsumeKey, types.OverrideKey.mk.injEq] at hkey
        obtain ⟨hteq, hlvl⟩ := hkey
        exact ⟨(hLevelIff L).mp hlvl, inv, (hRinfl agent inv).mpr hmem, hteq,
          (hConsEquiv inv hmem).mp hcons⟩
    · exact hReg
    · exact hRallow
    · exact hRinsp
    · intro A T L; rw [hFlowOv]; exact hRovr A T L
    · intro I t hI
      have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
      exact hRinvtool I t (heq ▸ hI)

/-- Re-run of the `sentinel_elevate_taint` inversion exposing the concrete frames (every untouched map
    unchanged) and the `vmNodupKeys` posts for the three written maps (`taint_levels`/`gh_taint_invoked`
    via the inserts, `override_used` via the conditional `extend_into`). -/
theorem sentinel_elevate_taint_inv_full {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcapInvs : inFlightLen st agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + inFlightLen st agent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.invocation_tool = st.invocation_tool ∧ st'.tool_registered = st.tool_registered ∧
    st'.gh_taint_received = st.gh_taint_received ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧ st'.flow_override = st.flow_override ∧
    (vmNodupKeys st.taint_levels → vmNodupKeys st'.taint_levels) ∧
    (vmNodupKeys st.gh_taint_invoked → vmNodupKeys st'.gh_taint_invoked) ∧
    (vmNodupKeys st.override_used → vmNodupKeys st'.override_used) := by
  simp only [transitions.sentinel_elevate_taint] at hok
  obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨invs, hinvsEq, hinvsMem, hinvsLen⟩ := spec_imp_exists (getSetOrEmptyInFlight_spec st agent)
  rw [hinvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨⟨acc, mb⟩, hloopEq, hMb, hDen, hCon, _hNd, hLen⟩ := spec_imp_exists
    (sentinelLoop_spec cgInst st bg content_gate agent level cgOf (ovC st agent level)
      (ocC st agent level) hcg (fun t => ovC_eq st agent level t)
      (fun t => ocC_eq st agent level t) invs { denied := false, to_consume := vs } false
      (by show vs.items.val.length + invs.items.val.length ≤ Usize.max
          rw [hvsNil, hinvsLen]; simpa using hcapInvs)
      { denied := false, to_consume := vs } false 0#usize
      (by simp) (by show vs.items.val.Nodup; rw [hvsNil]; exact List.nodup_nil)
      (by simp) (by simp) (by simp) (by simp))
  rw [hloopEq] at hok; simp only [bind_tc_ok] at hok
  have hmbF : mb = false := by cases mb with | false => rfl | true => simp at hok
  have hDenF : acc.denied = false := by
    cases hd : acc.denied with | false => rfl | true => simp [hmbF, hd] at hok
  simp [hmbF, hDenF] at hok
  have hAccLen : acc.to_consume.items.val.length ≤ inFlightLen st agent := by
    have h : acc.to_consume.items.val.length ≤ vs.items.val.length + invs.items.val.length := hLen
    rw [hvsNil, hinvsLen] at h; simpa using h
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc.to_consume)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmNd⟩ : ∃ vm,
      (if b1 = true then Result.ok st.override_used
       else collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
         types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
         types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used agent
         acc.to_consume) = Result.ok vm ∧
      (vmNodupKeys st.override_used → vmNodupKeys vm) := by
    cases hb1 : b1 with
    | true => exact ⟨st.override_used, by rw [if_pos rfl], id⟩
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; omega
      obtain ⟨vm', hvm'Eq, hvm'Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used agent acc.to_consume
          hcapOvE hcapJ (le_trans hAccLen hcapInvs))
      exact ⟨vm', by rw [if_neg (by decide)]; exact hvm'Eq, hvm'Nd⟩
  rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, _hvm1Mem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent level hcapTaintE hcapTaintS)
  obtain ⟨vm1Nd, hvm1NdEq, hvm1Nd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.taint_levels agent level hcapTaintE hcapTaintS)
  have hvv1 : vm1Nd = vm1 := Result.ok.inj (hvm1NdEq.symm.trans hvm1Eq)
  rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm2, hvm2Eq, _hvm2Mem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent level hcapGhE hcapGhS)
  obtain ⟨vm2Nd, hvm2NdEq, hvm2Nd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec st.gh_taint_invoked agent level hcapGhE hcapGhS)
  have hvv2 : vm2Nd = vm2 := Result.ok.inj (hvm2NdEq.symm.trans hvm2Eq)
  rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => hvv1 ▸ hvm1Nd h,
    fun h => hvv2 ▸ hvm2Nd h, hvmNd⟩

/-- `sentinel_elevate_taint` preserves the unified `R`. -/
theorem sentinel_elevate_taint_preservesR {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes agent t)
    (hR : R st bg a)
    (hcapInvs : inFlightLen st agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + inFlightLen st agent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapGhE : st.gh_taint_invoked.entries.val.length < Usize.max)
    (hcapGhS : ∀ p ∈ st.gh_taint_invoked.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_elevate_taint cgInst st bg content_gate agent level
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_elevate_taint agent (confA level)).guard a ∧
          (Tzimtzum.sentinel_elevate_taint agent (confA level)).next a a' ∧ R st' bg a' := by
  -- project `R → Rsent` (taint/gh `vmsMem` views via the input nodup bridges)
  have hRsent : Rsent st bg a := ⟨hR.active, hR.inflight,
    fun ag L => (hR.taint ag L).trans (vmsMem_iff_vmsMemLast st.taint_levels hR.ndTaint ag (confC L)).symm,
    fun ag L => (hR.ghInvoked ag L).trans
      (vmsMem_iff_vmsMemLast st.gh_taint_invoked hR.ndGhInvoked ag (confC L)).symm,
    hR.override, hR.toolEgress, hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool⟩
  obtain ⟨a', hguard, hnext, hRsent'⟩ :=
    sentinel_elevate_taint_refines cgInst st bg content_gate a agent level cgOf hcg hcgA hRsent
      hcapInvs hcapOvE hcapOvJoint hcapTaintE hcapTaintS hcapGhE hcapGhS st' ev hok
  obtain ⟨hf_act, hf_par, hf_cap, hf_infl, hf_invt, hf_reg, hf_ghrec, hf_instr, hf_bud, hf_flowov,
      hNdTaint, hNdGh, hNdOver⟩ :=
    sentinel_elevate_taint_inv_full cgInst st bg content_gate agent level cgOf hcg hcapInvs hcapOvE
      hcapOvJoint hcapTaintE hcapTaintS hcapGhE hcapGhS st' ev hok
  obtain ⟨hRact', hRinfl', hRtaint', hRgh', hRov', hReg', hAllow', hInsp', hOvr', hInvtool'⟩ := hRsent'
  simp only [Tzimtzum.sentinel_elevate_taint] at hnext
  obtain ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_flowov, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_returnconf, ha_instriss, ha_allowceil, ha_inspceil, ha_au, ha_cg, ha_invtool, ha_root,
      ha_capdecl, ha_caprefresh, ha_capgrantov⟩ := hnext
  refine ⟨a', hguard, ?_, ?_⟩
  · simp only [Tzimtzum.sentinel_elevate_taint]
    exact ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_flowov, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_returnconf, ha_instriss, ha_allowceil, ha_inspceil, ha_au, ha_cg, ha_invtool, ha_root,
      ha_capdecl, ⟨ha_caprefresh, ha_capgrantov⟩⟩
  · refine ⟨by rw [ha_root]; exact hR.root, by rw [ha_capdecl]; exact hR.cap_declass,
      by rw [ha_caprefresh]; exact hR.cap_refresh, by rw [ha_capgrantov]; exact hR.cap_grantov,
      hRact',
      fun t => by rw [ha_reg, hf_reg]; exact hR.tool_reg t,
      fun Cc P => by rw [ha_parent, hf_par]; exact hR.parent Cc P,
      fun N Cc => by rw [ha_cap, hf_cap]; exact hR.cap N Cc,
      fun ag ins => by rw [ha_instr, hf_instr]; exact hR.instr ag ins,
      fun ag L => (hRtaint' ag L).trans
        (vmsMem_iff_vmsMemLast st'.taint_levels (hNdTaint hR.ndTaint) ag (confC L)),
      hRinfl',
      fun ag L => (hRgh' ag L).trans
        (vmsMem_iff_vmsMemLast st'.gh_taint_invoked (hNdGh hR.ndGhInvoked) ag (confC L)),
      fun ag L => by rw [ha_ghrec, hf_ghrec]; exact hR.ghReceived ag L, hRov',
      fun G L hG => by rw [ha_bud, hf_bud]; rw [ha_active] at hG; exact hR.budget G L hG,
      fun t tmeta Cc h => by rw [ha_toolcap]; exact hR.toolCap t tmeta Cc h, hReg',
      fun t tmeta h => by rw [ha_floor]; exact hR.toolFloor t tmeta h,
      fun t tmeta h => by rw [ha_ob]; exact hR.toolBounded t tmeta h,
      fun t tmeta h => by rw [ha_iss]; exact hR.toolIssuer t tmeta h,
      fun i => by rw [ha_trust]; exact hR.trustedIss i,
      fun i issuer h => by rw [ha_instriss]; exact hR.instrIssuer i issuer h, hAllow', hInsp', hOvr',
      hInvtool', by rw [hf_par]; exact hR.ndParent, by rw [hf_cap]; exact hR.ndCap,
      by rw [hf_instr]; exact hR.ndInstr, hNdTaint hR.ndTaint, by rw [hf_infl]; exact hR.ndInflight,
      hNdGh hR.ndGhInvoked, by rw [hf_ghrec]; exact hR.ndGhReceived, hNdOver hR.ndOverride,
      by rw [hf_flowov]; exact hR.ndFlowOverride,
      by rw [hf_bud]; exact hR.ndBudget, fun ag I hmem => ?_⟩
    -- wfInflight: in_flight + invocation_tool unchanged
    have hmem' : vmsMemLast st.in_flight ag I := by rw [← hf_infl]; exact hmem
    obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hmem'
    exact ⟨t, tmeta, by unfold invToolC; rw [hf_invt]; exact ht, htm⟩

end ArgusLean.Refinement
