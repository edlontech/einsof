import ArgusLean.Refinement.Unified.Preservation.Ingest

/-! # Layer 1 — `settle_invocation` preserves the unified `R` (V4)

Settlement either quarantines an ordinary ambiguous result or closes a record and absorbs its
frozen labels. A quarantined record can only be closed with fresh, scope-matching resolution
evidence. Settling a non-permitted record additionally demotes the owner's remaining records.
-/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

deriving instance DecidableEq for types.Outcome

@[simp] theorem outcome_eq_spec (x y : types.Outcome) :
    types.Outcome.Insts.CoreCmpPartialEqOutcome.eq x y = .ok (decide (x = y)) := by
  cases x <;> cases y <;>
    simp [types.Outcome.Insts.CoreCmpPartialEqOutcome.eq, types.Outcome.read_discriminant]

/-- Abstract pending update corresponding to the concrete settle-then-demote sequence. -/
noncomputable def settlePendingAbs (a : AbsState) (inv : types.InvocationId) (outcome : types.Outcome)
    (agent : types.AgentId) (dispo : Tzimtzum.Disposition) :=
  if dispo = .permitted then Tzimtzum.settleAt a.pending inv (outcomeA outcome)
  else Tzimtzum.demoteAllOf (Tzimtzum.settleAt a.pending inv (outcomeA outcome)) agent

/-- The pending relation after the concrete point update, before optional demotion. -/
theorem settle_pending_update_clause (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (inv : types.InvocationId)
    (j : types.PendingInvocation)
    (jA : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.AttestationId types.PolicyDigest)
    (hjA : a.pending inv = some jA) (hj : pendingRel jA j)
    (outcome : types.Outcome)
    (vm : collections.VecMap types.InvocationId types.PendingInvocation)
    (hvmAmb : outcome = .Ambiguous → ∀ I,
      vmLastEntry vm.entries.val I =
        if I = inv then some (inv, { j with quarantined := true })
        else vmLastEntry st.pending.entries.val I)
    (hvmClose : outcome ≠ .Ambiguous →
      vm.entries.val = st.pending.entries.val.filter (removeKept inv)) (I : types.InvocationId) :
    optRel pendingRel (Tzimtzum.settleAt a.pending inv (outcomeA outcome) I)
      ((vmLastEntry vm.entries.val I).map Prod.snd) := by
  cases outcome with
  | Ambiguous =>
      rw [hvmAmb rfl I]
      by_cases hI : I = inv
      · subst I
        simp only [if_pos, Option.map_some, outcomeA]
        rw [Tzimtzum.settleAt_self_quarantined _ _ jA hjA]
        obtain ⟨hag, hsnap, hegr, hadm, hdisp, hauth, hquar⟩ := hj
        exact ⟨hag, hsnap, hegr, hadm, hdisp, hauth, by simp⟩
      · rw [if_neg hI, Tzimtzum.settleAt_other _ _ _ _ hI]
        exact hR.pending I
  | Success =>
      rw [hvmClose (by intro h; cases h), vmLastEntry_filter_removeKept]
      by_cases hI : I = inv
      · subst I; simp [outcomeA, optRel]
      · rw [if_neg hI, Tzimtzum.settleAt_other _ _ _ _ hI]
        exact hR.pending I
  | Failure =>
      rw [hvmClose (by intro h; cases h), vmLastEntry_filter_removeKept]
      by_cases hI : I = inv
      · subst I; simp [outcomeA, optRel]
      · rw [if_neg hI, Tzimtzum.settleAt_other _ _ _ _ hI]
        exact hR.pending I

/-- Optional E18 demotion preserves the point-update pending correspondence. -/
theorem settle_pending_demote_clause (a : AbsState) (inv : types.InvocationId) (outcome : types.Outcome) (agent : types.AgentId)
    (vm : collections.VecMap types.InvocationId types.PendingInvocation)
    (hbase : ∀ I, optRel pendingRel (Tzimtzum.settleAt a.pending inv (outcomeA outcome) I)
      ((vmLastEntry vm.entries.val I).map Prod.snd)) (I : types.InvocationId) :
    optRel pendingRel
      (Tzimtzum.demoteAllOf (Tzimtzum.settleAt a.pending inv (outcomeA outcome)) agent I)
      ((vmLastEntry (vm.entries.val.map (demoteEntry agent)) I).map Prod.snd) := by
  rw [vmLastEntry_map_key _ (demoteEntry agent) (fun _ => rfl) I]
  specialize hbase I
  cases hv : vmLastEntry vm.entries.val I with
  | none =>
      rw [hv] at hbase
      simp only [Option.map_none] at hbase ⊢
      cases ha : Tzimtzum.settleAt a.pending inv (outcomeA outcome) I with
      | none => simp [ha, Tzimtzum.demoteAllOf, optRel]
      | some J => simp [ha, optRel] at hbase
  | some p =>
      rw [hv] at hbase
      simp only [Option.map_some] at hbase ⊢
      cases ha : Tzimtzum.settleAt a.pending inv (outcomeA outcome) I with
      | none => simp [ha, optRel] at hbase
      | some J =>
          rw [ha] at hbase
          obtain ⟨hag, hsnap, hegr, hadm, hdisp, hauth, hquar⟩ := hbase
          simp only [Tzimtzum.demoteAllOf, ha, demoteEntry]
          by_cases hja : J.agent = agent
          · have hpa : p.2.agent = agent := by rw [← hag]; exact hja
            rw [if_pos hja, if_pos hpa]
            exact ⟨hag, hsnap, hegr, hadm, rfl, hauth, hquar⟩
          · have hpa : p.2.agent ≠ agent := by rw [← hag]; exact hja
            rw [if_neg hja, if_neg hpa]
            exact ⟨hag, hsnap, hegr, hadm, hdisp, hauth, hquar⟩

/-- Canonical abstract state produced by the settlement action. -/
noncomputable def settleStateAbs (a : AbsState) (inv : types.InvocationId)
    (outcome : types.Outcome) (agent : types.AgentId) (dispo : Tzimtzum.Disposition)
    (clvl : Tzimtzum.ConfLevel) (ilvl : Tzimtzum.IntegLevel)
    (att : Option (Tzimtzum.ResolutionAttestation types.InvocationId types.AttestationId)) : AbsState :=
  { a with
    pending := settlePendingAbs a inv outcome agent dispo
    taint_levels := fun A L =>
      a.taint_levels A L ∨
        (outcomeA outcome ≠ Tzimtzum.Outcome.ambiguous ∧ A = agent ∧ L = clvl)
    integ_levels := fun A L =>
      a.integ_levels A L ∨
        (outcomeA outcome ≠ Tzimtzum.Outcome.ambiguous ∧ A = agent ∧ L = ilvl)
    consumed_attestations := fun X =>
      a.consumed_attestations X ∨ ∃ r, att = some r ∧ X = r.id }

/-- Reassemble `R` from the four settlement updates and the framed fields. -/
theorem settle_post_R (st st' : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (inv : types.InvocationId) (outcome : types.Outcome)
    (agent : types.AgentId) (dispo : Tzimtzum.Disposition) (clvl : Tzimtzum.ConfLevel)
    (ilvl : Tzimtzum.IntegLevel)
    (attA : Option (Tzimtzum.ResolutionAttestation types.InvocationId types.AttestationId))
    (hpending : ∀ I, optRel pendingRel
      (settlePendingAbs a inv outcome agent dispo I) (pendingC st' I))
    (htaint : ∀ A L,
      (a.taint_levels A L ∨
        (outcomeA outcome ≠ Tzimtzum.Outcome.ambiguous ∧ A = agent ∧ L = clvl)) ↔
      vmsMemLast st'.taint_levels A (confC L))
    (hinteg : ∀ A L,
      (a.integ_levels A L ∨
        (outcomeA outcome ≠ Tzimtzum.Outcome.ambiguous ∧ A = agent ∧ L = ilvl)) ↔
      vmsMemLast st'.integ_levels A (integC L))
    (hatt : ∀ X, (a.consumed_attestations X ∨ ∃ r, attA = some r ∧ X = r.id) ↔
      vsMem st'.consumed_attestations X)
    (hframes : st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
      st'.agent_cap = st.agent_cap ∧ st'.challenges = st.challenges ∧
      st'.consumed_ids = st.consumed_ids ∧ st'.consumed_crossings = st.consumed_crossings ∧
      st'.crossing_grants = st.crossing_grants ∧ st'.tool_registered = st.tool_registered)
    (hndT : vmNodupKeys st'.taint_levels) (hndI : vmNodupKeys st'.integ_levels)
    (hndP : vmNodupKeys st'.pending) :
    R st' bg (settleStateAbs a inv outcome agent dispo clvl ilvl attA) := by
  obtain ⟨hactive, hparent, hcap, hchal, hids, hcross, hgrants, htool⟩ := hframes
  refine
    { root := hR.root, mode := hR.mode
      active := by intro x; rw [hactive]; exact hR.active x
      tool_reg := by intro t; rw [htool]; exact hR.tool_reg t
      parent := by intro C P; rw [hparent]; exact hR.parent C P
      cap := by intro N C; rw [hcap]; exact hR.cap N C
      taint := htaint, integ := hinteg, pending := hpending
      challenges := ?_, grants := ?_
      consumedIds := ?_, consumedAtt := hatt, consumedCross := ?_
      flowAllows := hR.flowAllows, flowInspects := hR.flowInspects
      ndParent := by rw [hparent]; exact hR.ndParent
      ndCap := by rw [hcap]; exact hR.ndCap
      ndTaint := hndT, ndInteg := hndI, ndPending := hndP
      ndChallenges := by rw [hchal]; exact hR.ndChallenges
      ndGrants := by rw [hgrants]; exact hR.ndGrants }
  · intro I; unfold settleStateAbs challengeC; rw [hchal]; exact hR.challenges I
  · intro A D; unfold settleStateAbs crossingGrantC; rw [hgrants]; exact hR.grants A D
  · intro I; unfold settleStateAbs; rw [hids]; exact hR.consumedIds I
  · intro X; unfold settleStateAbs; rw [hcross]; exact hR.consumedCross X

/-- The shared extracted state-update suffix after settlement validation. -/
noncomputable def settleTail (st : state.KernelState) (inv : types.InvocationId)
    (outcome : types.Outcome)
    (att : Option types.ResolutionAttestation) (j : types.PendingInvocation) :
    Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError) := do
  let vm ←
    if outcome = .Ambiguous then do
      let jq ← types.PendingInvocation.Insts.CoreCloneClone.clone j
      let ii ← types.InvocationId.Insts.CoreCloneClone.clone inv
      collections.VecMap.insert types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId
        types.PendingInvocation.Insts.CoreCloneClone st.pending ii { jq with quarantined := true }
    else
      collections.VecMap.remove types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId
        types.PendingInvocation.Insts.CoreCloneClone st.pending inv
  let s1 ←
    if j.disposition ≠ .Permitted then
      state.KernelState.demote_all_of { st with pending := vm } j.agent
    else ok { st with pending := vm }
  let s2 ←
    if outcome ≠ .Ambiguous then do
      let vm1 ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
        types.ConfLevel.Insts.CoreCmpPartialEqConfLevel s1.taint_levels j.agent
        j.policy.output_conf
      let vm2 ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId types.IntegLevel.Insts.CoreCloneClone
        types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel s1.integ_levels j.agent
        j.policy.output_integ
      ok { s1 with taint_levels := vm1, integ_levels := vm2 }
    else ok s1
  match att with
  | none => ok (.Ok (s2, .SettleInvocation inv j.agent j.disposition outcome
      j.policy.output_conf j.policy.output_integ none))
  | some r => do
      let ai ← types.AttestationId.Insts.CoreCloneClone.clone r.id
      let vs ← collections.VecSet.insert types.AttestationId.Insts.CoreCloneClone
        types.AttestationId.Insts.CoreCmpPartialEqAttestationId s2.consumed_attestations ai
      ok (.Ok ({ s2 with consumed_attestations := vs },
        .SettleInvocation inv j.agent j.disposition outcome j.policy.output_conf
          j.policy.output_integ (some ai)))

/-- The ordinary-outcome label and optional-evidence suffix. -/
noncomputable def settleLabelsTail (s : state.KernelState) (inv : types.InvocationId)
    (outcome : types.Outcome) (att : Option types.ResolutionAttestation)
    (j : types.PendingInvocation) :
    Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError) := do
  let vm1 ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
    types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
    types.ConfLevel.Insts.CoreCmpPartialEqConfLevel s.taint_levels j.agent j.policy.output_conf
  let vm2 ← collections.VecMapKVecSet.insert_into types.AgentId.Insts.CoreCloneClone
    types.AgentId.Insts.CoreCmpPartialEqAgentId types.IntegLevel.Insts.CoreCloneClone
    types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel s.integ_levels j.agent
    j.policy.output_integ
  let s2 := { s with taint_levels := vm1, integ_levels := vm2 }
  match att with
  | none => ok (.Ok (s2, .SettleInvocation inv j.agent j.disposition outcome
      j.policy.output_conf j.policy.output_integ none))
  | some r => do
      let ai ← types.AttestationId.Insts.CoreCloneClone.clone r.id
      let vs ← collections.VecSet.insert types.AttestationId.Insts.CoreCloneClone
        types.AttestationId.Insts.CoreCmpPartialEqAttestationId s2.consumed_attestations ai
      ok (.Ok ({ s2 with consumed_attestations := vs },
        .SettleInvocation inv j.agent j.disposition outcome j.policy.output_conf
          j.policy.output_integ (some ai)))

/-- The ordinary settlement suffix transports the two frozen labels and optional evidence. -/
theorem settleLabelsTail_preservesR (st s : state.KernelState)
    (bg : background.BackgroundTheory) (a : AbsState) (hR : R st bg a)
    (inv : types.InvocationId) (outcome : types.Outcome) (hamb : outcome ≠ .Ambiguous)
    (att : Option types.ResolutionAttestation)
    (attA : Option (Tzimtzum.ResolutionAttestation types.InvocationId types.AttestationId))
    (hatt : optRel resolutionAttestationRel attA att) (j : types.PendingInvocation)
    (hpending : ∀ I, optRel pendingRel
      (settlePendingAbs a inv outcome j.agent (dispA j.disposition) I) (pendingC s I))
    (hndP : vmNodupKeys s.pending)
    (hframes : s.agent_active = st.agent_active ∧ s.agent_parent = st.agent_parent ∧
      s.agent_cap = st.agent_cap ∧ s.challenges = st.challenges ∧
      s.consumed_ids = st.consumed_ids ∧ s.consumed_attestations = st.consumed_attestations ∧
      s.consumed_crossings = st.consumed_crossings ∧ s.crossing_grants = st.crossing_grants ∧
      s.tool_registered = st.tool_registered ∧ s.taint_levels = st.taint_levels ∧
      s.integ_levels = st.integ_levels)
    (hcapTE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTS : ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIE : st.integ_levels.entries.val.length < Usize.max)
    (hcapIS : ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapAtt : ∀ r, att = some r → st.consumed_attestations.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : settleLabelsTail s inv outcome att j = .ok (.Ok (st', ev))) :
    R st' bg (settleStateAbs a inv outcome j.agent (dispA j.disposition)
      (confA j.policy.output_conf) (integA j.policy.output_integ) attA) := by
  obtain ⟨hsa, hsp, hsc, hsch, hsids, hsatt, hscross, hsgr, hstool, hst, hsi⟩ := hframes
  unfold settleLabelsTail at hok
  obtain ⟨vm1, hvm1Eq, hvm1⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec s.taint_levels j.agent j.policy.output_conf
      (by rw [hst]; exact hcapTE) (by rw [hst]; exact hcapTS))
  rw [hvm1Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm2, hvm2Eq, hvm2⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_eq_spec integLevel_clone_spec s.integ_levels j.agent j.policy.output_integ
      (by rw [hsi]; exact hcapIE) (by rw [hsi]; exact hcapIS))
  rw [hvm2Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨vm1N, hvm1NEq, hvm1N⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_eq_spec confLevel_clone_spec s.taint_levels j.agent j.policy.output_conf
      (by rw [hst]; exact hcapTE) (by rw [hst]; exact hcapTS))
  obtain ⟨vm2N, hvm2NEq, hvm2N⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_eq_spec integLevel_clone_spec s.integ_levels j.agent j.policy.output_integ
      (by rw [hsi]; exact hcapIE) (by rw [hsi]; exact hcapIS))
  have hndT : vmNodupKeys vm1 := by
    have heq : vm1N = vm1 := Result.ok.inj (hvm1NEq.symm.trans hvm1Eq)
    rw [← heq]
    apply hvm1N
    rw [hst]
    exact hR.ndTaint
  have hndI : vmNodupKeys vm2 := by
    have heq : vm2N = vm2 := Result.ok.inj (hvm2NEq.symm.trans hvm2Eq)
    rw [← heq]
    apply hvm2N
    rw [hsi]
    exact hR.ndInteg
  have htaint : ∀ A L,
      (a.taint_levels A L ∨
        (outcomeA outcome ≠ .ambiguous ∧ A = j.agent ∧ L = confA j.policy.output_conf)) ↔
      vmsMemLast vm1 A (confC L) := by
    intro A L
    have hneA : outcomeA outcome ≠ .ambiguous := by cases outcome <;> simp_all [outcomeA]
    simp [hneA]
    rw [hvm1, hst, ← hR.taint A L]
    constructor
    · rintro (h | ⟨hA, hL⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hA, by rw [hL, confC_confA]⟩
    · rintro (h | ⟨hA, hv⟩)
      · exact Or.inl h
      · refine Or.inr ⟨hA, ?_⟩
        have := congrArg confA hv
        simpa using this
  have hinteg : ∀ A L,
      (a.integ_levels A L ∨
        (outcomeA outcome ≠ .ambiguous ∧ A = j.agent ∧ L = integA j.policy.output_integ)) ↔
      vmsMemLast vm2 A (integC L) := by
    intro A L
    have hneA : outcomeA outcome ≠ .ambiguous := by cases outcome <;> simp_all [outcomeA]
    simp [hneA]
    rw [hvm2, hsi, ← hR.integ A L]
    constructor
    · rintro (h | ⟨hA, hL⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hA, by rw [hL, integC_integA]⟩
    · rintro (h | ⟨hA, hv⟩)
      · exact Or.inl h
      · refine Or.inr ⟨hA, ?_⟩
        have := congrArg integA hv
        simpa using this
  cases hattC : att with
  | none =>
    simp only [hattC, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hst', _⟩ := hok
    subst st'
    cases hattAeq : attA with
    | some rA => simp [hattAeq, hattC, optRel] at hatt
    | none =>
      apply settle_post_R st { s with taint_levels := vm1, integ_levels := vm2 } bg a hR inv
        outcome j.agent (dispA j.disposition) (confA j.policy.output_conf)
        (integA j.policy.output_integ) none
      · exact hpending
      · exact htaint
      · exact hinteg
      · intro X; rw [hsatt]; simpa [optRel] using hR.consumedAtt X
      · exact ⟨hsa, hsp, hsc, hsch, hsids, hscross, hsgr, hstool⟩
      · exact hndT
      · exact hndI
      · exact hndP
  | some r =>
    simp only [hattC, attestationId_clone_spec, bind_tc_ok] at hok
    obtain ⟨vs, hvsEq, hvs⟩ := spec_imp_exists
      (vecSetInsert_spec types.AttestationId.Insts.CoreCloneClone
        types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
        s.consumed_attestations r.id (by rw [hsatt]; exact hcapAtt r hattC))
    rw [hvsEq] at hok
    simp at hok
    obtain ⟨hst', _⟩ := hok
    subst st'
    cases hattAeq : attA with
    | none => simp [hattAeq, hattC, optRel] at hatt
    | some rA =>
      have hr := hatt
      simp only [hattAeq, hattC, optRel] at hr
      let post : state.KernelState :=
        { { s with taint_levels := vm1, integ_levels := vm2 } with consumed_attestations := vs }
      change R post bg (settleStateAbs a inv outcome j.agent (dispA j.disposition)
        (confA j.policy.output_conf) (integA j.policy.output_integ) (some rA))
      refine settle_post_R st post bg a hR inv outcome j.agent (dispA j.disposition)
        (confA j.policy.output_conf) (integA j.policy.output_integ) (some rA) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact hpending
      · exact htaint
      · exact hinteg
      · intro X
        rw [hvs X, hsatt, ← hR.consumedAtt X]
        simp [hr.1]
      · exact ⟨hsa, hsp, hsc, hsch, hsids, hscross, hsgr, hstool⟩
      · exact hndT
      · exact hndI
      · exact hndP

/-- The validated settlement suffix has exactly the abstract settlement post-image. -/
theorem settleTail_preservesR (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (inv : types.InvocationId) (outcome : types.Outcome)
    (att : Option types.ResolutionAttestation)
    (attA : Option (Tzimtzum.ResolutionAttestation types.InvocationId types.AttestationId))
    (hatt : optRel resolutionAttestationRel attA att) (j : types.PendingInvocation)
    (jA : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.AttestationId types.PolicyDigest)
    (hjA : a.pending inv = some jA) (hj : pendingRel jA j)
    (hcapP : outcome = .Ambiguous → st.pending.entries.val.length < Usize.max)
    (hcapTE : outcome ≠ .Ambiguous → st.taint_levels.entries.val.length < Usize.max)
    (hcapTS : outcome ≠ .Ambiguous →
      ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIE : outcome ≠ .Ambiguous → st.integ_levels.entries.val.length < Usize.max)
    (hcapIS : outcome ≠ .Ambiguous →
      ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapAtt : ∀ r, att = some r → st.consumed_attestations.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : settleTail st inv outcome att j = .ok (.Ok (st', ev))) :
    R st' bg (settleStateAbs a inv outcome j.agent (dispA j.disposition)
      (confA j.policy.output_conf) (integA j.policy.output_integ) attA) := by
  unfold settleTail at hok
  by_cases hamb : outcome = .Ambiguous
  · simp only [hamb, pendingInvocation_clone_spec, invocationId_clone_spec, bind_tc_ok,
      reduceIte] at hok
    obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
      (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
        types.PendingInvocation.Insts.CoreCloneClone st.pending inv { j with quarantined := true }
        (hcapP hamb))
    rw [hvmEq] at hok
    simp only [bind_tc_ok] at hok
    obtain ⟨vmN, hvmNEq, hvmN⟩ := spec_imp_exists
      (vecMapInsert_nodup types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
        types.PendingInvocation.Insts.CoreCloneClone st.pending inv { j with quarantined := true }
        (hcapP hamb))
    have hvmNd : vmNodupKeys vm := by
      have heq : vmN = vm := Result.ok.inj (hvmNEq.symm.trans hvmEq)
      rw [← heq]
      exact hvmN hR.ndPending
    by_cases hperm : j.disposition = .Permitted
    · simp [hperm, hamb] at hok
      have hdispA : dispA j.disposition = .permitted := by rw [hperm]; rfl
      cases hattC : att with
      | none =>
        simp only [hattC, Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at hok
        obtain ⟨hst, _⟩ := hok
        subst st'
        cases hattAeq : attA with
        | some rA => simp [hattAeq, hattC, optRel] at hatt
        | none =>
          apply settle_post_R st { st with pending := vm } bg a hR inv outcome j.agent
            (dispA j.disposition) (confA j.policy.output_conf) (integA j.policy.output_integ) none
          · intro I
            rw [settlePendingAbs, hdispA, if_pos rfl]
            exact settle_pending_update_clause st bg a hR inv j jA hjA hj outcome vm
              (fun _ I => hvm I) (fun hn => absurd hamb hn) I
          · intro A L
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.taint A L
          · intro A L
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.integ A L
          · intro X; simpa [optRel] using hR.consumedAtt X
          · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · exact hR.ndTaint
          · exact hR.ndInteg
          · exact hvmNd
      | some r =>
        simp only [hattC, attestationId_clone_spec, bind_tc_ok] at hok
        obtain ⟨vs, hvsEq, hvs⟩ := spec_imp_exists
          (vecSetInsert_spec types.AttestationId.Insts.CoreCloneClone
            types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
            st.consumed_attestations r.id (hcapAtt r hattC))
        rw [hvsEq] at hok
        simp at hok
        obtain ⟨hst, _⟩ := hok
        subst st'
        cases hattAeq : attA with
        | none => simp [hattAeq, hattC, optRel] at hatt
        | some rA =>
          have hr := hatt
          simp only [hattAeq, hattC, optRel] at hr
          let post : state.KernelState :=
            { { st with pending := vm } with consumed_attestations := vs }
          change R post bg (settleStateAbs a inv outcome j.agent (dispA j.disposition)
            (confA j.policy.output_conf) (integA j.policy.output_integ) (some rA))
          refine settle_post_R st post bg a hR inv outcome j.agent (dispA j.disposition)
            (confA j.policy.output_conf) (integA j.policy.output_integ) (some rA)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · intro I
            rw [settlePendingAbs, hdispA, if_pos rfl]
            exact settle_pending_update_clause st bg a hR inv j jA hjA hj outcome vm
              (fun _ I => hvm I) (fun hn => absurd hamb hn) I
          · intro A L
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.taint A L
          · intro A L
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.integ A L
          · intro X
            rw [hvs X, ← hR.consumedAtt X]
            simp [hr.1]
          · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · exact hR.ndTaint
          · exact hR.ndInteg
          · exact hvmNd
    · simp [hperm, hamb] at hok
      obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1ch, hs1ci, hs1ca, hs1cc,
          hs1g, hs1tr, hs1pend⟩ := spec_imp_exists
        (demoteAllOf_spec { st with pending := vm } j.agent hvmNd)
      rw [hs1Eq] at hok
      simp [hamb] at hok
      have hdispA : dispA j.disposition ≠ .permitted := by
        cases hd : j.disposition <;> simp_all [dispA]
      have hpending : ∀ I, optRel pendingRel
          (settlePendingAbs a inv outcome j.agent (dispA j.disposition) I) (pendingC s1 I) := by
        intro I
        rw [settlePendingAbs, if_neg hdispA]
        unfold pendingC
        rw [hs1pend]
        apply settle_pending_demote_clause a inv outcome j.agent vm
        intro K
        exact settle_pending_update_clause st bg a hR inv j jA hjA hj outcome vm
          (fun _ I => hvm I) (fun hn => absurd hamb hn) K
      cases hattC : att with
      | none =>
        simp only [hattC, Result.ok.injEq, core.result.Result.Ok.injEq,
          Prod.mk.injEq] at hok
        obtain ⟨hst, _⟩ := hok
        subst st'
        cases hattAeq : attA with
        | some rA => simp [hattAeq, hattC, optRel] at hatt
        | none =>
          apply settle_post_R st s1 bg a hR inv outcome j.agent (dispA j.disposition)
            (confA j.policy.output_conf) (integA j.policy.output_integ) none hpending
          · intro A L
            rw [hs1t]
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.taint A L
          · intro A L
            rw [hs1i]
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.integ A L
          · intro X; rw [hs1ca]; simpa [optRel] using hR.consumedAtt X
          · exact ⟨hs1a, hs1p, hs1c, hs1ch, hs1ci, hs1cc, hs1g, hs1tr⟩
          · rw [hs1t]; exact hR.ndTaint
          · rw [hs1i]; exact hR.ndInteg
          · unfold vmNodupKeys
            rw [hs1pend, List.map_map]
            have hfe : Prod.fst ∘ demoteEntry j.agent =
                (Prod.fst : types.InvocationId × types.PendingInvocation → types.InvocationId) := by
              funext x
              rfl
            rw [hfe]
            exact hvmNd
      | some r =>
        simp only [hattC, attestationId_clone_spec, bind_tc_ok] at hok
        obtain ⟨vs, hvsEq, hvs⟩ := spec_imp_exists
          (vecSetInsert_spec types.AttestationId.Insts.CoreCloneClone
            types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
            s1.consumed_attestations r.id (by rw [hs1ca]; exact hcapAtt r hattC))
        rw [hvsEq] at hok
        simp at hok
        obtain ⟨hst, _⟩ := hok
        subst st'
        cases hattAeq : attA with
        | none => simp [hattAeq, hattC, optRel] at hatt
        | some rA =>
          have hr := hatt
          simp only [hattAeq, hattC, optRel] at hr
          apply settle_post_R st { s1 with consumed_attestations := vs } bg a hR inv outcome
            j.agent (dispA j.disposition) (confA j.policy.output_conf)
            (integA j.policy.output_integ) (some rA) hpending
          · intro A L
            rw [hs1t]
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.taint A L
          · intro A L
            rw [hs1i]
            simp only [hamb, outcomeA, ne_eq, not_true_eq_false, false_and, or_false]
            exact hR.integ A L
          · intro X
            rw [hvs X, hs1ca, ← hR.consumedAtt X]
            simp [hr.1]
          · exact ⟨hs1a, hs1p, hs1c, hs1ch, hs1ci, hs1cc, hs1g, hs1tr⟩
          · rw [hs1t]; exact hR.ndTaint
          · rw [hs1i]; exact hR.ndInteg
          · unfold vmNodupKeys
            rw [hs1pend, List.map_map]
            have hfe : Prod.fst ∘ demoteEntry j.agent =
                (Prod.fst : types.InvocationId × types.PendingInvocation → types.InvocationId) := by
              funext x
              rfl
            rw [hfe]
            exact hvmNd
  · simp only [hamb, reduceIte] at hok
    obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
      (vecMapRemove_spec types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_ne_spec
        types.PendingInvocation.Insts.CoreCloneClone st.pending inv)
    rw [hvmEq] at hok
    simp only [bind_tc_ok] at hok
    have hvmNd : vmNodupKeys vm := vmNodupKeysFilter hvm hR.ndPending
    by_cases hperm : j.disposition = .Permitted
    · simp [hperm, hamb] at hok
      have hdispA : dispA j.disposition = .permitted := by rw [hperm]; rfl
      have hpending : ∀ I, optRel pendingRel
          (settlePendingAbs a inv outcome j.agent (dispA j.disposition) I)
          (pendingC { st with pending := vm } I) := by
        intro I
        rw [settlePendingAbs, hdispA, if_pos rfl]
        exact settle_pending_update_clause st bg a hR inv j jA hjA hj outcome vm
          (fun ha => absurd ha hamb) (fun _ => hvm) I
      have hok' : settleLabelsTail { st with pending := vm } inv outcome att j =
          .ok (.Ok (st', ev)) := by
        unfold settleLabelsTail
        simpa [hperm] using hok
      exact settleLabelsTail_preservesR st { st with pending := vm } bg a hR inv outcome hamb
        att attA hatt j hpending hvmNd
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (hcapTE hamb) (hcapTS hamb) (hcapIE hamb) (hcapIS hamb) hcapAtt st' ev hok'
    · simp [hperm, hamb] at hok
      obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1ch, hs1ci, hs1ca, hs1cc,
          hs1g, hs1tr, hs1pend⟩ := spec_imp_exists
        (demoteAllOf_spec { st with pending := vm } j.agent hvmNd)
      rw [hs1Eq] at hok
      simp [hamb] at hok
      have hdispA : dispA j.disposition ≠ .permitted := by
        cases hd : j.disposition <;> simp_all [dispA]
      have hpending : ∀ I, optRel pendingRel
          (settlePendingAbs a inv outcome j.agent (dispA j.disposition) I) (pendingC s1 I) := by
        intro I
        rw [settlePendingAbs, if_neg hdispA]
        unfold pendingC
        rw [hs1pend]
        apply settle_pending_demote_clause a inv outcome j.agent vm
        intro K
        exact settle_pending_update_clause st bg a hR inv j jA hjA hj outcome vm
          (fun ha => absurd ha hamb) (fun _ => hvm) K
      have hok' : settleLabelsTail s1 inv outcome att j = .ok (.Ok (st', ev)) := by
        unfold settleLabelsTail
        simpa using hok
      exact settleLabelsTail_preservesR st s1 bg a hR inv outcome hamb att attA hatt j hpending
        (by
          unfold vmNodupKeys
          rw [hs1pend, List.map_map]
          have hfe : Prod.fst ∘ demoteEntry j.agent =
              (Prod.fst : types.InvocationId × types.PendingInvocation → types.InvocationId) := by
            funext x
            rfl
          rw [hfe]
          exact hvmNd)
        ⟨hs1a, hs1p, hs1c, hs1ch, hs1ci, hs1ca, hs1cc, hs1g, hs1tr, hs1t, hs1i⟩
        (hcapTE hamb) (hcapTS hamb) (hcapIE hamb) (hcapIS hamb) hcapAtt st' ev hok'

/-- V4 `settle_invocation` preserves the unified relation. Capacity assumptions are required only
on the extracted branches that execute the corresponding bounded collection write. -/
theorem settle_invocation_preservesR (st : state.KernelState)
    (bg : background.BackgroundTheory) (a : AbsState) (inv : types.InvocationId)
    (outcome : types.Outcome) (att : Option types.ResolutionAttestation)
    (attA : Option (Tzimtzum.ResolutionAttestation types.InvocationId types.AttestationId))
    (hatt : optRel resolutionAttestationRel attA att) (hR : R st bg a)
    (hcapP : outcome = .Ambiguous → st.pending.entries.val.length < Usize.max)
    (hcapTE : outcome ≠ .Ambiguous → st.taint_levels.entries.val.length < Usize.max)
    (hcapTS : outcome ≠ .Ambiguous →
      ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapIE : outcome ≠ .Ambiguous → st.integ_levels.entries.val.length < Usize.max)
    (hcapIS : outcome ≠ .Ambiguous →
      ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
    (hcapAtt : ∀ r, att = some r → st.consumed_attestations.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.settle_invocation st inv outcome att = .ok (.Ok (st', ev))) :
    ∃ (agent : types.AgentId) (dispo : Tzimtzum.Disposition)
      (clvl : Tzimtzum.ConfLevel) (ilvl : Tzimtzum.IntegLevel) (a' : AbsState),
      (Tzimtzum.settle_invocation inv agent dispo (outcomeA outcome) clvl ilvl attA).guard a ∧
      (Tzimtzum.settle_invocation inv agent dispo (outcomeA outcome) clvl ilvl attA).next a a' ∧
      R st' bg a' := by
  simp only [transitions.settle_invocation] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec st.pending inv)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  cases hoO : o with
  | none => simp [hoO] at hok
  | some j =>
    have hjC : pendingC st inv = some j := by
      unfold pendingC
      rw [← ho, hoO]
    have hjR := hR.pending inv
    rw [hjC] at hjR
    cases hjAeq : a.pending inv with
    | none => simp [hjAeq, optRel] at hjR
    | some jA =>
      have hj : pendingRel jA j := by simpa [hjAeq, optRel] using hjR
      obtain ⟨hag, hsnap, hegr, hadm, hdisp, hauth, hquar⟩ := hj
      simp only [hoO, agentId_clone_spec, bind_tc_ok] at hok
      obtain ⟨ba, hbaEq, hba⟩ := spec_imp_exists
        (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active j.agent)
      rw [hbaEq] at hok
      simp only [bind_tc_ok] at hok
      have hbaT : ba = true := by cases ba with | true => rfl | false => simp at hok
      simp only [hbaT, reduceIte, disposition_eq_spec] at hok
      have hblocked : j.disposition ≠ .Blocked := by
        intro hb
        have hb' : decide (j.disposition = types.Disposition.Blocked) = true := by simp [hb]
        simp [hb'] at hok
      simp [hblocked] at hok
      have hdispNot : dispA j.disposition ≠ .blocked := by
        cases hd : j.disposition <;> simp_all [dispA]
      have hactive : a.agent_active j.agent := (hR.active j.agent).mpr (hba.mp hbaT)
      obtain ⟨hsTool, hsCaps, hsClear, hsFloor, hsInspect, hsOutC, hsOutI, hsDecl, hsPD⟩ := hsnap
      have hj' : pendingRel jA j :=
        ⟨hag, ⟨hsTool, hsCaps, hsClear, hsFloor, hsInspect, hsOutC, hsOutI, hsDecl, hsPD⟩,
          hegr, hadm, hdisp, hauth, hquar⟩
      clear hoEq
      cases hq : j.quarantined with
      | true =>
        simp only [hq, outcome_eq_spec, bind_tc_ok] at hok
        have hnotAmb : outcome ≠ .Ambiguous := by
          intro hout
          subst hout
          simp [hblocked] at hok
        have hbAmb : decide (outcome = types.Outcome.Ambiguous) = false := by simp [hnotAmb]
        simp only [hbAmb, Bool.false_eq_true, reduceIte] at hok
        cases hattC : att with
        | none => simp [hattC, hblocked, hnotAmb] at hok
        | some r =>
          simp only [hattC, invocationId_eq_spec, bind_tc_ok] at hok
          have hrInv : r.inv = inv := by
            by_contra hn
            have hna : outcome ≠ .Ambiguous := by
              intro h
              rw [h] at hbAmb
              contradiction
            simpa [hn, hna] using hok
          simp only [hrInv, decide_true, reduceIte, outcome_eq_spec, bind_tc_ok] at hok
          have hrOutcome : r.outcome = outcome := by
            by_contra hn
            have hna : outcome ≠ .Ambiguous := by
              intro h
              rw [h] at hbAmb
              contradiction
            simpa [hn, hna] using hok
          simp only [hrOutcome, decide_true, reduceIte] at hok
          obtain ⟨bc, hbcEq, hbc⟩ := spec_imp_exists
            (vecSetContains_spec types.AttestationId.Insts.CoreCloneClone
              types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
              st.consumed_attestations r.id)
          rw [hbcEq] at hok
          simp only [bind_tc_ok] at hok
          have hbcF : bc = false := by
            cases hbcv : bc with
            | false => rfl
            | true =>
              have hna : outcome ≠ .Ambiguous := by
                intro h
                rw [h] at hbAmb
                contradiction
              simpa [hbcv, hna] using hok
          simp only [hbcF, Bool.not_false, reduceIte] at hok
          cases hattAeq : attA with
          | none => simp [hattAeq, hattC, optRel] at hatt
          | some rA =>
            have hrRel : resolutionAttestationRel rA r := by
              simpa [hattAeq, hattC, optRel] using hatt
            have hqA : jA.quarantined := hquar.mpr hq
            have hbcMem : ¬vsMem st.consumed_attestations r.id := by
              intro hc
              have hbct := hbc.mpr hc
              rw [hbcF] at hbct
              contradiction
            have hfreshA : ¬a.consumed_attestations rA.id := by
              intro ha
              apply hbcMem
              rw [← hrRel.1]
              exact (hR.consumedAtt rA.id).mp ha
            have hguard :
                (Tzimtzum.settle_invocation inv j.agent (dispA j.disposition)
                  (outcomeA outcome) (confA j.policy.output_conf)
                  (integA j.policy.output_integ) (some rA)).guard a := by
              simp only [Tzimtzum.settle_invocation]
              refine ⟨⟨jA, hjAeq⟩, hactive, hdispNot, ?_, ?_, ?_⟩
              · intro J hJ
                rw [hjAeq] at hJ
                injection hJ with hJ
                subst J
                exact ⟨hag.symm, hdisp.symm, hsOutC.symm, hsOutI.symm⟩
              · intro J hJ hJq
                rw [hjAeq] at hJ
                injection hJ with hJ
                subst J
                refine ⟨by cases outcome <;> simp_all [outcomeA], rA, rfl, ?_, ?_, hfreshA⟩
                · rw [hrRel.2.1, hrInv]
                · rw [hrRel.2.2, hrOutcome]
              · intro J hJ hJnq
                rw [hjAeq] at hJ
                injection hJ with hJ
                subst J
                exact absurd hqA hJnq
            have hnext :
                (Tzimtzum.settle_invocation inv j.agent (dispA j.disposition)
                  (outcomeA outcome) (confA j.policy.output_conf)
                  (integA j.policy.output_integ) (some rA)).next a
                  (settleStateAbs a inv outcome j.agent (dispA j.disposition)
                    (confA j.policy.output_conf) (integA j.policy.output_integ) (some rA)) := by
              simp [Tzimtzum.settle_invocation, settleStateAbs, settlePendingAbs]
            have hokTail : settleTail st inv outcome (some r) j = .ok (.Ok (st', ev)) := by
              cases hout : outcome <;> cases hd : j.disposition <;>
                simp_all [settleTail, core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default, disposition_eq_spec, outcome_eq_spec]
            refine ⟨j.agent, dispA j.disposition, confA j.policy.output_conf,
              integA j.policy.output_integ,
              settleStateAbs a inv outcome j.agent (dispA j.disposition)
                (confA j.policy.output_conf) (integA j.policy.output_integ) (some rA),
              hguard, hnext, ?_⟩
            exact settleTail_preservesR st bg a hR inv outcome (some r) (some rA) hrRel j jA
              hjAeq hj' hcapP hcapTE hcapTS hcapIE hcapIS
              (fun r' hr' => by injection hr' with hr'; subst r'; exact hcapAtt r hattC)
              st' ev hokTail
      | false =>
        simp only [hq] at hok
        cases hattC : att with
        | some r => simp [hattC, hblocked] at hok
        | none =>
          simp only [hattC, outcome_eq_spec, bind_tc_ok] at hok
          cases hattAeq : attA with
          | some rA => simp [hattAeq, hattC, optRel] at hatt
          | none =>
            have hqA : ¬jA.quarantined := by
              intro h
              have : j.quarantined = true := hquar.mp h
              rw [hq] at this
              contradiction
            have hguard :
                (Tzimtzum.settle_invocation inv j.agent (dispA j.disposition)
                  (outcomeA outcome) (confA j.policy.output_conf)
                  (integA j.policy.output_integ) none).guard a := by
              simp only [Tzimtzum.settle_invocation]
              refine ⟨⟨jA, hjAeq⟩, hactive, hdispNot, ?_, ?_, ?_⟩
              · intro J hJ
                rw [hjAeq] at hJ
                injection hJ with hJ
                subst J
                exact ⟨hag.symm, hdisp.symm, hsOutC.symm, hsOutI.symm⟩
              · intro J hJ hJq
                rw [hjAeq] at hJ
                injection hJ with hJ
                subst J
                exact absurd hJq hqA
              · intro J hJ _
                rw [hjAeq] at hJ
                injection hJ with hJ
                trivial
            have hnext :
                (Tzimtzum.settle_invocation inv j.agent (dispA j.disposition)
                  (outcomeA outcome) (confA j.policy.output_conf)
                  (integA j.policy.output_integ) none).next a
                  (settleStateAbs a inv outcome j.agent (dispA j.disposition)
                    (confA j.policy.output_conf) (integA j.policy.output_integ) none) := by
              simp [Tzimtzum.settle_invocation, settleStateAbs, settlePendingAbs]
            have hokTail : settleTail st inv outcome none j = .ok (.Ok (st', ev)) := by
              cases hout : outcome <;> cases hd : j.disposition <;>
                simp_all [settleTail, core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default, disposition_eq_spec, outcome_eq_spec]
            refine ⟨j.agent, dispA j.disposition, confA j.policy.output_conf,
              integA j.policy.output_integ,
              settleStateAbs a inv outcome j.agent (dispA j.disposition)
                (confA j.policy.output_conf) (integA j.policy.output_integ) none,
              hguard, hnext, ?_⟩
            exact settleTail_preservesR st bg a hR inv outcome none none (by trivial) j jA hjAeq hj'
              hcapP hcapTE hcapTS hcapIE hcapIS (fun r hr => by simp at hr) st' ev hokTail

end ArgusLean.Refinement
