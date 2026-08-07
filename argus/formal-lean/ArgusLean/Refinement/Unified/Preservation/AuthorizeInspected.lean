import ArgusLean.Refinement.Unified.Preservation.BeginInvocation

/-! # Layer 1 — `authorize_inspected` preserves the unified `R` (V4)

Inspection resolution reads the stored challenge, checks exact attestation scope and one-use,
re-evaluates the admissible gate against live state, optionally inserts a permitted pending record,
then always closes the challenge and consumes the attestation identifier.
-/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

/- Reuse the staged begin-admissible bridge rather than saturating the extracted live-gate tree.
   The main proof then normalizes only the positive-admit, positive-deny, and negative branches.
   `challenge_scoped` supplies the consumed-invocation fact deliberately not rechecked by Rust. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-- The extracted live authorization check is the abstract `authorizeAdmits`. -/
theorem authorizeAdmits_spec (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (inv : types.InvocationId)
    (sc : types.ChallengeScope)
    (scA : Tzimtzum.ChallengeScope types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.ChallengeId types.PolicyDigest types.ContentHash)
    (hsc : challengeRel scA sc)
    (hcapT : vmSetLen st.taint_levels sc.agent + st.pending.entries.val.length ≤ Usize.max)
    (hcapI : vmSetLen st.integ_levels sc.agent + st.pending.entries.val.length ≤ Usize.max) :
    transitions.authorize_admits st bg inv sc ⦃ b =>
      b = true ↔ Tzimtzum.authorizeAdmits a inv scA ⦄ := by
  obtain ⟨hchal, hag, hsnap, hegr, hah, hau⟩ := hsc
  unfold transitions.authorize_admits Tzimtzum.authorizeAdmits
  obtain ⟨ba, hbaEq, hba⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active sc.agent)
  rw [hbaEq]
  simp only [bind_tc_ok]
  by_cases ha : ba = true
  · simp only [ha, reduceIte, background.BackgroundTheory.impl.root_agent,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      agentId_eq_spec, bind_tc_ok]
    by_cases hne : sc.agent ≠ bg.root_agent
    · have hneB : decide (¬decide (sc.agent = bg.root_agent) = true) = true := by
        simp [hne]
      simp only [hneB, reduceIte]
      obtain ⟨bt, hbtEq, hbt⟩ := spec_imp_exists
        (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
          types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec
          st.tool_registered sc.policy.tool)
      rw [hbtEq]
      simp only [bind_tc_ok]
      by_cases ht : bt = true
      · simp only [ht, reduceIte, integLevel_le_spec, bind_tc_ok]
        by_cases hcoh : integLeC sc.policy.integ_inspect sc.policy.integ_floor = true
        · simp only [hcoh, reduceIte]
          obtain ⟨bp, hbpEq, hbp⟩ := spec_imp_exists
            (containsKey_spec types.InvocationId.Insts.CoreCloneClone
              types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
              types.PendingInvocation.Insts.CoreCloneClone st.pending inv)
          rw [hbpEq]
          simp only [bind_tc_ok]
          by_cases hp : bp = true
          · simp only [hp, reduceIte, spec_ok]
            constructor
            · intro hfalse
              exact absurd hfalse (by decide)
            · rintro ⟨_, _, _, _, hpnone, _⟩
              have hpC : pendingC st inv = none := by
                have hh := hR.pending inv
                rw [hpnone] at hh
                cases hc : pendingC st inv <;> simp_all [optRel]
              unfold pendingC at hpC
              cases hlast : vmLastEntry st.pending.entries.val inv with
              | none =>
                have hraw : ¬∃ p ∈ st.pending.entries.val, p.1 = inv := by
                  rintro ⟨p, hmem, hpI⟩
                  obtain ⟨k, v⟩ := p
                  subst hpI
                  have := (vmLastEntry_nodup _ _ _ hR.ndPending).mpr hmem
                  rw [hlast] at this
                  contradiction
                have hbpF : bp = false := by
                  cases bp <;> simp_all
                rw [hbpF] at hp
                contradiction
              | some p => simp [hlast] at hpC
          · have hpF : bp = false := by simpa using hp
            simp only [hpF, Bool.false_eq_true, reduceIte]
            obtain ⟨bn, hbnEq, hbn⟩ := spec_imp_exists
              (egressNarrows_spec sc.egress sc.policy.declared_egress)
            rw [hbnEq]
            simp only [bind_tc_ok]
            by_cases hn : bn = true
            · simp only [hn, reduceIte]
              obtain ⟨bc, hbcEq, hbc⟩ := spec_imp_exists
                (egressCovers_spec sc.policy.declared_egress sc.egress)
              rw [hbcEq]
              simp only [bind_tc_ok]
              by_cases hcov : bc = true
              · simp only [hcov, reduceIte]
                obtain ⟨badm, hbadmEq, hbadm⟩ := spec_imp_exists
                  (beginAdmissible_spec st bg a hR sc.agent sc.policy scA.policy hsnap
                    sc.egress scA.egress (fun E => (hegr E).symm)
                    sc.authorized scA.authorized hau.symm hcapT hcapI)
                rw [hbadmEq]
                simp only [spec_ok]
                rw [hag]
                constructor
                · intro hadm
                  refine ⟨(hR.active sc.agent).mpr (hba.mp ha), ?_, ?_, ?_, ?_, ?_, ?_,
                    hbadm.mp hadm⟩
                  · rw [hR.root]
                    exact hne
                  · rw [hsnap.1]
                    exact (hR.tool_reg sc.policy.tool).mpr (hbt.mp ht)
                  · obtain ⟨_, _, _, hfloor, hinspect, _⟩ := hsnap
                    rw [hinspect, hfloor, le_integ_integLeC_both]
                    exact hcoh
                  · have hpC : pendingC st inv = none := by
                      unfold pendingC
                      apply Option.map_eq_none_iff.mpr
                      apply vmLastEntry_eq_none
                      intro p hmem hpI
                      exact hp (hbp.mpr ⟨p, hmem, hpI⟩)
                    have hh := hR.pending inv
                    rw [hpC] at hh
                    cases hpa : a.pending inv <;> simp_all [optRel]
                  · intro E hE
                    obtain ⟨_, _, _, _, _, _, _, hdecl, _⟩ := hsnap
                    exact (hdecl E).mpr (hbn.mp hn E ((hegr E).mp hE))
                  · intro hdecl
                    obtain ⟨E, hE⟩ := hdecl
                    obtain ⟨_, _, _, _, _, _, _, hdeclRel, _⟩ := hsnap
                    have hdne : sc.policy.declared_egress.items.val ≠ [] := by
                      intro hempty
                      have := (hdeclRel E).mp hE
                      rw [hempty] at this
                      contradiction
                    have hene := hbc.mp hcov hdne
                    obtain ⟨E', hE'⟩ := List.exists_mem_of_ne_nil sc.egress.items.val hene
                    exact ⟨E', (hegr E').mpr hE'⟩
                · rintro ⟨_, _, _, _, _, _, _, hadm⟩
                  exact hbadm.mpr hadm
              · have hcovF : bc = false := by simpa using hcov
                simp only [hcovF, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
                rintro ⟨_, _, _, _, _, _, hcover, _⟩
                obtain ⟨_, _, _, _, _, _, _, hdecl, _⟩ := hsnap
                have hcabs : (∃ E, scA.policy.declared_egress E) → ∃ E, scA.egress E := hcover
                by_cases hd : sc.policy.declared_egress.items.val = []
                · have : bc = true := hbc.mpr (by simp [hd])
                  rw [hcovF] at this
                  contradiction
                · obtain ⟨E, hE⟩ := List.exists_mem_of_ne_nil _ hd
                  obtain ⟨E', hE'⟩ := hcabs ⟨E, (hdecl E).mpr hE⟩
                  have hegrne : sc.egress.items.val ≠ [] := by
                    intro hempty
                    have := (hegr E').mp hE'
                    rw [hempty] at this
                    contradiction
                  exact hcov (hbc.mpr (fun _ => hegrne))
            · have hnF : bn = false := by simpa using hn
              simp only [hnF, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
              rintro ⟨_, _, _, _, _, hnarrow, _⟩
              have hconc : ∀ E ∈ sc.egress.items.val, E ∈ sc.policy.declared_egress.items.val := by
                intro E hE
                obtain ⟨_, _, _, _, _, _, _, hdecl, _⟩ := hsnap
                exact (hdecl E).mp (hnarrow E ((hegr E).mpr hE))
              have := hbn.mpr hconc
              rw [hnF] at this
              contradiction
        · have hcohF : integLeC sc.policy.integ_inspect sc.policy.integ_floor = false := by
            simpa using hcoh
          simp only [hcohF, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
          rintro ⟨_, _, _, habs, _⟩
          obtain ⟨_, _, _, hfloor, hinspect, _⟩ := hsnap
          rw [hinspect, hfloor, le_integ_integLeC_both] at habs
          rw [hcohF] at habs
          contradiction
      · have htF : bt = false := by simpa using ht
        simp only [htF, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
        rintro ⟨_, _, htoolA, _⟩
        rw [hsnap.1] at htoolA
        have := hbt.mpr ((hR.tool_reg sc.policy.tool).mp htoolA)
        rw [htF] at this
        contradiction
    · have hneF : decide (¬decide (sc.agent = bg.root_agent) = true) = false := by
        simp [hne]
      simp only [hneF, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
      rintro ⟨_, hneA, _⟩
      rw [hag, hR.root] at hneA
      exact hneA (by simpa using hne)
  · have haF : ba = false := by simpa using ha
    simp only [haF, Bool.false_eq_true, reduceIte, spec_ok, false_iff]
    rintro ⟨hactiveA, _⟩
    have := hba.mpr ((hR.active sc.agent).mp (by rw [← hag]; exact hactiveA))
    rw [haF] at this
    contradiction


/-- Rebuild `R` after challenge removal and attestation consumption. -/
theorem authorizePostR (st st' : state.KernelState) (bg : background.BackgroundTheory)
    (a a' : AbsState) (hR : R st bg a) (inv : types.InvocationId)
    (pending' : collections.VecMap types.InvocationId types.PendingInvocation)
    (hpending : ∀ I, optRel pendingRel (a'.pending I)
      (Option.map Prod.snd (vmLastEntry pending'.entries.val I)))
    (hndPending : vmNodupKeys pending')
    (hchalA : ∀ I, a'.challenges I = if I = inv then none else a.challenges I)
    (attId : types.AttestationId)
    (hattA : ∀ X, a'.consumed_attestations X ↔ a.consumed_attestations X ∨ X = attId)
    (hframes : a'.root_agent = a.root_agent ∧ a'.mode = a.mode ∧
      a'.agent_active = a.agent_active ∧ a'.tool_registered = a.tool_registered ∧
      a'.agent_parent = a.agent_parent ∧ a'.agent_cap = a.agent_cap ∧
      a'.taint_levels = a.taint_levels ∧ a'.integ_levels = a.integ_levels ∧
      a'.crossing_grants = a.crossing_grants ∧ a'.consumed_ids = a.consumed_ids ∧
      a'.consumed_crossings = a.consumed_crossings ∧ a'.flow_allows = a.flow_allows ∧
      a'.flow_inspects = a.flow_inspects)
    (hcapAtt : st.consumed_attestations.items.val.length < Usize.max)
    (ev0 ev : event.KernelAction)
    (hok : (do
      let ch ← collections.VecMap.remove types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId
        types.ChallengeScope.Insts.CoreCloneClone st.challenges inv
      let ca ← types.AttestationId.Insts.CoreCloneClone.clone attId
      let ats ← collections.VecSet.insert types.AttestationId.Insts.CoreCloneClone
        types.AttestationId.Insts.CoreCmpPartialEqAttestationId st.consumed_attestations ca
      ok (.Ok ({ { { st with pending := pending' } with challenges := ch } with
        consumed_attestations := ats }, ev0))) =
      (.ok (.Ok (st', ev)) : Result (core.result.Result
        (state.KernelState × event.KernelAction) error.KernelError))) :
    R st' bg a' := by
  obtain ⟨ch, hchEq, hch⟩ := spec_imp_exists
    (vecMapRemove_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_ne_spec
      types.ChallengeScope.Insts.CoreCloneClone st.challenges inv)
  rw [hchEq] at hok
  simp only [bind_tc_ok, attestationId_clone_spec] at hok
  obtain ⟨ats, hatsEq, hats⟩ := spec_imp_exists
    (vecSetInsert_spec types.AttestationId.Insts.CoreCloneClone
      types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
      st.consumed_attestations attId hcapAtt)
  rw [hatsEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq,
    Prod.mk.injEq] at hok
  obtain ⟨hst, hev⟩ := hok
  subst st'
  obtain ⟨hroot, hmode, hactive, htool, hparent, hcap, htaint, hinteg, hgrants,
    hids, hcross, hflowA, hflowI⟩ := hframes
  refine { root := by rw [hroot, hR.root]
           mode := by rw [hmode, hR.mode]
           active := by intro x; rw [hactive]; exact hR.active x
           tool_reg := by intro t; rw [htool]; exact hR.tool_reg t
           parent := by intro C P; rw [hparent]; exact hR.parent C P
           cap := by intro N C; rw [hcap]; exact hR.cap N C
           taint := by intro ag L; rw [htaint]; exact hR.taint ag L
           integ := by intro ag L; rw [hinteg]; exact hR.integ ag L
           pending := hpending
           challenges := ?_
           grants := by intro A D; rw [hgrants]; exact hR.grants A D
           consumedIds := by intro I; rw [hids]; exact hR.consumedIds I
           consumedAtt := ?_
           consumedCross := by intro X; rw [hcross]; exact hR.consumedCross X
           flowAllows := by intro L E; rw [hflowA]; exact hR.flowAllows L E
           flowInspects := by intro L E; rw [hflowI]; exact hR.flowInspects L E
           ndParent := hR.ndParent
           ndCap := hR.ndCap
           ndTaint := hR.ndTaint
           ndInteg := hR.ndInteg
           ndPending := ?_
           ndChallenges := ?_
           ndGrants := hR.ndGrants }
  · intro I
    change optRel challengeRel (a'.challenges I)
      (Option.map Prod.snd (vmLastEntry ch.entries.val I))
    rw [hch]
    by_cases hI : I = inv
    · subst I
      rw [vmLastEntry_filter_removeKept, hchalA inv]
      simp [optRel]
    · rw [vmLastEntry_filter_removeKept, if_neg hI, hchalA I, if_neg hI]
      exact hR.challenges I
  · intro X
    rw [hattA X, hats]
    exact or_congr (hR.consumedAtt X) (by simp)
  · exact hndPending
  · change vmNodupKeys ch
    unfold vmNodupKeys
    rw [hch]
    exact List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hR.ndChallenges

/-- Canonical abstract post-state for inspection authorization. -/
def authorizeAbs (a : AbsState) (inv : types.InvocationId)
    (sc : Tzimtzum.ChallengeScope types.AgentId types.ToolId capability.CapKind
      types.EgressKind types.ChallengeId types.PolicyDigest types.ContentHash)
    (att : Tzimtzum.InspectionAttestation types.InvocationId types.ChallengeId
      types.AttestationId types.PolicyDigest types.ContentHash) (admit : Bool) : AbsState :=
  { a with
    pending := fun I =>
      if I = inv ∧ admit = true then
        some (Tzimtzum.PendingInvocation.mk sc.agent sc.policy sc.egress
          (.inspected att.id) .permitted sc.authorized False)
      else a.pending I
    challenges := fun I => if I = inv then none else a.challenges I
    consumed_attestations := fun X => a.consumed_attestations X ∨ X = att.id }

/-- V4 `authorize_inspected` preserves the unified relation. -/
theorem authorize_inspected_preservesR (st : state.KernelState)
    (bg : background.BackgroundTheory) (a : AbsState)
    (inv : types.InvocationId) (att : types.InspectionAttestation)
    (attA : Tzimtzum.InspectionAttestation types.InvocationId types.ChallengeId
      types.AttestationId types.PolicyDigest types.ContentHash)
    (hatt : inspectionAttestationRel attA att) (hR : R st bg a)
    (hScoped : Tzimtzum.challenge_scoped a)
    (hcapT : ∀ sc, challengeC st inv = some sc →
      vmSetLen st.taint_levels sc.agent + st.pending.entries.val.length ≤ Usize.max)
    (hcapI : ∀ sc, challengeC st inv = some sc →
      vmSetLen st.integ_levels sc.agent + st.pending.entries.val.length ≤ Usize.max)
    (hcapP : st.pending.entries.val.length < Usize.max)
    (hcapAtt : st.consumed_attestations.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.authorize_inspected st bg inv att = .ok (.Ok (st', ev))) :
    ∃ (scA : Tzimtzum.ChallengeScope types.AgentId types.ToolId capability.CapKind
          types.EgressKind types.ChallengeId types.PolicyDigest types.ContentHash)
      (admit : Bool) (a' : AbsState),
      (Tzimtzum.authorize_inspected inv scA attA admit).guard a ∧
      (Tzimtzum.authorize_inspected inv scA attA admit).next a a' ∧ R st' bg a' := by
  simp only [transitions.authorize_inspected] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ChallengeScope.Insts.CoreCloneClone challengeScope_clone_spec st.challenges inv)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  cases hoO : o with
  | none => simp [hoO] at hok
  | some sc =>
    have hscC : challengeC st inv = some sc := by
      unfold challengeC
      rw [← ho, hoO]
    have hopt := hR.challenges inv
    rw [hscC] at hopt
    cases hscAeq : a.challenges inv with
    | none => simp [hscAeq, optRel] at hopt
    | some scA =>
      have hsc : challengeRel scA sc := by simpa [hscAeq, optRel] using hopt
      obtain ⟨hchid, hag, hsnap, hegr, hah, hau⟩ := hsc
      have hsc' : challengeRel scA sc := ⟨hchid, hag, hsnap, hegr, hah, hau⟩
      have hsnapDigest : scA.policy.policy_digest = sc.policy.policy_digest :=
        hsnap.2.2.2.2.2.2.2.2
      obtain ⟨hatId, hatInv, hatCh, hatHash, hatPolicy, hatPos⟩ := hatt
      simp only [hoO, core.cmp.PartialEq.ne.trait_default,
        core.cmp.PartialEq.ne.default, invocationId_eq_spec, bind_tc_ok] at hok
      have hi : att.inv = inv := by
        by_contra hne
        have hb : decide (¬decide (att.inv = inv) = true) = true := by simp [hne]
        simp only [hb, reduceIte] at hok
        simp at hok
      have hbi : decide (¬decide (att.inv = inv) = true) = false := by simp [hi]
      simp only [hbi, Bool.false_eq_true, reduceIte, challengeId_eq_spec, bind_tc_ok] at hok
      have hch : att.challenge = sc.challenge := by
        by_contra hne
        have hb : decide (¬decide (att.challenge = sc.challenge) = true) = true := by simp [hne]
        simp only [hb, reduceIte] at hok
        simp at hok
      have hbch : decide (¬decide (att.challenge = sc.challenge) = true) = false := by simp [hch]
      simp only [hbch, Bool.false_eq_true, reduceIte, contentHash_eq_spec, bind_tc_ok] at hok
      have hh : att.args_hash = sc.args_hash := by
        by_contra hne
        have hb : decide (¬decide (att.args_hash = sc.args_hash) = true) = true := by simp [hne]
        simp only [hb, reduceIte] at hok
        simp at hok
      have hbh : decide (¬decide (att.args_hash = sc.args_hash) = true) = false := by simp [hh]
      simp only [hbh, Bool.false_eq_true, reduceIte, policyDigest_eq_spec, bind_tc_ok] at hok
      have hpd : att.policy_digest = sc.policy.policy_digest := by
        by_contra hne
        have hb : decide (¬decide (att.policy_digest = sc.policy.policy_digest) = true) = true := by
          simp [hne]
        simp only [hb, reduceIte] at hok
        simp at hok
      have hbpd : decide (¬decide (att.policy_digest = sc.policy.policy_digest) = true) = false := by
        simp [hpd]
      simp only [hbpd, Bool.false_eq_true, reduceIte] at hok
      obtain ⟨bc, hbcEq, hbc⟩ := spec_imp_exists
        (vecSetContains_spec types.AttestationId.Insts.CoreCloneClone
          types.AttestationId.Insts.CoreCmpPartialEqAttestationId attestationId_eq_spec
          st.consumed_attestations att.id)
      rw [hbcEq] at hok
      simp only [bind_tc_ok] at hok
      have hbcF : bc = false := by
        cases hb : bc with
        | false => rfl
        | true => simp [hb] at hok
      simp only [hbcF, Bool.false_eq_true, reduceIte] at hok
      have hnotConsumedA : ¬a.consumed_attestations attA.id := by
        intro haC
        have haC' : a.consumed_attestations att.id := by rw [← hatId]; exact haC
        have hcC := (hR.consumedAtt att.id).mp haC'
        have := hbc.mpr hcC
        rw [hbcF] at this
        contradiction
      have hconsumedId : a.consumed_ids inv := (hScoped inv scA hscAeq).2.1
      by_cases hp : att.positive = true
      · simp only [hp, reduceIte] at hok
        obtain ⟨badm, hbadmEq, hbadm⟩ := spec_imp_exists
          (authorizeAdmits_spec st bg a hR inv sc scA hsc'
            (hcapT sc hscC) (hcapI sc hscC))
        rw [hbadmEq] at hok
        simp only [bind_tc_ok] at hok
        cases ha : badm with
        | true =>
          have hcloneE := vecSetClone_spec types.EgressKind.Insts.CoreCloneClone
            egressKind_clone_spec sc.egress
          simp only [ha, reduceIte, invocationId_clone_spec, agentId_clone_spec,
            actionPolicySnapshot_clone_spec, hcloneE, attestationId_clone_spec,
            bind_tc_ok] at hok
          let cj : types.PendingInvocation := types.PendingInvocation.mk sc.agent sc.policy
            sc.egress (.Inspected att.id) .Permitted sc.authorized false
          let aj : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
              types.EgressKind types.AttestationId types.PolicyDigest :=
            Tzimtzum.PendingInvocation.mk scA.agent scA.policy scA.egress
              (.inspected attA.id) .permitted scA.authorized False
          have hrel : pendingRel aj cj := by
            unfold aj cj
            rw [hag]
            exact pendingRel_new sc.agent sc.policy scA.policy hsnap sc.egress scA.egress
              (fun E => (hegr E).symm) sc.authorized scA.authorized hau.symm
              (.Inspected att.id) (.inspected attA.id)
              (by simp [admissionRel, hatId]) .Permitted .permitted rfl
          obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
            (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
              types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
              types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj hcapP)
          obtain ⟨vmN, hvmNEq, hvmN⟩ := spec_imp_exists
            (vecMapInsert_nodup types.InvocationId.Insts.CoreCloneClone
              types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
              types.PendingInvocation.Insts.CoreCloneClone st.pending inv cj hcapP)
          have hvmN' : vmN = vm := Result.ok.inj (hvmNEq.symm.trans hvmEq)
          simp only [cj] at hvmEq
          rw [hvmEq] at hok
          refine ⟨scA, true, authorizeAbs a inv scA attA true, ?_, ?_, ?_⟩
          · simp only [Tzimtzum.authorize_inspected]
            exact ⟨hscAeq, by rw [hatInv]; exact hi, by rw [hatCh, hchid]; exact hch,
              by rw [hatHash, hah]; exact hh, by rw [hatPolicy, hsnapDigest]; exact hpd,
              hnotConsumedA, hconsumedId,
              fun _ => ⟨hatPos.mpr hp, hbadm.mp (by simp [ha])⟩, by simp⟩
          · simp [Tzimtzum.authorize_inspected, authorizeAbs]
            funext I
            by_cases hI : I = inv <;> simp [hI]
          · apply authorizePostR st st' bg a (authorizeAbs a inv scA attA true) hR inv vm (hndPending := hvmN' ▸ hvmN hR.ndPending)
              (attId := att.id) (ev0 := event.KernelAction.AuthorizeInspected inv att.id true)
              (ev := ev) (hcapAtt := hcapAtt)
            · intro I
              simpa [authorizeAbs] using
                (pending_clause_insert st bg a hR inv aj cj hrel vm hvm I)
            · intro I
              simp [authorizeAbs]
            · intro X
              unfold authorizeAbs
              change (a.consumed_attestations X ∨ X = attA.id) ↔
                a.consumed_attestations X ∨ X = att.id
              rw [hatId]
            · unfold authorizeAbs
              refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
              · funext L E; unfold Tzimtzum.St.flow_allows; rfl
              · funext L E; unfold Tzimtzum.St.flow_inspects; rfl
            · simpa only [Bool.false_eq_true, reduceIte, bind_tc_ok, attestationId_clone_spec] using hok
        | false =>
          simp only [ha, Bool.false_eq_true, reduceIte] at hok
          refine ⟨scA, false, authorizeAbs a inv scA attA false, ?_, ?_, ?_⟩
          · simp only [Tzimtzum.authorize_inspected]
            exact ⟨hscAeq, by rw [hatInv]; exact hi, by rw [hatCh, hchid]; exact hch,
              by rw [hatHash, hah]; exact hh, by rw [hatPolicy, hsnapDigest]; exact hpd,
              hnotConsumedA, hconsumedId, by simp,
              fun _ => Or.inr (fun hadm => by
                have := hbadm.mpr hadm
                simp [ha] at this)⟩
          · simp [Tzimtzum.authorize_inspected, authorizeAbs]
            funext I
            by_cases hI : I = inv <;> simp [hI]
          · apply authorizePostR st st' bg a (authorizeAbs a inv scA attA false) hR inv st.pending (hndPending := hR.ndPending) (attId := att.id)
              (ev0 := event.KernelAction.AuthorizeInspected inv att.id false) (ev := ev)
              (hcapAtt := hcapAtt)
            · intro I
              simpa only [authorizeAbs, Bool.false_eq_true, and_false, if_false, pendingC] using hR.pending I
            · intro I
              simp [authorizeAbs]
            · intro X
              unfold authorizeAbs
              change (a.consumed_attestations X ∨ X = attA.id) ↔
                a.consumed_attestations X ∨ X = att.id
              rw [hatId]
            · unfold authorizeAbs
              refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
              · funext L E; unfold Tzimtzum.St.flow_allows; rfl
              · funext L E; unfold Tzimtzum.St.flow_inspects; rfl
            · simpa only [Bool.false_eq_true, reduceIte, bind_tc_ok, attestationId_clone_spec] using hok
      · have hpF : att.positive = false := by simpa using hp
        simp only [hpF, Bool.false_eq_true, reduceIte] at hok
        refine ⟨scA, false, authorizeAbs a inv scA attA false, ?_, ?_, ?_⟩
        · simp only [Tzimtzum.authorize_inspected]
          exact ⟨hscAeq, by rw [hatInv]; exact hi, by rw [hatCh, hchid]; exact hch,
            by rw [hatHash, hah]; exact hh, by rw [hatPolicy, hsnapDigest]; exact hpd,
            hnotConsumedA, hconsumedId, by simp,
            fun _ => Or.inl (by rw [hatPos]; simpa using hp)⟩
        · simp [Tzimtzum.authorize_inspected, authorizeAbs]
          funext I
          by_cases hI : I = inv <;> simp [hI]
        · apply authorizePostR st st' bg a (authorizeAbs a inv scA attA false) hR inv st.pending (hndPending := hR.ndPending) (attId := att.id)
            (ev0 := event.KernelAction.AuthorizeInspected inv att.id false) (ev := ev)
            (hcapAtt := hcapAtt)
          · intro I
            simpa only [authorizeAbs, Bool.false_eq_true, and_false, if_false, pendingC] using hR.pending I
          · intro I
            simp [authorizeAbs]
          · intro X
            unfold authorizeAbs
            change (a.consumed_attestations X ∨ X = attA.id) ↔
              a.consumed_attestations X ∨ X = att.id
            rw [hatId]
          · unfold authorizeAbs
            refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
            · funext L E; unfold Tzimtzum.St.flow_allows; rfl
            · funext L E; unfold Tzimtzum.St.flow_inspects; rfl
          · simpa only [Bool.false_eq_true, reduceIte, bind_tc_ok, attestationId_clone_spec] using hok

end ArgusLean.Refinement
