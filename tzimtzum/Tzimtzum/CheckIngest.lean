import Tzimtzum.Soundness.Common

/-! `ingest` preserves the bundle (one theorem per sub-bundle).

Ingestion inserts one provenance pair into the target's label sets; the permitted arm is
gated by `ingestHolds`, and the monitor arm demotes the target's permitted records instead.
The manual bullets all follow one argument: a post-state pending record is an old record
unchanged or an old record demoted (`pending_preimage`), a *contained* record is always an
old record unchanged (`contained_pending_preimage`), and a contained record owned by the
ingest target forces the permitted arm (`contained_owner_permitted`) — whose `ingestHolds`
guard payload then covers the new label, arm by arm. Everything else is automated. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- The state at this file's sort tuple. The ascription in each `Preserves` statement pins
the sorts the action's arguments do not determine. -/
local notation "St!" => St AgentId ToolId InvocationId CapKind EgressKind ChallengeId
  AttestationId CrossingId AssignmentDigest PolicyDigest ContentHash

/-! ## Inversion helpers

Built on the `kav_action`-generated projections (`next_pending`, `guard_not_blocked`, …):
nothing in this file destructures the action's `guard`/`next` conjunctions positionally. -/

section Inversion

variable {a : AgentId} {src : Option AgentId} {pconf : ConfLevel} {pinteg : IntegLevel}
  {d : Disposition}
  {s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash}
  {I : InvocationId}
  {J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest}

/-- Every post-ingest pending record comes from the old map unchanged or with only its
`disposition` demoted. Keeping this frame fact explicit avoids unfolding the full invariant
bundle in every pending-record VC. -/
private theorem pending_preimage (hn : (ingest a src pconf pinteg d).next s s')
    (hJ : s'.pending I = some J) :
    ∃ K, s.pending I = some K
      ∧ (J = K ∨ (d = Disposition.monitor_bypassed
        ∧ J = { K with disposition := Disposition.monitor_bypassed })) := by
  rw [ingest.next_pending hn] at hJ
  by_cases hd : d = Disposition.monitor_bypassed
  · simp only [if_pos hd] at hJ
    rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
      ⟨K, hK, -, hEq⟩ | ⟨hOld, -⟩
    · exact ⟨K, hK, Or.inr ⟨hd, hEq⟩⟩
    · exact ⟨J, hOld, Or.inl rfl⟩
  · exact ⟨J, by simpa only [if_neg hd] using hJ, Or.inl rfl⟩

/-- A contained post-ingest record cannot be one of the demoted records, so it is present
unchanged in the pre-state. -/
private theorem contained_pending_preimage (hn : (ingest a src pconf pinteg d).next s s')
    (hJ : s'.pending I = some J) (hcontained : contained J) : s.pending I = some J := by
  rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, hdemoted⟩⟩
  · exact hK
  · rw [hdemoted] at hcontained
    simp [contained] at hcontained

/-- A contained post-ingest record owned by the ingest target can only come from the
permitted arm; the monitor arm demotes every such record. -/
private theorem contained_owner_permitted (hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s')
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = a) :
    d = Disposition.permitted := by
  cases d with
  | permitted => rfl
  | blocked => kav_discharge_lite ingest
  | monitor_bypassed =>
      rw [ingest.next_pending hn] at hJ
      simp only [if_pos rfl] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, -, -, hEq⟩ | ⟨-, hOther⟩
      · rw [hEq] at hcontained
        simp [contained] at hcontained
      · exact (hOther howner).elim

end Inversion

/-! ## Preservation, one theorem per sub-bundle -/

/-- `invS` (9 structural conjuncts): automated except `revocation_clean` (an inactive
agent's cleanliness survives because only the active target gains labels and only its
records are demoted) and `pending_active` (record owners are unchanged by demotion). -/
theorem presS_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition) :
    Preserves (ingest a src pconf pinteg d : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  refine ⟨?root_always_active, ?parent_implies_active, ?single_parent, ?no_self_parent,
    ?root_no_parent, ?capability_subsumption, ?root_all_caps, ?revocation_clean,
    ?pending_active⟩
  case root_always_active => kav_discharge_lite ingest
  case parent_implies_active => kav_discharge_lite ingest
  case single_parent => kav_discharge_lite ingest
  case no_self_parent => kav_discharge_lite ingest
  case root_no_parent => kav_discharge_lite ingest
  case capability_subsumption => kav_discharge_lite ingest
  case root_all_caps => kav_discharge_lite ingest
  case revocation_clean =>
    have hact := ingest.next_agent_active hn
    have ht := ingest.next_taint_levels hn
    have hi := ingest.next_integ_levels hn
    have hpen := ingest.next_pending hn
    have hch := ingest.next_challenges hn
    have hgrants := ingest.next_crossing_grants hn
    have ha := ingest.guard_active hg
    intro A hA
    rw [hact] at hA
    have hne : A ≠ a := by
      intro heq
      subst A
      exact hA ha
    obtain ⟨hrt, hri, hrp, hrch, hrg⟩ := hinv.revocation_clean A hA
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro L hL
      rw [ht] at hL
      rcases hL with hL | ⟨heq, -⟩
      · exact hrt L hL
      · exact hne heq
    · intro L hL
      rw [hi] at hL
      rcases hL with hL | ⟨heq, -⟩
      · exact hri L hL
      · exact hne heq
    · intro I J hJ
      rw [hpen] at hJ
      by_cases hd : d = Disposition.monitor_bypassed
      · simp only [if_pos hd] at hJ
        rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
          ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
        · exact hrp I K hK
        · exact hrp I J hK
      · have hOld : s.pending I = some J := by simpa only [if_neg hd] using hJ
        exact hrp I J hOld
    · intro I sc hsc
      rw [hch] at hsc
      exact hrch I sc hsc
    · intro D
      rw [hgrants]
      exact hrg D
  case pending_active =>
    have hact := ingest.next_agent_active hn
    have hpen := ingest.next_pending hn
    intro I J hJ
    rw [hact]
    rw [hpen] at hJ
    by_cases hd : d = Disposition.monitor_bypassed
    · simp only [if_pos hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
      · exact hinv.pending_active I K hK
      · exact hinv.pending_active I J hK
    · have hOld : s.pending I = some J := by simpa only [if_neg hd] using hJ
      exact hinv.pending_active I J hOld

/-- `invP` (12 pending/gate conjuncts). `pending_unique` is automated. The rest are
manual: registry/identifier/ceiling facts route each record through `pending_preimage`,
and the five confinement conjuncts split on whether the constrained label is old (the
pre-state invariant applies) or the newly ingested pair (the permitted arm's
`ingestHolds` payload applies, via `contained_owner_permitted`). -/
theorem presP_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition) :
    Preserves (ingest a src pconf pinteg d : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  refine ⟨?pending_unique, ?pending_registered, ?root_no_pending, ?pending_ids_consumed,
    ?pending_egress_attested, ?pending_snapshot_coherent, ?default_deny, ?flow_confinement,
    ?flow_confinement_weak, ?integrity_confinement, ?integrity_confinement_weak,
    ?clearance_confinement⟩
  case pending_unique => kav_discharge_lite ingest
  case pending_registered =>
    have hpen := ingest.next_pending hn
    have htool := ingest.next_tool_registered hn
    intro I J hJ
    rw [htool]
    rw [hpen] at hJ
    by_cases hd : d = Disposition.monitor_bypassed
    · simp only [if_pos hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
      · exact hinv.pending_registered I K hK
      · exact hinv.pending_registered I J hK
    · have hOld : s.pending I = some J := by simpa only [if_neg hd] using hJ
      exact hinv.pending_registered I J hOld
  case root_no_pending =>
    have hroot := ingest.next_root_agent hn
    intro I J hJ
    rw [hroot]
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hinv.root_no_pending I J hK
    · exact hinv.root_no_pending I K hK
  case pending_ids_consumed =>
    have hids := ingest.next_consumed_ids hn
    intro I J hJ
    rw [hids]
    rcases pending_preimage hn hJ with ⟨K, hK, -⟩
    exact hinv.pending_ids_consumed I K hK
  case pending_egress_attested =>
    intro I J hJ
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hinv.pending_egress_attested I J hK
    · exact hinv.pending_egress_attested I K hK
  case pending_snapshot_coherent =>
    intro I J hJ
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hinv.pending_snapshot_coherent I J hK
    · exact hinv.pending_snapshot_coherent I K hK
  case default_deny =>
    have hcap := ingest.next_agent_cap hn
    intro I J hJ hcontained
    rw [hcap]
    exact hinv.default_deny I J (contained_pending_preimage hn hJ hcontained) hcontained
  case flow_confinement =>
    have hpermit := ingest.guard_permitted_holds hg
    have ht := ingest.next_taint_levels hn
    have hallow := ingest.next_egress_allow_ceiling hn
    have hinspect := ingest.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hinv.flow_confinement L I J E hL hOld hcontained hE
    · subst L
      have hd := contained_owner_permitted hg hn hJ hcontained howner
      exact (hpermit hd).conf I J E hOld howner hE
  case flow_confinement_weak =>
    have hpermit := ingest.guard_permitted_holds hg
    have ht := ingest.next_taint_levels hn
    have hallow := ingest.next_egress_allow_ceiling hn
    have hinspect := ingest.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hinv.flow_confinement_weak L I J E hL hOld hcontained hE
    · subst L
      have hd := contained_owner_permitted hg hn hJ hcontained howner
      rcases (hpermit hd).conf I J E hOld howner hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  case integrity_confinement =>
    have hpermit := ingest.guard_permitted_holds hg
    have hi := ingest.next_integ_levels hn
    intro L I J hL hJ hcontained
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hinv.integrity_confinement L I J hL hOld hcontained
    · subst L
      have hd := contained_owner_permitted hg hn hJ hcontained howner
      exact (hpermit hd).integ I J hOld howner
  case integrity_confinement_weak =>
    have hpermit := ingest.guard_permitted_holds hg
    have hi := ingest.next_integ_levels hn
    intro L I J hL hJ hcontained
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hinv.integrity_confinement_weak L I J hL hOld hcontained
    · subst L
      have hd := contained_owner_permitted hg hn hJ hcontained howner
      rcases (hpermit hd).integ I J hOld howner with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  case clearance_confinement =>
    have hpermit := ingest.guard_permitted_holds hg
    have ht := ingest.next_taint_levels hn
    intro L I J hJ hcontained hspec
    have hOldJ := contained_pending_preimage hn hJ hcontained
    unfold speculative_taint_contained at hspec
    rcases hspec with hL | ⟨I2, K, hK, hagent, hKcontained, hlevel⟩
    · rw [ht] at hL
      rcases hL with hL | ⟨howner, hnew⟩
      · exact hinv.clearance_confinement L I J hOldJ hcontained (Or.inl hL)
      · subst L
        have hd := contained_owner_permitted hg hn hJ hcontained howner
        exact (hpermit hd).clear I J hOldJ howner
    · have hOldK := contained_pending_preimage hn hK hKcontained
      exact hinv.clearance_confinement L I J hOldJ hcontained
        (Or.inr ⟨I2, K, hOldK, hagent, hKcontained, hlevel⟩)

/-- `invPP` (2 pairwise conjuncts), both manual: contained records are pre-existing
(`contained_pending_preimage`) and the flow relations are framed, so both conjuncts defer
to the pre-state invariant. -/
theorem presPP_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition) :
    Preserves (ingest a src pconf pinteg d : Kav.Action St!) invPP := by
  intro s s' hinv _hg hn
  refine ⟨?pending_flow_compat, ?pending_integ_compat⟩
  case pending_flow_compat =>
    have hallow := ingest.next_egress_allow_ceiling hn
    have hinspect := ingest.next_egress_inspect_ceiling hn
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    exact hinv.pending_flow_compat I1 I2 J1 J2 E
      (contained_pending_preimage hn hJ1 hcontained1)
      (contained_pending_preimage hn hJ2 hcontained2)
      hagent hcontained1 hcontained2 hE
  case pending_integ_compat =>
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    exact hinv.pending_integ_compat I1 I2 J1 J2
      (contained_pending_preimage hn hJ1 hcontained1)
      (contained_pending_preimage hn hJ2 hcontained2)
      hagent hcontained1 hcontained2

/-- `invE` (6 evidence conjuncts): manual frame arguments. Challenges, consumed
histories, mode, and scope-relevant state are all framed, so each conjunct routes its
record or scope through the appropriate frame projection and defers to the pre-state
invariant; `quarantine_pending` is immediate. -/
theorem presE_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition) :
    Preserves (ingest a src pconf pinteg d : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  refine ⟨?challenge_scoped, ?challenges_enforce_only, ?challenge_unique,
    ?inspected_evidence_consumed, ?bypass_mode_sound, ?quarantine_pending⟩
  case challenge_scoped =>
    have hact := ingest.next_agent_active hn
    have hpen := ingest.next_pending hn
    have hch := ingest.next_challenges hn
    have hids := ingest.next_consumed_ids hn
    have htool := ingest.next_tool_registered hn
    have hroot := ingest.next_root_agent hn
    intro I sc hsc
    rw [hch] at hsc
    obtain ⟨hpending, hid, hactive, hnonroot, hregistered, hcoherent, hnarrow, hcoverage⟩ :=
      hinv.challenge_scoped I sc hsc
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hnarrow, hcoverage⟩
    · rw [hpen]
      by_cases hd : d = Disposition.monitor_bypassed
      · simpa only [if_pos hd, demoteAllOf_eq_none] using hpending
      · simpa only [if_neg hd] using hpending
    · rw [hids]
      exact hid
    · rw [hact]
      exact hactive
    · rw [hroot]
      exact hnonroot
    · rw [htool]
      exact hregistered
    · exact hcoherent
  case challenges_enforce_only =>
    have hch := ingest.next_challenges hn
    have hmode := ingest.next_mode hn
    intro I sc hsc
    rw [hmode]
    rw [hch] at hsc
    exact hinv.challenges_enforce_only I sc hsc
  case challenge_unique =>
    have hch := ingest.next_challenges hn
    intro I sc1 sc2 hsc1 hsc2
    rw [hch] at hsc1 hsc2
    exact hinv.challenge_unique I sc1 sc2 hsc1 hsc2
  case inspected_evidence_consumed =>
    have hatt := ingest.next_consumed_attestations hn
    intro I J att hJ hadmission
    rw [hatt]
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hinv.inspected_evidence_consumed I J att hK hadmission
    · exact hinv.inspected_evidence_consumed I K att hK hadmission
  case bypass_mode_sound =>
    have hmonitor := ingest.guard_bypass_monitor hg
    have hmode := ingest.next_mode hn
    intro I J hJ
    rw [hmode]
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨hd, rfl⟩⟩
    · exact hinv.bypass_mode_sound I J hK
    · exact ⟨fun _ => hmonitor hd, fun _ => hmonitor hd⟩
  case quarantine_pending =>
    intro I J hJ hquarantined
    exact ⟨J, hJ, hquarantined⟩

/-- `invC` (3 crossing conjuncts): fully automated frame preservation. -/
theorem presC_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition) :
    Preserves (ingest a src pconf pinteg d : Kav.Action St!) invC := by
  intro s s' hinv _hg hn
  kav_discharge_lite ingest

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition) :
    Preserves (ingest a src pconf pinteg d : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_ingest a src pconf pinteg d s s' hinv hg hn,
     presP_ingest a src pconf pinteg d s s' hinv hg hn,
     presPP_ingest a src pconf pinteg d s s' hinv hg hn,
     presE_ingest a src pconf pinteg d s s' hinv hg hn,
     presC_ingest a src pconf pinteg d s s' hinv hg hn⟩

#print axioms pres_ingest

end Tzimtzum
