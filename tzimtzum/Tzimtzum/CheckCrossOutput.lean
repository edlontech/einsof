import Tzimtzum.Soundness.Common

/-! `cross_output` preserves the bundle (one theorem per sub-bundle).

The crossing update has three branches (endorsed release, unendorsed copy, fail) and may
demote the receiver. The manual bullets all follow one argument: a post-state pending
record is an old record unchanged or demoted (`pending_preimage`), a *contained* record is
always an old record (`contained_pending_preimage`), and a contained record owned by the
receiver forces the permitted arm (`contained_owner_permitted`) — whose `crossHolds` guard
payload (`contained_owner_holds`) then covers the released or copied labels, branch by
branch and arm by arm. Grants decrement by exactly one on the endorsed branch
(`decrement_grant_preimage`). Everything else is automated. -/

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

Built on the `kav_action`-generated projections (`next_pending`, `guard_permitted_holds`,
…): nothing in this file destructures the action's `guard`/`next` conjunctions
positionally. -/

section Inversion

variable {q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash}
  {branch : CrossBranch} {dispo : Disposition}
  {s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash}
  {I : InvocationId}
  {J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest}

/-- A post-crossing pending record is unchanged or differs only by receiver demotion. -/
private theorem pending_preimage (hn : (cross_output q branch dispo).next s s')
    (hJ : s'.pending I = some J) :
    ∃ K, s.pending I = some K
      ∧ (J = K ∨ (dispo = Disposition.monitor_bypassed
        ∧ J = { K with disposition := Disposition.monitor_bypassed })) := by
  rw [cross_output.next_pending hn] at hJ
  by_cases hd : dispo = Disposition.monitor_bypassed
  · simp only [if_pos hd] at hJ
    rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
      ⟨K, hK, -, hEq⟩ | ⟨hOld, -⟩
    · exact ⟨K, hK, Or.inr ⟨hd, hEq⟩⟩
    · exact ⟨J, hOld, Or.inl rfl⟩
  · exact ⟨J, by simpa only [if_neg hd] using hJ, Or.inl rfl⟩

/-- Containment excludes the demoted image, yielding an unchanged pre-state record. -/
private theorem contained_pending_preimage (hn : (cross_output q branch dispo).next s s')
    (hJ : s'.pending I = some J) (hcontained : contained J) : s.pending I = some J := by
  rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, hdemoted⟩⟩
  · exact hK
  · rw [hdemoted] at hcontained
    simp [contained] at hcontained

/-- A contained post-state record owned by the receiver implies the permitted arm. -/
private theorem contained_owner_permitted (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s')
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = q.rcv) :
    dispo = Disposition.permitted := by
  cases dispo with
  | permitted => rfl
  | blocked => exact (cross_output.guard_not_blocked hg rfl).elim
  | monitor_bypassed =>
      rw [cross_output.next_pending hn] at hJ
      simp only [if_pos rfl] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, -, -, hEq⟩ | ⟨-, hOther⟩
      · rw [hEq] at hcontained
        simp [contained] at hcontained
      · exact (hOther howner).elim

/-- The receiver's surviving contained permits force the permitted arm and its branch
holds. -/
private theorem contained_owner_holds (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s')
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = q.rcv) :
    crossHolds s q branch :=
  cross_output.guard_permitted_holds hg
    (contained_owner_permitted hg hn hJ hcontained howner)

end Inversion

/-! ## Preservation, one theorem per sub-bundle -/

/-- `invS` (9 structural conjuncts): automated except `revocation_clean` (only the active
receiver gains labels, and only its grant key decrements) and `pending_active` (record
owners are unchanged by demotion). -/
theorem presS_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition) :
    Preserves (cross_output q branch dispo : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  refine ⟨?root_always_active, ?parent_implies_active, ?single_parent, ?no_self_parent,
    ?root_no_parent, ?capability_subsumption, ?root_all_caps, ?revocation_clean,
    ?pending_active⟩
  case root_always_active => kav_discharge_lite cross_output
  case parent_implies_active => kav_discharge_lite cross_output
  case single_parent => kav_discharge_lite cross_output
  case no_self_parent => kav_discharge_lite cross_output
  case root_no_parent => kav_discharge_lite cross_output
  case capability_subsumption => kav_discharge_lite cross_output
  case root_all_caps => kav_discharge_lite cross_output
  case revocation_clean =>
    have hact := cross_output.next_agent_active hn
    have ht := cross_output.next_taint_levels hn
    have hi := cross_output.next_integ_levels hn
    have hpen := cross_output.next_pending hn
    have hch := cross_output.next_challenges hn
    have hgrants := cross_output.next_crossing_grants hn
    have hrcvActive := cross_output.guard_rcv_active hg
    intro A hA
    rw [hact] at hA
    have hne : A ≠ q.rcv := fun heq => hA (heq ▸ hrcvActive)
    obtain ⟨hrt, hri, hrp, hrch, hrg⟩ := hinv.revocation_clean A hA
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro L hL
      rw [ht] at hL
      rcases hL with hL | ⟨-, heq, -⟩ | ⟨-, heq, -⟩
      · exact hrt L hL
      · exact hne heq
      · exact hne heq
    · intro L hL
      rw [hi] at hL
      rcases hL with hL | ⟨-, heq, -⟩ | ⟨-, heq, -⟩
      · exact hri L hL
      · exact hne heq
      · exact hne heq
    · intro I J hJ
      rw [hpen] at hJ
      by_cases hd : dispo = Disposition.monitor_bypassed
      · simp only [if_pos hd] at hJ
        rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
          ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
        · exact hrp I K hK
        · exact hrp I J hK
      · exact hrp I J (by simpa only [if_neg hd] using hJ)
    · intro I sc hsc
      rw [hch] at hsc
      exact hrch I sc hsc
    · intro D
      rw [hgrants]
      by_cases hb : branch = CrossBranch.endorsed
      · simp only [if_pos hb]
        simpa only [decrementGrantAt_other s.crossing_grants q.rcv A q.assignment D
          (fun hEq => hne hEq.1)] using hrg D
      · simpa only [if_neg hb] using hrg D
  case pending_active =>
    have hact := cross_output.next_agent_active hn
    intro I J hJ
    rw [hact]
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hinv.pending_active I J hK
    · exact hinv.pending_active I K hK

/-- `invP` (12 pending/gate conjuncts). `pending_unique` is automated. The rest are
manual: registry/identifier/ceiling facts route each record through `pending_preimage`,
and the five confinement conjuncts split three ways on the constrained label — old (the
pre-state invariant), endorsed release, or unendorsed copy (each covered by the matching
arm of the receiver's `crossHolds` payload via `contained_owner_holds`). -/
theorem presP_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition) :
    Preserves (cross_output q branch dispo : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  refine ⟨?pending_unique, ?pending_registered, ?root_no_pending, ?pending_ids_consumed,
    ?pending_egress_attested, ?pending_snapshot_coherent, ?default_deny, ?flow_confinement,
    ?flow_confinement_weak, ?integrity_confinement, ?integrity_confinement_weak,
    ?clearance_confinement⟩
  case pending_unique => kav_discharge_lite cross_output
  case pending_registered =>
    have hpen := cross_output.next_pending hn
    have htool := cross_output.next_tool_registered hn
    intro I J hJ
    rw [htool]
    rw [hpen] at hJ
    by_cases hd : dispo = Disposition.monitor_bypassed
    · simp only [if_pos hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
      · exact hinv.pending_registered I K hK
      · exact hinv.pending_registered I J hK
    · exact hinv.pending_registered I J (by simpa only [if_neg hd] using hJ)
  case root_no_pending =>
    have hroot := cross_output.next_root_agent hn
    intro I J hJ
    rw [hroot]
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hinv.root_no_pending I J hK
    · exact hinv.root_no_pending I K hK
  case pending_ids_consumed =>
    have hids := cross_output.next_consumed_ids hn
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
    have hcap := cross_output.next_agent_cap hn
    intro I J hJ hcontained
    rw [hcap]
    exact hinv.default_deny I J (contained_pending_preimage hn hJ hcontained) hcontained
  case flow_confinement =>
    have ht := cross_output.next_taint_levels hn
    have hallow := cross_output.next_egress_allow_ceiling hn
    have hinspect := cross_output.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hinv.flow_confinement L I J E hL hOld hcontained hE
    · exact (contained_owner_holds hg hn hJ hcontained howner).endorsed hb
        |>.conf I J E hOld howner hE
    · exact (contained_owner_holds hg hn hJ hcontained howner).unendorsed hb
        |>.1 L hsrc |>.1 I J E hOld howner hE
  case flow_confinement_weak =>
    have ht := cross_output.next_taint_levels hn
    have hallow := cross_output.next_egress_allow_ceiling hn
    have hinspect := cross_output.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hinv.flow_confinement_weak L I J E hL hOld hcontained hE
    · rcases (contained_owner_holds hg hn hJ hcontained howner).endorsed hb
          |>.conf I J E hOld howner hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases (contained_owner_holds hg hn hJ hcontained howner).unendorsed hb
          |>.1 L hsrc |>.1 I J E hOld howner hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  case integrity_confinement =>
    have hi := cross_output.next_integ_levels hn
    intro L I J hL hJ hcontained
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hinv.integrity_confinement L I J hL hOld hcontained
    · exact (contained_owner_holds hg hn hJ hcontained howner).endorsed hb
        |>.integ I J hOld howner
    · exact (contained_owner_holds hg hn hJ hcontained howner).unendorsed hb
        |>.2 L hsrc I J hOld howner
  case integrity_confinement_weak =>
    have hi := cross_output.next_integ_levels hn
    intro L I J hL hJ hcontained
    have hOld := contained_pending_preimage hn hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hinv.integrity_confinement_weak L I J hL hOld hcontained
    · rcases (contained_owner_holds hg hn hJ hcontained howner).endorsed hb
          |>.integ I J hOld howner with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases (contained_owner_holds hg hn hJ hcontained howner).unendorsed hb
          |>.2 L hsrc I J hOld howner with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  case clearance_confinement =>
    have ht := cross_output.next_taint_levels hn
    intro L I J hJ hcontained hspec
    have hOldJ := contained_pending_preimage hn hJ hcontained
    unfold speculative_taint_contained at hspec
    rcases hspec with hL | ⟨I2, K, hK, hagent, hKcontained, hlevel⟩
    · rw [ht] at hL
      rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
      · exact hinv.clearance_confinement L I J hOldJ hcontained (Or.inl hL)
      · exact (contained_owner_holds hg hn hJ hcontained howner).endorsed hb
          |>.clear I J hOldJ howner
      · exact (contained_owner_holds hg hn hJ hcontained howner).unendorsed hb
          |>.1 L hsrc |>.2 I J hOldJ howner
    · have hOldK := contained_pending_preimage hn hK hKcontained
      exact hinv.clearance_confinement L I J hOldJ hcontained
        (Or.inr ⟨I2, K, hOldK, hagent, hKcontained, hlevel⟩)

/-- `invPP` (2 pairwise conjuncts), both manual: contained records are pre-existing
(`contained_pending_preimage`) and the flow relations are framed, so both conjuncts defer
to the pre-state invariant. -/
theorem presPP_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition) :
    Preserves (cross_output q branch dispo : Kav.Action St!) invPP := by
  intro s s' hinv _hg hn
  refine ⟨?pending_flow_compat, ?pending_integ_compat⟩
  case pending_flow_compat =>
    have hallow := cross_output.next_egress_allow_ceiling hn
    have hinspect := cross_output.next_egress_inspect_ceiling hn
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
theorem presE_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition) :
    Preserves (cross_output q branch dispo : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  refine ⟨?challenge_scoped, ?challenges_enforce_only, ?challenge_unique,
    ?inspected_evidence_consumed, ?bypass_mode_sound, ?quarantine_pending⟩
  case challenge_scoped =>
    have hact := cross_output.next_agent_active hn
    have hpen := cross_output.next_pending hn
    have hch := cross_output.next_challenges hn
    have hids := cross_output.next_consumed_ids hn
    have htool := cross_output.next_tool_registered hn
    have hroot := cross_output.next_root_agent hn
    intro I sc hsc
    rw [hch] at hsc
    obtain ⟨hpending, hid, hactive, hnonroot, hregistered, hcoherent, hnarrow, hcoverage⟩ :=
      hinv.challenge_scoped I sc hsc
    refine ⟨?_, ?_, ?_, ?_, ?_, hcoherent, hnarrow, hcoverage⟩
    · rw [hpen]
      by_cases hd : dispo = Disposition.monitor_bypassed
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
  case challenges_enforce_only =>
    have hch := cross_output.next_challenges hn
    have hmode := cross_output.next_mode hn
    intro I sc hsc
    rw [hmode]
    rw [hch] at hsc
    exact hinv.challenges_enforce_only I sc hsc
  case challenge_unique =>
    have hch := cross_output.next_challenges hn
    intro I sc1 sc2 hsc1 hsc2
    rw [hch] at hsc1 hsc2
    exact hinv.challenge_unique I sc1 sc2 hsc1 hsc2
  case inspected_evidence_consumed =>
    have hatt := cross_output.next_consumed_attestations hn
    intro I J att hJ hadmission
    rw [hatt]
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact Or.inl (hinv.inspected_evidence_consumed I J att hK hadmission)
    · exact Or.inl (hinv.inspected_evidence_consumed I K att hK hadmission)
  case bypass_mode_sound =>
    have hmonitor := cross_output.guard_bypass_hold_failed hg
    have hmode := cross_output.next_mode hn
    intro I J hJ
    rw [hmode]
    rcases pending_preimage hn hJ with ⟨K, hK, rfl | ⟨hd, rfl⟩⟩
    · exact hinv.bypass_mode_sound I J hK
    · exact ⟨fun _ => (hmonitor hd).2, fun _ => (hmonitor hd).2⟩
  case quarantine_pending =>
    intro I J hJ hquarantined
    exact ⟨J, hJ, hquarantined⟩

/-- A decremented grant is either the updated target grant or an unchanged other key. -/
theorem decrement_grant_preimage
    (g : AgentId → AssignmentDigest → Option CrossingGrant) (a A : AgentId)
    (d D : AssignmentDigest) (out : CrossingGrant)
    (h : decrementGrantAt g a d A D = some out) :
    (∃ old, A = a ∧ D = d ∧ g A D = some old
      ∧ out = { old with remaining := old.remaining - 1 })
    ∨ (¬ (A = a ∧ D = d) ∧ g A D = some out) := by
  unfold decrementGrantAt at h
  by_cases hkey : A = a ∧ D = d
  · rcases hkey with ⟨rfl, rfl⟩
    left
    cases hOld : g A D with
    | none => simp [hOld] at h
    | some old =>
        have hself : A = A ∧ D = D := ⟨rfl, rfl⟩
        simp only [if_pos hself, hOld] at h
        exact ⟨old, rfl, rfl, rfl, Option.some.inj h.symm⟩
  · right
    exact ⟨hkey, by simpa only [if_neg hkey] using h⟩

/-- `invC` (3 crossing conjuncts), manual: the endorsed branch decrements the receiver's
grant by one (`decrement_grant_preimage` keeps it bounded and its holder active); every
other key and branch is a frame; pinning is immediate from map functionality. -/
theorem presC_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition) :
    Preserves (cross_output q branch dispo : Kav.Action St!) invC := by
  intro s s' hinv hg hn
  refine ⟨?grant_bounded, ?grant_active, ?grant_pinned⟩
  case grant_bounded =>
    have hgrants := cross_output.next_crossing_grants hn
    intro A D out hOut
    rw [hgrants] at hOut
    by_cases hb : branch = CrossBranch.endorsed
    · simp only [if_pos hb] at hOut
      rcases decrement_grant_preimage s.crossing_grants q.rcv A q.assignment D out hOut with
        ⟨old, -, -, hOld, rfl⟩ | ⟨-, hOld⟩
      · have hbound := hinv.grant_bounded A D old hOld
        simp only
        omega
      · exact hinv.grant_bounded A D out hOld
    · exact hinv.grant_bounded A D out (by simpa only [if_neg hb] using hOut)
  case grant_active =>
    have hrcvActive := cross_output.guard_rcv_active hg
    have hact := cross_output.next_agent_active hn
    have hgrants := cross_output.next_crossing_grants hn
    intro A D out hOut
    rw [hact]
    rw [hgrants] at hOut
    by_cases hb : branch = CrossBranch.endorsed
    · simp only [if_pos hb] at hOut
      rcases decrement_grant_preimage s.crossing_grants q.rcv A q.assignment D out hOut with
        ⟨old, hA, -, -, -⟩ | ⟨-, hOld⟩
      · simpa only [hA] using hrcvActive
      · exact hinv.grant_active A D out hOld
    · exact hinv.grant_active A D out (by simpa only [if_neg hb] using hOut)
  case grant_pinned =>
    intro A D g1 g2 h1 h2
    exact Option.some.inj (h1.symm.trans h2)

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition) :
    Preserves (cross_output q branch dispo : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_cross_output q branch dispo s s' hinv hg hn,
     presP_cross_output q branch dispo s s' hinv hg hn,
     presPP_cross_output q branch dispo s s' hinv hg hn,
     presE_cross_output q branch dispo s s' hinv hg hn,
     presC_cross_output q branch dispo s s' hinv hg hn⟩

#print axioms pres_cross_output

end Tzimtzum
