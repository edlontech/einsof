import Tzimtzum.Soundness.Common

/-!
# Task 10 — `cross_output` preserves the bundle

The crossing update combines three branch shapes with optional receiver demotion. Broad
cascades saturate on the semantic confinement VCs, so this module keeps the framed VCs on
the shared cascades and proves the label/pending/grant obligations through small preimage
and branch arguments, following `CheckIngest`.
-/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- A post-crossing pending record is unchanged or differs only by receiver demotion. -/
theorem cross_pending_preimage
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hn : (cross_output q branch dispo).next s s') (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) :
    ∃ K, s.pending I = some K
      ∧ (J = K ∨ (dispo = Disposition.monitor_bypassed
        ∧ J = { K with disposition := Disposition.monitor_bypassed })) := by
  obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
  rw [hpen] at hJ
  by_cases hd : dispo = Disposition.monitor_bypassed
  · simp only [if_pos hd] at hJ
    rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
      ⟨K, hK, -, hEq⟩ | ⟨hOld, -⟩
    · exact ⟨K, hK, Or.inr ⟨hd, hEq⟩⟩
    · exact ⟨J, hOld, Or.inl rfl⟩
  · exact ⟨J, by simpa only [if_neg hd] using hJ, Or.inl rfl⟩

/-- Containment excludes the demoted image, yielding an unchanged pre-state record. -/
theorem cross_contained_pending_preimage
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hn : (cross_output q branch dispo).next s s') (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) (hcontained : contained J) : s.pending I = some J := by
  rcases cross_pending_preimage q branch dispo s s' hn I J hJ with
    ⟨K, hK, rfl | ⟨-, hdemoted⟩⟩
  · exact hK
  · rw [hdemoted] at hcontained
    simp [contained] at hcontained

/-- A contained post-state record owned by the receiver implies the permitted arm. -/
theorem cross_contained_owner_permitted
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = q.rcv) :
    dispo = Disposition.permitted := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnotBlocked, -, -⟩ := hg
  cases dispo with
  | permitted => rfl
  | blocked => exact (hnotBlocked rfl).elim
  | monitor_bypassed =>
      obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
      rw [hpen] at hJ
      simp only [if_pos rfl] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, -, -, hEq⟩ | ⟨-, hOther⟩
      · rw [hEq] at hcontained
        simp [contained] at hcontained
      · exact (hOther howner).elim

theorem presS_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') : invS s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kav_discharge_lite cross_output
  · kav_discharge_lite cross_output
  · kav_discharge_lite cross_output
  · kav_discharge_lite cross_output
  · kav_discharge_lite cross_output
  · kav_discharge_lite cross_output
  · kav_discharge_lite cross_output
  · obtain ⟨hact, -, -, ht, hi, hpen, hch, -, -, -, hgrants, -, -, -, -, -⟩ := hn
    obtain ⟨⟨-, -, -, -, -, -, -, hclean, -⟩, -, -, -, -⟩ := hinv
    obtain ⟨-, hrcvActive, -, -, -, -, -, -, -, -, -, -, -⟩ := hg
    intro A hA
    rw [hact] at hA
    have hne : A ≠ q.rcv := fun heq => hA (heq ▸ hrcvActive)
    obtain ⟨hrt, hri, hrp, hrch, hrg⟩ := hclean A hA
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
  · have hnext := hn
    obtain ⟨hact, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨⟨-, -, -, -, -, -, -, -, hactive⟩, -, -, -, -⟩ := hinv
    intro I J hJ
    rw [hact]
    rcases cross_pending_preimage q branch dispo s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hactive I J hK
    · exact hactive I K hK

/-- The receiver's surviving contained permits force the permitted arm and its branch holds. -/
theorem cross_contained_owner_holds
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = q.rcv) :
    crossHolds s q branch := by
  have hguard := hg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpermitted, -⟩ := hguard
  exact hpermitted
    (cross_contained_owner_permitted q branch dispo s s' hg hn I J hJ hcontained howner)

theorem presP_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') : invP s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kav_discharge_lite cross_output
  · obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, htool, -, -, -, -⟩ := hn
    obtain ⟨-, ⟨-, hregistered, -, -, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [htool]
    rw [hpen] at hJ
    by_cases hd : dispo = Disposition.monitor_bypassed
    · simp only [if_pos hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
      · exact hregistered I K hK
      · exact hregistered I J hK
    · exact hregistered I J (by simpa only [if_neg hd] using hJ)
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hroot⟩ := hnext
    obtain ⟨-, ⟨-, -, hrootPending, -, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [hroot]
    rcases cross_pending_preimage q branch dispo s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hrootPending I J hK
    · exact hrootPending I K hK
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, hused, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [hids]
    rcases cross_pending_preimage q branch dispo s s' hn I J hJ with ⟨K, hK, -⟩
    exact hused I K hK
  · obtain ⟨-, ⟨-, -, -, -, hegress, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rcases cross_pending_preimage q branch dispo s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hegress I J hK
    · exact hegress I K hK
  · obtain ⟨-, ⟨-, -, -, -, -, hcoherent, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rcases cross_pending_preimage q branch dispo s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hcoherent I J hK
    · exact hcoherent I K hK
  · have hnext := hn
    obtain ⟨-, -, hcap, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, hdeny, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ hcontained
    rw [hcap]
    exact hdeny I J
      (cross_contained_pending_preimage q branch dispo s s' hn I J hJ hcontained)
      hcontained
  · have hnext := hn
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, hflow, -, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld := cross_contained_pending_preimage q branch dispo s s' hn I J hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hflow L I J E hL hOld hcontained hE
    · exact (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
        howner).1 hb |>.1 I J E hOld howner hE
    · exact (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
        howner).2 hb |>.1 L hsrc |>.1 I J E hOld howner hE
  · have hnext := hn
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, hflow, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld := cross_contained_pending_preimage q branch dispo s s' hn I J hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hflow L I J E hL hOld hcontained hE
    · rcases (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
          howner).1 hb |>.1 I J E hOld howner hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
          howner).2 hb |>.1 L hsrc |>.1 I J E hOld howner hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · have hnext := hn
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, hinteg, -, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    have hOld := cross_contained_pending_preimage q branch dispo s s' hn I J hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hinteg L I J hL hOld hcontained
    · exact (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
        howner).1 hb |>.2.2 I J hOld howner
    · exact (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
        howner).2 hb |>.2 L hsrc I J hOld howner
  · have hnext := hn
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hinteg, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    have hOld := cross_contained_pending_preimage q branch dispo s s' hn I J hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
    · exact hinteg L I J hL hOld hcontained
    · rcases (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
          howner).1 hb |>.2.2 I J hOld howner with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
          howner).2 hb |>.2 L hsrc I J hOld howner with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · have hnext := hn
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hclear⟩, -, -, -⟩ := hinv
    intro L I J hJ hcontained hspec
    have hOldJ := cross_contained_pending_preimage q branch dispo s s' hn I J hJ hcontained
    unfold speculative_taint_contained at hspec
    rcases hspec with hL | ⟨I2, K, hK, hagent, hKcontained, hlevel⟩
    · rw [ht] at hL
      rcases hL with hL | ⟨hb, howner, rfl⟩ | ⟨hb, howner, hsrc⟩
      · exact hclear L I J hOldJ hcontained (Or.inl hL)
      · exact (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
          howner).1 hb |>.2.1 I J hOldJ howner
      · exact (cross_contained_owner_holds q branch dispo s s' hg hn I J hJ hcontained
          howner).2 hb |>.1 L hsrc |>.2 I J hOldJ howner
    · have hOldK :=
        cross_contained_pending_preimage q branch dispo s s' hn I2 K hK hKcontained
      exact hclear L I J hOldJ hcontained
        (Or.inr ⟨I2, K, hOldK, hagent, hKcontained, hlevel⟩)

theorem presPP_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (_hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') : invPP s' := by
  refine ⟨?_, ?_⟩
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, -, ⟨hflow, -⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    exact hflow I1 I2 J1 J2 E
      (cross_contained_pending_preimage q branch dispo s s' hn I1 J1 hJ1 hcontained1)
      (cross_contained_pending_preimage q branch dispo s s' hn I2 J2 hJ2 hcontained2)
      hagent hcontained1 hcontained2 hE
  · obtain ⟨-, -, ⟨-, hinteg⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    exact hinteg I1 I2 J1 J2
      (cross_contained_pending_preimage q branch dispo s s' hn I1 J1 hJ1 hcontained1)
      (cross_contained_pending_preimage q branch dispo s s' hn I2 J2 hJ2 hcontained2)
      hagent hcontained1 hcontained2

theorem presE_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') : invE s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnext := hn
    obtain ⟨hact, -, -, -, -, hpen, hch, hids, -, -, -, htool, -, -, -, hroot⟩ := hnext
    obtain ⟨-, -, -, ⟨hscope, -, -, -, -, -⟩, -⟩ := hinv
    intro I sc hsc
    rw [hch] at hsc
    obtain ⟨hpending, hid, hactive, hnonroot, hregistered, hcoherent, hnarrow, hcoverage⟩ :=
      hscope I sc hsc
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
  · obtain ⟨-, -, -, -, -, -, hch, -, -, -, -, -, -, -, hmode, -⟩ := hn
    obtain ⟨-, -, -, ⟨-, henforce, -, -, -, -⟩, -⟩ := hinv
    intro I sc hsc
    rw [hmode]
    rw [hch] at hsc
    exact henforce I sc hsc
  · obtain ⟨-, -, -, -, -, -, hch, -, -, -, -, -, -, -, -, -⟩ := hn
    obtain ⟨-, -, -, ⟨-, -, hunique, -, -, -⟩, -⟩ := hinv
    intro I sc1 sc2 hsc1 hsc2
    rw [hch] at hsc1 hsc2
    exact hunique I sc1 sc2 hsc1 hsc2
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, hatt, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, ⟨-, -, -, hevidence, -, -⟩, -⟩ := hinv
    intro I J att hJ hadmission
    rw [hatt]
    rcases cross_pending_preimage q branch dispo s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact Or.inl (hevidence I J att hK hadmission)
    · exact Or.inl (hevidence I K att hK hadmission)
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmonitor⟩ := hguard
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmode, -⟩ := hnext
    obtain ⟨-, -, -, ⟨-, -, -, -, hbypass, -⟩, -⟩ := hinv
    intro I J hJ
    rw [hmode]
    rcases cross_pending_preimage q branch dispo s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨hd, rfl⟩⟩
    · exact hbypass I J hK
    · exact ⟨fun _ => (hmonitor hd).2, fun _ => (hmonitor hd).2⟩
  · intro I J hJ hquarantined
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

theorem presC_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') : invC s' := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
    obtain ⟨-, -, -, -, hbounded, -, -⟩ := hinv
    intro A D out hOut
    rw [hgrants] at hOut
    by_cases hb : branch = CrossBranch.endorsed
    · simp only [if_pos hb] at hOut
      rcases decrement_grant_preimage s.crossing_grants q.rcv A q.assignment D out hOut with
        ⟨old, -, -, hOld, rfl⟩ | ⟨-, hOld⟩
      · have hbound := hbounded A D old hOld
        simp only
        omega
      · exact hbounded A D out hOld
    · exact hbounded A D out (by simpa only [if_neg hb] using hOut)
  · have hguard := hg
    obtain ⟨-, hrcvActive, -, -, -, -, -, -, -, -, -, -, -⟩ := hguard
    obtain ⟨-, -, -, -, -, hactive, -⟩ := hinv
    obtain ⟨hact, -, -, -, -, -, -, -, -, -, hgrants, -, -, -, -, -⟩ := hn
    intro A D out hOut
    rw [hact]
    rw [hgrants] at hOut
    by_cases hb : branch = CrossBranch.endorsed
    · simp only [if_pos hb] at hOut
      rcases decrement_grant_preimage s.crossing_grants q.rcv A q.assignment D out hOut with
        ⟨old, hA, -, -, -⟩ | ⟨-, hOld⟩
      · simpa only [hA] using hrcvActive
      · exact hactive A D out hOld
    · exact hactive A D out (by simpa only [if_neg hb] using hOut)
  · intro A D g1 g2 h1 h2
    exact Option.some.inj (h1.symm.trans h2)

/-- The full-bundle preservation lemma consumed by Tasks 11+ and the soundness assembly. -/
theorem pres_cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (cross_output q branch dispo).guard s)
    (hn : (cross_output q branch dispo).next s s') : allInv s' :=
  ⟨presS_cross_output q branch dispo s s' hinv hg hn,
   presP_cross_output q branch dispo s s' hinv hg hn,
   presPP_cross_output q branch dispo s s' hinv hg hn,
   presE_cross_output q branch dispo s s' hinv hg hn,
   presC_cross_output q branch dispo s s' hinv hg hn⟩

#print axioms pres_cross_output

end Tzimtzum
