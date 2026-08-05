import Tzimtzum.Soundness.Common

/-! # Task 8 — `ingest` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- Every post-ingest pending record comes from the old map unchanged or with only its
`disposition` demoted. Keeping this frame fact explicit avoids unfolding the full invariant
bundle in every pending-record VC. -/
theorem ingest_pending_preimage (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hn : (ingest a src pconf pinteg d).next s s') (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) :
    ∃ K, s.pending I = some K
      ∧ (J = K ∨ (d = Disposition.monitor_bypassed
        ∧ J = { K with disposition := Disposition.monitor_bypassed })) := by
  obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
  rw [hpen] at hJ
  by_cases hd : d = Disposition.monitor_bypassed
  · simp only [if_pos hd] at hJ
    rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
      ⟨K, hK, -, hEq⟩ | ⟨hOld, -⟩
    · exact ⟨K, hK, Or.inr ⟨hd, hEq⟩⟩
    · exact ⟨J, hOld, Or.inl rfl⟩
  · exact ⟨J, by simpa only [if_neg hd] using hJ, Or.inl rfl⟩

/-- A contained post-ingest record cannot be one of the demoted records, so it is present
unchanged in the pre-state. -/
theorem ingest_contained_pending_preimage (a : AgentId) (src : Option AgentId)
    (pconf : ConfLevel) (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hn : (ingest a src pconf pinteg d).next s s') (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) (hcontained : contained J) : s.pending I = some J := by
  rcases ingest_pending_preimage a src pconf pinteg d s s' hn I J hJ with
    ⟨K, hK, rfl | ⟨-, hdemoted⟩⟩
  · exact hK
  · rw [hdemoted] at hcontained
    simp [contained] at hcontained

/-- A contained post-ingest record owned by the ingest target can only come from the
permitted arm; the monitor arm demotes every such record. -/
theorem ingest_contained_owner_permitted (a : AgentId) (src : Option AgentId)
    (pconf : ConfLevel) (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s') (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = a) :
    d = Disposition.permitted := by
  cases d with
  | permitted => rfl
  | blocked => kav_discharge_lite ingest
  | monitor_bypassed =>
      obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
      rw [hpen] at hJ
      simp only [if_pos rfl] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, -, -, hEq⟩ | ⟨-, hOther⟩
      · rw [hEq] at hcontained
        simp [contained] at hcontained
      · exact (hOther howner).elim

theorem presS_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s') : invS s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kav_discharge_lite ingest
  · kav_discharge_lite ingest
  · kav_discharge_lite ingest
  · kav_discharge_lite ingest
  · kav_discharge_lite ingest
  · kav_discharge_lite ingest
  · kav_discharge_lite ingest
  case refine_8 =>
    obtain ⟨hact, -, -, ht, hi, hpen, hch, -, -, -, hgrants, -, -, -, -, -⟩ := hn
    obtain ⟨⟨-, -, -, -, -, -, -, hrc, -⟩, -, -, -, -⟩ := hinv
    have ha : s.agent_active a := by kav_discharge_lite ingest
    intro A hA
    rw [hact] at hA
    have hne : A ≠ a := by
      intro heq
      subst A
      exact hA ha
    obtain ⟨hrt, hri, hrp, hrch, hrg⟩ := hrc A hA
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
  case refine_9 =>
    obtain ⟨hact, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
    obtain ⟨⟨-, -, -, -, -, -, -, -, hpa⟩, -, -, -, -⟩ := hinv
    intro I J hJ
    rw [hact]
    rw [hpen] at hJ
    by_cases hd : d = Disposition.monitor_bypassed
    · simp only [if_pos hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
      · exact hpa I K hK
      · exact hpa I J hK
    · have hOld : s.pending I = some J := by simpa only [if_neg hd] using hJ
      exact hpa I J hOld

theorem presP_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s') : invP s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kav_discharge_lite ingest
  · obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, htool, -, -, -, -⟩ := hn
    obtain ⟨-, ⟨-, hreg, -, -, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [htool]
    rw [hpen] at hJ
    by_cases hd : d = Disposition.monitor_bypassed
    · simp only [if_pos hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, hK, -, rfl⟩ | ⟨hK, -⟩
      · exact hreg I K hK
      · exact hreg I J hK
    · have hOld : s.pending I = some J := by simpa only [if_neg hd] using hJ
      exact hreg I J hOld
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrootField⟩ := hnext
    obtain ⟨-, ⟨-, -, hroot, -, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [hrootField]
    rcases ingest_pending_preimage a src pconf pinteg d s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hroot I J hK
    · exact hroot I K hK
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, hused, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [hids]
    rcases ingest_pending_preimage a src pconf pinteg d s s' hn I J hJ with
      ⟨K, hK, -⟩
    exact hused I K hK
  · obtain ⟨-, ⟨-, -, -, -, hegress, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rcases ingest_pending_preimage a src pconf pinteg d s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hegress I J hK
    · exact hegress I K hK
  · obtain ⟨-, ⟨-, -, -, -, -, hcoherent, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rcases ingest_pending_preimage a src pconf pinteg d s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hcoherent I J hK
    · exact hcoherent I K hK
  · have hnext := hn
    obtain ⟨-, -, hcap, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, hdeny, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ hcontained
    rw [hcap]
    exact hdeny I J
      (ingest_contained_pending_preimage a src pconf pinteg d s s' hn I J hJ hcontained)
      hcontained
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, hpermit, -, -⟩ := hguard
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, hflow, -, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld :=
      ingest_contained_pending_preimage a src pconf pinteg d s s' hn I J hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hflow L I J E hL hOld hcontained hE
    · subst L
      have hd :=
        ingest_contained_owner_permitted a src pconf pinteg d s s' hg hn I J hJ hcontained howner
      exact (hpermit hd).1 I J E hOld howner hE
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, hpermit, -, -⟩ := hguard
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, hflow, -, -, -⟩, -, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    have hOld :=
      ingest_contained_pending_preimage a src pconf pinteg d s s' hn I J hJ hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hflow L I J E hL hOld hcontained hE
    · subst L
      have hd :=
        ingest_contained_owner_permitted a src pconf pinteg d s s' hg hn I J hJ hcontained howner
      rcases (hpermit hd).1 I J E hOld howner hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, hpermit, -, -⟩ := hguard
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, hinteg, -, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    have hOld :=
      ingest_contained_pending_preimage a src pconf pinteg d s s' hn I J hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hinteg L I J hL hOld hcontained
    · subst L
      have hd :=
        ingest_contained_owner_permitted a src pconf pinteg d s s' hg hn I J hJ hcontained howner
      exact (hpermit hd).2.2 I J hOld howner
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, hpermit, -, -⟩ := hguard
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hinteg, -⟩, -, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    have hOld :=
      ingest_contained_pending_preimage a src pconf pinteg d s s' hn I J hJ hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨howner, hlevel⟩
    · exact hinteg L I J hL hOld hcontained
    · subst L
      have hd :=
        ingest_contained_owner_permitted a src pconf pinteg d s s' hg hn I J hJ hcontained howner
      rcases (hpermit hd).2.2 I J hOld howner with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, hpermit, -, -⟩ := hguard
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hclear⟩, -, -, -⟩ := hinv
    intro L I J hJ hcontained hspec
    have hOldJ :=
      ingest_contained_pending_preimage a src pconf pinteg d s s' hn I J hJ hcontained
    unfold speculative_taint_contained at hspec
    rcases hspec with hL | ⟨I2, K, hK, hagent, hKcontained, hlevel⟩
    · rw [ht] at hL
      rcases hL with hL | ⟨howner, hnew⟩
      · exact hclear L I J hOldJ hcontained (Or.inl hL)
      · subst L
        have hd :=
          ingest_contained_owner_permitted a src pconf pinteg d s s' hg hn I J hJ hcontained howner
        exact (hpermit hd).2.1 I J hOldJ howner
    · have hOldK :=
        ingest_contained_pending_preimage a src pconf pinteg d s s' hn I2 K hK hKcontained
      exact hclear L I J hOldJ hcontained
        (Or.inr ⟨I2, K, hOldK, hagent, hKcontained, hlevel⟩)

theorem presPP_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (_hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s') : invPP s' := by
  refine ⟨?_, ?_⟩
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, -, ⟨hflow, -⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    exact hflow I1 I2 J1 J2 E
      (ingest_contained_pending_preimage a src pconf pinteg d s s' hn I1 J1 hJ1 hcontained1)
      (ingest_contained_pending_preimage a src pconf pinteg d s s' hn I2 J2 hJ2 hcontained2)
      hagent hcontained1 hcontained2 hE
  · obtain ⟨-, -, ⟨-, hinteg⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    exact hinteg I1 I2 J1 J2
      (ingest_contained_pending_preimage a src pconf pinteg d s s' hn I1 J1 hJ1 hcontained1)
      (ingest_contained_pending_preimage a src pconf pinteg d s s' hn I2 J2 hJ2 hcontained2)
      hagent hcontained1 hcontained2

theorem presE_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s') : invE s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnext := hn
    obtain ⟨hact, -, -, -, -, hpen, hch, hids, -, -, -, htool, -, -, -, hroot⟩ := hnext
    obtain ⟨-, -, -, ⟨hscope, -, -, -, -, -⟩, -⟩ := hinv
    intro I sc hsc
    rw [hch] at hsc
    obtain ⟨hpending, hid, hactive, hnonroot, hregistered, hcoherent, hnarrow, hcoverage⟩ :=
      hscope I sc hsc
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
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, hch, -, -, -, -, -, -, -, hmode, -⟩ := hnext
    obtain ⟨-, -, -, ⟨-, henforce, -, -, -, -⟩, -⟩ := hinv
    intro I sc hsc
    rw [hmode]
    rw [hch] at hsc
    exact henforce I sc hsc
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, hch, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, ⟨-, -, hunique, -, -, -⟩, -⟩ := hinv
    intro I sc1 sc2 hsc1 hsc2
    rw [hch] at hsc1 hsc2
    exact hunique I sc1 sc2 hsc1 hsc2
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, hatt, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, -, -, ⟨-, -, -, hevidence, -, -⟩, -⟩ := hinv
    intro I J att hJ hadmission
    rw [hatt]
    rcases ingest_pending_preimage a src pconf pinteg d s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨-, rfl⟩⟩
    · exact hevidence I J att hK hadmission
    · exact hevidence I K att hK hadmission
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, -, -, -, hmonitor⟩ := hguard
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmode, -⟩ := hnext
    obtain ⟨-, -, -, ⟨-, -, -, -, hbypass, -⟩, -⟩ := hinv
    intro I J hJ
    rw [hmode]
    rcases ingest_pending_preimage a src pconf pinteg d s s' hn I J hJ with
      ⟨K, hK, rfl | ⟨hd, rfl⟩⟩
    · exact hbypass I J hK
    · exact ⟨fun _ => hmonitor hd, fun _ => hmonitor hd⟩
  · intro I J hJ hquarantined
    exact ⟨J, hJ, hquarantined⟩

theorem presC_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (_hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s') : invC s' := by
  kav_discharge_lite ingest

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_ingest (a : AgentId) (src : Option AgentId) (pconf : ConfLevel)
    (pinteg : IntegLevel) (d : Disposition)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (ingest a src pconf pinteg d).guard s)
    (hn : (ingest a src pconf pinteg d).next s s') : allInv s' :=
  ⟨presS_ingest a src pconf pinteg d s s' hinv hg hn,
   presP_ingest a src pconf pinteg d s s' hinv hg hn,
   presPP_ingest a src pconf pinteg d s s' hinv hg hn,
   presE_ingest a src pconf pinteg d s s' hinv hg hn,
   presC_ingest a src pconf pinteg d s s' hinv hg hn⟩

#print axioms pres_ingest

end Tzimtzum
