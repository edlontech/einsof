import Tzimtzum.Soundness.Common

/-! `settle_invocation` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- The pending-record fields settlement never changes. A contained post-record also came
from a contained pre-record; quarantine preserves disposition, while demotion makes the
post-record non-contained. -/
def samePendingCore
    (J K : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) : Prop :=
  J.agent = K.agent ∧ J.policy = K.policy ∧ J.egress = K.egress
  ∧ J.admission = K.admission ∧ J.authorized = K.authorized
  ∧ (contained J → contained K)

/-- `settleAt` either frames a record or changes only its quarantine flag. -/
theorem settleAt_pending_preimage
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (inv : InvocationId) (outcome : Outcome) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : settleAt p inv outcome I = some J) :
    ∃ K, p I = some K ∧ samePendingCore J K := by
  by_cases hI : I = inv
  · subst I
    cases outcome with
    | success => cases hp : p inv <;> simp [settleAt, hp] at hJ
    | failure => cases hp : p inv <;> simp [settleAt, hp] at hJ
    | ambiguous =>
        unfold settleAt at hJ
        cases hp : p inv with
        | none => simp [hp] at hJ
        | some K =>
            simp [hp] at hJ
            subst J
            exact ⟨K, rfl, by simp [samePendingCore, contained]⟩
  · rw [settleAt_other _ _ _ _ hI] at hJ
    exact ⟨J, hJ, by simp [samePendingCore]⟩

/-- Quarantine changes no disposition, so `settleAt` preserves containment for survivors. -/
theorem settleAt_pending_containment
    (p : InvocationId →
      Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest))
    (inv : InvocationId) (outcome : Outcome) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : settleAt p inv outcome I = some J) :
    ∃ K, p I = some K ∧ (contained J ↔ contained K) := by
  by_cases hI : I = inv
  · subst I
    cases outcome with
    | success => cases hp : p inv <;> simp [settleAt, hp] at hJ
    | failure => cases hp : p inv <;> simp [settleAt, hp] at hJ
    | ambiguous =>
        unfold settleAt at hJ
        cases hp : p inv with
        | none => simp [hp] at hJ
        | some K =>
            simp [hp] at hJ
            subst J
            exact ⟨K, rfl, by simp [contained]⟩
  · rw [settleAt_other _ _ _ _ hI] at hJ
    exact ⟨J, hJ, Iff.rfl⟩

/-- Every post-settlement pending record has a pre-state record with the same stable core. -/
theorem settle_pending_preimage (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s')
    (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) :
    ∃ K, s.pending I = some K ∧ samePendingCore J K := by
  obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
  rw [hpen] at hJ
  by_cases hd : dispo = Disposition.permitted
  · simp only [if_pos hd] at hJ
    exact settleAt_pending_preimage s.pending inv outcome I J hJ
  · simp only [if_neg hd] at hJ
    rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
      ⟨M, hM, -, hEq⟩ | ⟨hM, -⟩
    · rcases settleAt_pending_preimage s.pending inv outcome I M hM with ⟨K, hK, hcore⟩
      rcases hcore with ⟨hagent, hpolicy, hegress, hadmission, hauthorized, -⟩
      rw [hEq]
      exact ⟨K, hK, hagent, hpolicy, hegress, hadmission, hauthorized, by simp [contained]⟩
    · rcases settleAt_pending_preimage s.pending inv outcome I J hM with ⟨K, hK, hcore⟩
      exact ⟨K, hK, hcore⟩

/-- A contained settlement survivor owned by `a` can only come from the permitted arm. -/
theorem settle_contained_owner_permitted (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s')
    (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = a) :
    dispo = Disposition.permitted := by
  cases dispo with
  | permitted => rfl
  | blocked => kav_discharge_lite settle_invocation
  | monitor_bypassed =>
      obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, -, -⟩ := hn
      rw [hpen] at hJ
      have hd : Disposition.monitor_bypassed ≠ Disposition.permitted := by decide
      rw [if_neg hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, -, -, hEq⟩ | ⟨-, hOther⟩
      · rw [hEq] at hcontained
        simp [contained] at hcontained
      · exact (hOther howner).elim

/-- The unique source record and the guard-pinned settlement inputs. -/
theorem settlement_source (inv : InvocationId) (a : AgentId) (dispo : Disposition)
    (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s) :
    ∃ J, s.pending inv = some J ∧ a = J.agent ∧ dispo = J.disposition
      ∧ clvl = J.policy.output_conf ∧ ilvl = J.policy.output_integ := by
  obtain ⟨hexists, -, -, hpinned, -, -⟩ := hg
  rcases hexists with ⟨J, hJ⟩
  exact ⟨J, hJ, hpinned J hJ⟩

theorem presS_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') : invS s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kav_discharge_lite settle_invocation
  · kav_discharge_lite settle_invocation
  · kav_discharge_lite settle_invocation
  · kav_discharge_lite settle_invocation
  · kav_discharge_lite settle_invocation
  · kav_discharge_lite settle_invocation
  · kav_discharge_lite settle_invocation
  case refine_8 =>
    have hnext := hn
    have hguard := hg
    obtain ⟨-, ha, -, -, -, -⟩ := hguard
    obtain ⟨hact, -, -, ht, hi, -, hch, -, -, -, hgrants, -, -, -, -, -⟩ := hnext
    obtain ⟨⟨-, -, -, -, -, -, -, hrc, -⟩, -, -, -, -⟩ := hinv
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
      rcases hL with hL | ⟨-, heq, -⟩
      · exact hrt L hL
      · exact hne heq
    · intro L hL
      rw [hi] at hL
      rcases hL with hL | ⟨-, heq, -⟩
      · exact hri L hL
      · exact hne heq
    · intro I J hJ
      rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
        ⟨K, hK, hcore⟩
      intro hagentJ
      exact hrp I K hK (by rw [← hcore.1]; exact hagentJ)
    · intro I sc hsc
      rw [hch] at hsc
      exact hrch I sc hsc
    · intro D
      rw [hgrants]
      exact hrg D
  case refine_9 =>
    have hnext := hn
    obtain ⟨hact, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨⟨-, -, -, -, -, -, -, -, hpa⟩, -, -, -, -⟩ := hinv
    intro I J hJ
    rw [hact]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hcore⟩
    rw [hcore.1]
    exact hpa I K hK

theorem presP_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') : invP s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I J1 J2 hJ1 hJ2
    rw [hJ1] at hJ2
    exact Option.some.inj hJ2
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htool, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, hregistered, -, -, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [htool]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, -, hpolicy, -⟩
    rw [hpolicy]
    exact hregistered I K hK
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrootField⟩ := hnext
    obtain ⟨-, ⟨-, -, hroot, -, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [hrootField]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hagent, -⟩
    rw [hagent]
    exact hroot I K hK
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, hids, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, hused, -, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rw [hids]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, -⟩
    exact hused I K hK
  · obtain ⟨-, ⟨-, -, -, -, hegressInv, -, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, -, hpolicy, hegress, -⟩
    rw [hpolicy, hegress]
    exact hegressInv I K hK
  · obtain ⟨-, ⟨-, -, -, -, -, hcoherent, -, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, -, hpolicy, -⟩
    rw [hpolicy]
    exact hcoherent I K hK
  · have hnext := hn
    obtain ⟨-, -, hcap, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, hdeny, -, -, -, -, -⟩, -, -, -⟩ := hinv
    intro I J hJ hcontained
    rw [hcap]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hagent, hpolicy, -, -, hauthorized, hcontainedOld⟩
    obtain ⟨hauth, hcaps⟩ := hdeny I K hK (hcontainedOld hcontained)
    constructor
    · rw [hauthorized]
      exact hauth
    · intro C hC
      rw [hpolicy] at hC
      rw [hagent]
      exact hcaps C hC
  · have hnext := hn
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, hflow, -, -, -, -⟩, ⟨hpair, -⟩, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects vouched
    rw [hallow, hinspect]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hagent, -, hegress, hadmission, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hegress] at hE
      rw [hadmission]
      exact hflow L I K E hL hK hKcontained hE
    · have hd := settle_contained_owner_permitted inv a dispo outcome clvl ilvl att
        s s' hg hn I J hJ hcontained howner
      rcases settlement_source inv a dispo outcome clvl ilvl att s hg with
        ⟨R, hR, haR, hdispo, hconf, -⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hegress] at hE
      rw [hlevel, hconf, hadmission]
      exact hpair inv I R K E hR hK hsameAgent hRcontained hKcontained hE
  · have hnext := hn
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, hflow, -, -, -⟩, ⟨hpair, -⟩, -, -⟩ := hinv
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hagent, -, hegress, -, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hegress] at hE
      exact hflow L I K E hL hK hKcontained hE
    · have hd := settle_contained_owner_permitted inv a dispo outcome clvl ilvl att
        s s' hg hn I J hJ hcontained howner
      rcases settlement_source inv a dispo outcome clvl ilvl att s hg with
        ⟨R, hR, haR, hdispo, hconf, -⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hegress] at hE
      rw [hlevel, hconf]
      rcases hpair inv I R K E hR hK hsameAgent hRcontained hKcontained hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · have hnext := hn
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, hinteg, -, -⟩, ⟨-, hpair⟩, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    unfold vouched
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hagent, hpolicy, -, hadmission, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hpolicy, hadmission]
      exact hinteg L I K hL hK hKcontained
    · have hd := settle_contained_owner_permitted inv a dispo outcome clvl ilvl att
        s s' hg hn I J hJ hcontained howner
      rcases settlement_source inv a dispo outcome clvl ilvl att s hg with
        ⟨R, hR, haR, hdispo, -, hintegOut⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hlevel, hintegOut, hpolicy, hadmission]
      exact hpair inv I R K hR hK hsameAgent hRcontained hKcontained
  · have hnext := hn
    obtain ⟨-, -, -, -, hi, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hinteg, -⟩, ⟨-, hpair⟩, -, -⟩ := hinv
    intro L I J hL hJ hcontained
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hagent, hpolicy, -, -, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hpolicy]
      exact hinteg L I K hL hK hKcontained
    · have hd := settle_contained_owner_permitted inv a dispo outcome clvl ilvl att
        s s' hg hn I J hJ hcontained howner
      rcases settlement_source inv a dispo outcome clvl ilvl att s hg with
        ⟨R, hR, haR, hdispo, -, hintegOut⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hlevel, hintegOut, hpolicy]
      rcases hpair inv I R K hR hK hsameAgent hRcontained hKcontained with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · have hnext := hn
    obtain ⟨-, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hnext
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hclear⟩, -, -, -⟩ := hinv
    intro L I J hJ hcontained hspec
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, hagent, hpolicy, -, -, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [hpolicy]
    unfold speculative_taint_contained at hspec
    rcases hspec with hL | ⟨I2, M, hM, hMagent, hMcontained, hMlevel⟩
    · rw [ht] at hL
      rcases hL with hL | ⟨houtcome, howner, hlevel⟩
      · rw [hagent] at hL
        exact hclear L I K hK hKcontained (Or.inl hL)
      · have hd := settle_contained_owner_permitted inv a dispo outcome clvl ilvl att
          s s' hg hn I J hJ hcontained howner
        rcases settlement_source inv a dispo outcome clvl ilvl att s hg with
          ⟨R, hR, haR, hdispo, hconf, -⟩
        have hRcontained : contained R := by
          unfold contained
          rw [← hdispo, hd]
        have hsameAgent : R.agent = K.agent := by
          rw [← hagent, howner, haR]
        exact hclear L I K hK hKcontained
          (Or.inr ⟨inv, R, hR, hsameAgent, hRcontained,
            hconf.symm.trans hlevel.symm⟩)
    · rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I2 M hM with
        ⟨N, hN, hMagentN, hMpolicyN, -, -, -, hMcontainedOld⟩
      have hNcontained := hMcontainedOld hMcontained
      have hsameAgent : N.agent = K.agent := by
        rw [← hMagentN, hMagent, hagent]
      have houtput : N.policy.output_conf = L := by
        rw [← hMpolicyN]
        exact hMlevel
      exact hclear L I K hK hKcontained
        (Or.inr ⟨I2, N, hN, hsameAgent, hNcontained, houtput⟩)

theorem presPP_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (_hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') : invPP s' := by
  refine ⟨?_, ?_⟩
  · have hnext := hn
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hallow, hinspect, -, -⟩ := hnext
    obtain ⟨-, -, ⟨hflow, -⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects vouched
    rw [hallow, hinspect]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I1 J1 hJ1 with
      ⟨K1, hK1, hagent1, hpolicy1, -, hadmission1, -, hcontainedOld1⟩
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I2 J2 hJ2 with
      ⟨K2, hK2, hagent2, hpolicy2, hegress2, hadmission2, -, hcontainedOld2⟩
    have hsameAgent : K1.agent = K2.agent := by
      rw [← hagent1, hagent, hagent2]
    rw [hegress2] at hE
    rw [hpolicy1, hadmission2]
    exact hflow I1 I2 K1 K2 E hK1 hK2 hsameAgent
      (hcontainedOld1 hcontained1) (hcontainedOld2 hcontained2) hE
  · obtain ⟨-, -, ⟨-, hinteg⟩, -, -⟩ := hinv
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    unfold vouched
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I1 J1 hJ1 with
      ⟨K1, hK1, hagent1, hpolicy1, -, -, -, hcontainedOld1⟩
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I2 J2 hJ2 with
      ⟨K2, hK2, hagent2, hpolicy2, -, hadmission2, -, hcontainedOld2⟩
    have hsameAgent : K1.agent = K2.agent := by
      rw [← hagent1, hagent, hagent2]
    rw [hpolicy1, hpolicy2, hadmission2]
    exact hinteg I1 I2 K1 K2 hK1 hK2 hsameAgent
      (hcontainedOld1 hcontained1) (hcontainedOld2 hcontained2)

theorem presE_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') : invE s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnext := hn
    obtain ⟨hact, -, -, -, -, hpen, hch, hids, -, -, -, htool, -, -, -, hroot⟩ := hnext
    obtain ⟨-, -, -, ⟨hscope, -, -, -, -, -⟩, -⟩ := hinv
    rcases settlement_source inv a dispo outcome clvl ilvl att s hg with ⟨R, hR, -⟩
    intro I sc hsc
    rw [hch] at hsc
    obtain ⟨hpending, hid, hactive, hnonroot, hregistered, hcoherent, hnarrow, hcoverage⟩ :=
      hscope I sc hsc
    have hI : I ≠ inv := by
      intro heq
      subst I
      rw [hR] at hpending
      contradiction
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hnarrow, hcoverage⟩
    · rw [hpen]
      by_cases hd : dispo = Disposition.permitted
      · simpa only [if_pos hd, settleAt_other _ _ _ _ hI] using hpending
      · have hsettled : settleAt s.pending inv outcome I = none := by
          rw [settleAt_other _ _ _ _ hI]
          exact hpending
        simpa only [if_neg hd, demoteAllOf_eq_none] using hsettled
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
    intro I J evidence hJ hadmission
    rw [hatt]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, -, -, -, hadmissionCore, -⟩
    apply Or.inl
    apply hevidence I K evidence hK
    rw [← hadmissionCore]
    exact hadmission
  · have hnext := hn
    have hguard := hg
    obtain ⟨-, -, hnotBlocked, -, -, -⟩ := hguard
    obtain ⟨-, -, -, -, -, hpen, -, -, -, -, -, -, -, -, hmode, -⟩ := hnext
    obtain ⟨-, -, -, ⟨-, -, -, -, hbypass, -⟩, -⟩ := hinv
    rcases settlement_source inv a dispo outcome clvl ilvl att s hg with
      ⟨R, hR, -, hdispo, -, -⟩
    intro I J hJ
    rw [hmode]
    rcases settle_pending_preimage inv a dispo outcome clvl ilvl att s s' hn I J hJ with
      ⟨K, hK, -, -, -, hadmission, -, -⟩
    constructor
    · intro hnotContained
      by_cases hd : dispo = Disposition.permitted
      · have hpost : settleAt s.pending inv outcome I = some J := by
          rw [hpen] at hJ
          simpa only [if_pos hd] using hJ
        rcases settleAt_pending_containment s.pending inv outcome I J hpost with
          ⟨N, hN, hcontainedIff⟩
        exact (hbypass I N hN).1 (fun hNcontained => hnotContained (hcontainedIff.mpr hNcontained))
      · have hRnotContained : ¬ contained R := by
          intro hRcontained
          exact hd (hdispo.trans hRcontained)
        exact (hbypass inv R hR).1 hRnotContained
    · intro hAdmission
      exact (hbypass I K hK).2 (by rw [← hadmission]; exact hAdmission)
  · intro I J hJ hquarantined
    exact ⟨J, hJ, hquarantined⟩

theorem presC_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (_hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') : invC s' := by
  kav_discharge_lite settle_invocation

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId))
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s') : allInv s' :=
  ⟨presS_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
   presP_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
   presPP_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
   presE_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
   presC_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn⟩

#print axioms pres_settle_invocation

end Tzimtzum
