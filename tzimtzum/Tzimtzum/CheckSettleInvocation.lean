import Tzimtzum.Soundness.Common

/-! `settle_invocation` preserves the bundle (one theorem per sub-bundle).

Settlement removes or quarantines the settled record and absorbs its frozen provenance
pair into the owner's labels; the monitor arm additionally demotes the owner's records.
The manual bullets all follow one argument: every survivor has a pre-state record with
the same stable core (`pending_preimage` via `samePendingCore`), a contained survivor
owned by the settling agent forces the permitted arm (`contained_owner_permitted`), and
the absorbed pair is exactly the guard-pinned output provenance of the unique settled
record (`settlement_source`) — so the pairwise pre-state invariants cover the new labels.
Everything else is automated. -/

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

/-- The pending-record fields settlement never changes. A contained post-record also came
from a contained pre-record; quarantine preserves disposition, while demotion makes the
post-record non-contained. -/
def samePendingCore
    (J K : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) :
    Prop :=
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

/-! ## Inversion helpers

Built on the `kav_action`-generated projections (`next_pending`, `guard_record_pinned`, …):
nothing in this file destructures the action's `guard`/`next` conjunctions positionally. -/

section Inversion

variable {inv : InvocationId} {a : AgentId} {dispo : Disposition} {outcome : Outcome}
  {clvl : ConfLevel} {ilvl : IntegLevel}
  {att : Option (ResolutionAttestation InvocationId AttestationId)}
  {s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash}
  {I : InvocationId}
  {J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest}

/-- Every post-settlement pending record has a pre-state record with the same stable core. -/
private theorem pending_preimage
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s')
    (hJ : s'.pending I = some J) :
    ∃ K, s.pending I = some K ∧ samePendingCore J K := by
  rw [settle_invocation.next_pending hn] at hJ
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
private theorem contained_owner_permitted
    (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s)
    (hn : (settle_invocation inv a dispo outcome clvl ilvl att).next s s')
    (hJ : s'.pending I = some J) (hcontained : contained J) (howner : J.agent = a) :
    dispo = Disposition.permitted := by
  cases dispo with
  | permitted => rfl
  | blocked => kav_discharge_lite settle_invocation
  | monitor_bypassed =>
      rw [settle_invocation.next_pending hn] at hJ
      have hd : Disposition.monitor_bypassed ≠ Disposition.permitted := by decide
      rw [if_neg hd] at hJ
      rcases (demoteAllOf_eq_some _ _ _ _ |>.mp hJ) with
        ⟨K, -, -, hEq⟩ | ⟨-, hOther⟩
      · rw [hEq] at hcontained
        simp [contained] at hcontained
      · exact (hOther howner).elim

/-- The unique source record and the guard-pinned settlement inputs. -/
private theorem settlement_source
    (hg : (settle_invocation inv a dispo outcome clvl ilvl att).guard s) :
    ∃ J, s.pending inv = some J ∧ a = J.agent ∧ dispo = J.disposition
      ∧ clvl = J.policy.output_conf ∧ ilvl = J.policy.output_integ := by
  rcases settle_invocation.guard_pending_exists hg with ⟨J, hJ⟩
  exact ⟨J, hJ, settle_invocation.guard_record_pinned hg J hJ⟩

end Inversion

/-! ## Preservation, one theorem per sub-bundle -/

/-- `invS` (9 structural conjuncts): automated except `revocation_clean` (only the active
settling agent gains labels, and survivors keep their owner) and `pending_active`
(survivor cores are stable). -/
theorem presS_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId)) :
    Preserves (settle_invocation inv a dispo outcome clvl ilvl att : Kav.Action St!)
      invS := by
  intro s s' hinv hg hn
  refine ⟨?root_always_active, ?parent_implies_active, ?single_parent, ?no_self_parent,
    ?root_no_parent, ?capability_subsumption, ?root_all_caps, ?revocation_clean,
    ?pending_active⟩
  case root_always_active => kav_discharge_lite settle_invocation
  case parent_implies_active => kav_discharge_lite settle_invocation
  case single_parent => kav_discharge_lite settle_invocation
  case no_self_parent => kav_discharge_lite settle_invocation
  case root_no_parent => kav_discharge_lite settle_invocation
  case capability_subsumption => kav_discharge_lite settle_invocation
  case root_all_caps => kav_discharge_lite settle_invocation
  case revocation_clean =>
    have ha := settle_invocation.guard_active hg
    have hact := settle_invocation.next_agent_active hn
    have ht := settle_invocation.next_taint_levels hn
    have hi := settle_invocation.next_integ_levels hn
    have hch := settle_invocation.next_challenges hn
    have hgrants := settle_invocation.next_crossing_grants hn
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
      rcases hL with hL | ⟨-, heq, -⟩
      · exact hrt L hL
      · exact hne heq
    · intro L hL
      rw [hi] at hL
      rcases hL with hL | ⟨-, heq, -⟩
      · exact hri L hL
      · exact hne heq
    · intro I J hJ
      rcases pending_preimage hn hJ with ⟨K, hK, hcore⟩
      intro hagentJ
      exact hrp I K hK (by rw [← hcore.1]; exact hagentJ)
    · intro I sc hsc
      rw [hch] at hsc
      exact hrch I sc hsc
    · intro D
      rw [hgrants]
      exact hrg D
  case pending_active =>
    have hact := settle_invocation.next_agent_active hn
    intro I J hJ
    rw [hact]
    rcases pending_preimage hn hJ with ⟨K, hK, hcore⟩
    rw [hcore.1]
    exact hinv.pending_active I K hK

/-- `invP` (12 pending/gate conjuncts). `pending_unique` is immediate. Registry,
identifier, and gate facts route each survivor through `pending_preimage`; the five
confinement conjuncts additionally split on whether the constrained label is old or the
newly absorbed provenance pair — the latter is covered by the pairwise pre-state
invariants against the guard-pinned settled record (`settlement_source`, forced onto the
permitted arm by `contained_owner_permitted`). -/
theorem presP_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId)) :
    Preserves (settle_invocation inv a dispo outcome clvl ilvl att : Kav.Action St!)
      invP := by
  intro s s' hinv hg hn
  refine ⟨?pending_unique, ?pending_registered, ?root_no_pending, ?pending_ids_consumed,
    ?pending_egress_attested, ?pending_snapshot_coherent, ?default_deny, ?flow_confinement,
    ?flow_confinement_weak, ?integrity_confinement, ?integrity_confinement_weak,
    ?clearance_confinement⟩
  case pending_unique =>
    intro I J1 J2 hJ1 hJ2
    rw [hJ1] at hJ2
    exact Option.some.inj hJ2
  case pending_registered =>
    have htool := settle_invocation.next_tool_registered hn
    intro I J hJ
    rw [htool]
    rcases pending_preimage hn hJ with ⟨K, hK, -, hpolicy, -⟩
    rw [hpolicy]
    exact hinv.pending_registered I K hK
  case root_no_pending =>
    have hrootField := settle_invocation.next_root_agent hn
    intro I J hJ
    rw [hrootField]
    rcases pending_preimage hn hJ with ⟨K, hK, hagent, -⟩
    rw [hagent]
    exact hinv.root_no_pending I K hK
  case pending_ids_consumed =>
    have hids := settle_invocation.next_consumed_ids hn
    intro I J hJ
    rw [hids]
    rcases pending_preimage hn hJ with ⟨K, hK, -⟩
    exact hinv.pending_ids_consumed I K hK
  case pending_egress_attested =>
    intro I J hJ
    rcases pending_preimage hn hJ with ⟨K, hK, -, hpolicy, hegress, -⟩
    rw [hpolicy, hegress]
    exact hinv.pending_egress_attested I K hK
  case pending_snapshot_coherent =>
    intro I J hJ
    rcases pending_preimage hn hJ with ⟨K, hK, -, hpolicy, -⟩
    rw [hpolicy]
    exact hinv.pending_snapshot_coherent I K hK
  case default_deny =>
    have hcap := settle_invocation.next_agent_cap hn
    intro I J hJ hcontained
    rw [hcap]
    rcases pending_preimage hn hJ with
      ⟨K, hK, hagent, hpolicy, -, -, hauthorized, hcontainedOld⟩
    obtain ⟨hauth, hcaps⟩ := hinv.default_deny I K hK (hcontainedOld hcontained)
    constructor
    · rw [hauthorized]
      exact hauth
    · intro C hC
      rw [hpolicy] at hC
      rw [hagent]
      exact hcaps C hC
  case flow_confinement =>
    have ht := settle_invocation.next_taint_levels hn
    have hallow := settle_invocation.next_egress_allow_ceiling hn
    have hinspect := settle_invocation.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects vouched
    rw [hallow, hinspect]
    rcases pending_preimage hn hJ with
      ⟨K, hK, hagent, -, hegress, hadmission, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hegress] at hE
      rw [hadmission]
      exact hinv.flow_confinement L I K E hL hK hKcontained hE
    · have hd := contained_owner_permitted hg hn hJ hcontained howner
      rcases settlement_source hg with ⟨R, hR, haR, hdispo, hconf, -⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hegress] at hE
      rw [hlevel, hconf, hadmission]
      exact hinv.pending_flow_compat inv I R K E hR hK hsameAgent hRcontained
        hKcontained hE
  case flow_confinement_weak =>
    have ht := settle_invocation.next_taint_levels hn
    have hallow := settle_invocation.next_egress_allow_ceiling hn
    have hinspect := settle_invocation.next_egress_inspect_ceiling hn
    intro L I J E hL hJ hcontained hE
    unfold St.flow_allows St.flow_inspects
    rw [hallow, hinspect]
    rcases pending_preimage hn hJ with
      ⟨K, hK, hagent, -, hegress, -, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [ht] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hegress] at hE
      exact hinv.flow_confinement_weak L I K E hL hK hKcontained hE
    · have hd := contained_owner_permitted hg hn hJ hcontained howner
      rcases settlement_source hg with ⟨R, hR, haR, hdispo, hconf, -⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hegress] at hE
      rw [hlevel, hconf]
      rcases hinv.pending_flow_compat inv I R K E hR hK hsameAgent hRcontained
          hKcontained hE with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  case integrity_confinement =>
    have hi := settle_invocation.next_integ_levels hn
    intro L I J hL hJ hcontained
    unfold vouched
    rcases pending_preimage hn hJ with
      ⟨K, hK, hagent, hpolicy, -, hadmission, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hpolicy, hadmission]
      exact hinv.integrity_confinement L I K hL hK hKcontained
    · have hd := contained_owner_permitted hg hn hJ hcontained howner
      rcases settlement_source hg with ⟨R, hR, haR, hdispo, -, hintegOut⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hlevel, hintegOut, hpolicy, hadmission]
      exact hinv.pending_integ_compat inv I R K hR hK hsameAgent hRcontained hKcontained
  case integrity_confinement_weak =>
    have hi := settle_invocation.next_integ_levels hn
    intro L I J hL hJ hcontained
    rcases pending_preimage hn hJ with
      ⟨K, hK, hagent, hpolicy, -, -, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [hi] at hL
    rcases hL with hL | ⟨houtcome, howner, hlevel⟩
    · rw [hagent] at hL
      rw [hpolicy]
      exact hinv.integrity_confinement_weak L I K hL hK hKcontained
    · have hd := contained_owner_permitted hg hn hJ hcontained howner
      rcases settlement_source hg with ⟨R, hR, haR, hdispo, -, hintegOut⟩
      have hRcontained : contained R := by
        unfold contained
        rw [← hdispo, hd]
      have hsameAgent : R.agent = K.agent := by
        rw [← hagent, howner, haR]
      rw [hlevel, hintegOut, hpolicy]
      rcases hinv.pending_integ_compat inv I R K hR hK hsameAgent hRcontained
          hKcontained with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  case clearance_confinement =>
    have ht := settle_invocation.next_taint_levels hn
    intro L I J hJ hcontained hspec
    rcases pending_preimage hn hJ with
      ⟨K, hK, hagent, hpolicy, -, -, -, hcontainedOld⟩
    have hKcontained := hcontainedOld hcontained
    rw [hpolicy]
    unfold speculative_taint_contained at hspec
    rcases hspec with hL | ⟨I2, M, hM, hMagent, hMcontained, hMlevel⟩
    · rw [ht] at hL
      rcases hL with hL | ⟨houtcome, howner, hlevel⟩
      · rw [hagent] at hL
        exact hinv.clearance_confinement L I K hK hKcontained (Or.inl hL)
      · have hd := contained_owner_permitted hg hn hJ hcontained howner
        rcases settlement_source hg with ⟨R, hR, haR, hdispo, hconf, -⟩
        have hRcontained : contained R := by
          unfold contained
          rw [← hdispo, hd]
        have hsameAgent : R.agent = K.agent := by
          rw [← hagent, howner, haR]
        exact hinv.clearance_confinement L I K hK hKcontained
          (Or.inr ⟨inv, R, hR, hsameAgent, hRcontained,
            hconf.symm.trans hlevel.symm⟩)
    · rcases pending_preimage hn hM with
        ⟨N, hN, hMagentN, hMpolicyN, -, -, -, hMcontainedOld⟩
      have hNcontained := hMcontainedOld hMcontained
      have hsameAgent : N.agent = K.agent := by
        rw [← hMagentN, hMagent, hagent]
      have houtput : N.policy.output_conf = L := by
        rw [← hMpolicyN]
        exact hMlevel
      exact hinv.clearance_confinement L I K hK hKcontained
        (Or.inr ⟨I2, N, hN, hsameAgent, hNcontained, houtput⟩)

/-- `invPP` (2 pairwise conjuncts), both manual: survivor pairs project to pre-state pairs
with the same stable cores, so both conjuncts defer to the pre-state invariant. -/
theorem presPP_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId)) :
    Preserves (settle_invocation inv a dispo outcome clvl ilvl att : Kav.Action St!)
      invPP := by
  intro s s' hinv _hg hn
  refine ⟨?pending_flow_compat, ?pending_integ_compat⟩
  case pending_flow_compat =>
    have hallow := settle_invocation.next_egress_allow_ceiling hn
    have hinspect := settle_invocation.next_egress_inspect_ceiling hn
    intro I1 I2 J1 J2 E hJ1 hJ2 hagent hcontained1 hcontained2 hE
    unfold St.flow_allows St.flow_inspects vouched
    rw [hallow, hinspect]
    rcases pending_preimage hn hJ1 with
      ⟨K1, hK1, hagent1, hpolicy1, -, hadmission1, -, hcontainedOld1⟩
    rcases pending_preimage hn hJ2 with
      ⟨K2, hK2, hagent2, hpolicy2, hegress2, hadmission2, -, hcontainedOld2⟩
    have hsameAgent : K1.agent = K2.agent := by
      rw [← hagent1, hagent, hagent2]
    rw [hegress2] at hE
    rw [hpolicy1, hadmission2]
    exact hinv.pending_flow_compat I1 I2 K1 K2 E hK1 hK2 hsameAgent
      (hcontainedOld1 hcontained1) (hcontainedOld2 hcontained2) hE
  case pending_integ_compat =>
    intro I1 I2 J1 J2 hJ1 hJ2 hagent hcontained1 hcontained2
    unfold vouched
    rcases pending_preimage hn hJ1 with
      ⟨K1, hK1, hagent1, hpolicy1, -, -, -, hcontainedOld1⟩
    rcases pending_preimage hn hJ2 with
      ⟨K2, hK2, hagent2, hpolicy2, -, hadmission2, -, hcontainedOld2⟩
    have hsameAgent : K1.agent = K2.agent := by
      rw [← hagent1, hagent, hagent2]
    rw [hpolicy1, hpolicy2, hadmission2]
    exact hinv.pending_integ_compat I1 I2 K1 K2 hK1 hK2 hsameAgent
      (hcontainedOld1 hcontained1) (hcontainedOld2 hcontained2)

/-- `invE` (6 evidence conjuncts): manual frame arguments. The settled slot cannot carry a
challenge (`settlement_source` + scope freshness), survivors keep their admission cores,
and the bypass conjunct splits on the permitted/demoting arm. `quarantine_pending` is
immediate. -/
theorem presE_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId)) :
    Preserves (settle_invocation inv a dispo outcome clvl ilvl att : Kav.Action St!)
      invE := by
  intro s s' hinv hg hn
  refine ⟨?challenge_scoped, ?challenges_enforce_only, ?challenge_unique,
    ?inspected_evidence_consumed, ?bypass_mode_sound, ?quarantine_pending⟩
  case challenge_scoped =>
    have hact := settle_invocation.next_agent_active hn
    have hpen := settle_invocation.next_pending hn
    have hch := settle_invocation.next_challenges hn
    have hids := settle_invocation.next_consumed_ids hn
    have htool := settle_invocation.next_tool_registered hn
    have hroot := settle_invocation.next_root_agent hn
    rcases settlement_source hg with ⟨R, hR, -⟩
    intro I sc hsc
    rw [hch] at hsc
    obtain ⟨hpending, hid, hactive, hnonroot, hregistered, hcoherent, hnarrow, hcoverage⟩ :=
      hinv.challenge_scoped I sc hsc
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
  case challenges_enforce_only =>
    have hch := settle_invocation.next_challenges hn
    have hmode := settle_invocation.next_mode hn
    intro I sc hsc
    rw [hmode]
    rw [hch] at hsc
    exact hinv.challenges_enforce_only I sc hsc
  case challenge_unique =>
    have hch := settle_invocation.next_challenges hn
    intro I sc1 sc2 hsc1 hsc2
    rw [hch] at hsc1 hsc2
    exact hinv.challenge_unique I sc1 sc2 hsc1 hsc2
  case inspected_evidence_consumed =>
    have hatt := settle_invocation.next_consumed_attestations hn
    intro I J evidence hJ hadmission
    rw [hatt]
    rcases pending_preimage hn hJ with ⟨K, hK, -, -, -, hadmissionCore, -⟩
    apply Or.inl
    apply hinv.inspected_evidence_consumed I K evidence hK
    rw [← hadmissionCore]
    exact hadmission
  case bypass_mode_sound =>
    have hpen := settle_invocation.next_pending hn
    have hmode := settle_invocation.next_mode hn
    rcases settlement_source hg with ⟨R, hR, -, hdispo, -, -⟩
    intro I J hJ
    rw [hmode]
    rcases pending_preimage hn hJ with ⟨K, hK, -, -, -, hadmission, -, -⟩
    constructor
    · intro hnotContained
      by_cases hd : dispo = Disposition.permitted
      · have hpost : settleAt s.pending inv outcome I = some J := by
          rw [hpen] at hJ
          simpa only [if_pos hd] using hJ
        rcases settleAt_pending_containment s.pending inv outcome I J hpost with
          ⟨N, hN, hcontainedIff⟩
        exact (hinv.bypass_mode_sound I N hN).1
          (fun hNcontained => hnotContained (hcontainedIff.mpr hNcontained))
      · have hRnotContained : ¬ contained R := by
          intro hRcontained
          exact hd (hdispo.trans hRcontained)
        exact (hinv.bypass_mode_sound inv R hR).1 hRnotContained
    · intro hAdmission
      exact (hinv.bypass_mode_sound I K hK).2 (by rw [← hadmission]; exact hAdmission)
  case quarantine_pending =>
    intro I J hJ hquarantined
    exact ⟨J, hJ, hquarantined⟩

/-- `invC` (3 crossing conjuncts): fully automated frame preservation. -/
theorem presC_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId)) :
    Preserves (settle_invocation inv a dispo outcome clvl ilvl att : Kav.Action St!)
      invC := by
  intro s s' hinv _hg hn
  kav_discharge_lite settle_invocation

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_settle_invocation (inv : InvocationId) (a : AgentId)
    (dispo : Disposition) (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId)) :
    Preserves (settle_invocation inv a dispo outcome clvl ilvl att : Kav.Action St!)
      allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
     presP_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
     presPP_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
     presE_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn,
     presC_settle_invocation inv a dispo outcome clvl ilvl att s s' hinv hg hn⟩

#print axioms pres_settle_invocation

end Tzimtzum
