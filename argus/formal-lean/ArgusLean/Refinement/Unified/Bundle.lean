import ArgusLean.Refinement.Unified.Preservation.RegisterTool
import ArgusLean.Refinement.Unified.Preservation.UnregisterTool
import ArgusLean.Refinement.Unified.Preservation.Delegate
import ArgusLean.Refinement.Unified.Preservation.GrantCapability
import ArgusLean.Refinement.Unified.Preservation.GrantCrossing
import ArgusLean.Refinement.Unified.Preservation.Revoke
import ArgusLean.Refinement.Unified.Preservation.CascadeRevoke
import ArgusLean.Refinement.Unified.Preservation.Ingest
import ArgusLean.Refinement.Unified.Preservation.BeginInvocation
import ArgusLean.Refinement.Unified.Preservation.AuthorizeInspected
import ArgusLean.Refinement.Unified.Preservation.SettleInvocation
import ArgusLean.Refinement.Unified.Preservation.CrossOutput

/-! # Layer 1 — V4 dispatch and one-step refinement

`KernelCmd` is the twelve-command surface of the extracted V4 kernel. `kernelStep` dispatches one
command to exactly one extracted transition. `AbsStep` describes the corresponding single V4 action;
its existential parameters are only the action's transparent internal branch choices (disposition,
verdict, live challenge scope, settlement record fields, or crossing branch).

The bundle has two explicit per-step contracts:

* `StepPre` contains only extraction/resource premises plus the fixed per-invocation snapshot
  prediction used by `begin_invocation`.
* `StepFidelity` is the narrowed oracle seam: the begin command's authorizer `Bool` and attested
  egress set agree with the fixed abstract per-invocation interpretation. Inspection, resolution,
  and conformance are explicit scoped one-use data and require no oracle assumption.
-/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

abbrev AbsSnapshot := Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
  types.EgressKind types.PolicyDigest

/-- The extracted driver-level command surface. -/
inductive KernelCmd where
  | RegisterTool : types.ToolId → KernelCmd
  | UnregisterTool : types.ToolId → KernelCmd
  | Delegate : types.AgentId → types.AgentId → KernelCmd
  | GrantCapability : types.AgentId → types.AgentId → capability.CapKind → KernelCmd
  | GrantCrossing : types.AgentId → types.AgentId → types.AssignmentDigest → Std.U32 → KernelCmd
  | Revoke : types.AgentId → types.AgentId → KernelCmd
  | CascadeRevoke : types.AgentId → types.AgentId → KernelCmd
  | Ingest : types.AgentId → Option types.AgentId → types.ConfLevel → types.IntegLevel → KernelCmd
  | BeginInvocation : types.AgentId → types.InvocationId → types.ChallengeId →
      types.ActionPolicySnapshot → collections.VecSet types.EgressKind → types.ContentHash → Bool →
      KernelCmd
  | AuthorizeInspected : types.InvocationId → types.InspectionAttestation → KernelCmd
  | SettleInvocation : types.InvocationId → types.Outcome → Option types.ResolutionAttestation →
      KernelCmd
  | CrossOutput : types.CrossInput → KernelCmd

/-- Dispatch a command to the matching extracted transition. -/
noncomputable def kernelStep (st : state.KernelState) (bg : background.BackgroundTheory) (cmd : KernelCmd) :
    Result (core.result.Result (state.KernelState × event.KernelAction) error.KernelError) :=
  match cmd with
  | .RegisterTool tool => transitions.register_tool st tool
  | .UnregisterTool tool => transitions.unregister_tool st tool
  | .Delegate grantor grantee => transitions.delegate st bg grantor grantee
  | .GrantCapability parent child cap => transitions.grant_capability st parent child cap
  | .GrantCrossing grantor agent assignment n =>
      transitions.grant_crossing st bg grantor agent assignment n
  | .Revoke parent target => transitions.revoke st bg parent target
  | .CascadeRevoke child parent => transitions.cascade_revoke st bg child parent
  | .Ingest agent src pconf pinteg => transitions.ingest st bg agent src pconf pinteg
  | .BeginInvocation agent inv chal snap egr ah authorized =>
      transitions.begin_invocation st bg agent inv chal snap egr ah authorized
  | .AuthorizeInspected inv att => transitions.authorize_inspected st bg inv att
  | .SettleInvocation inv outcome att => transitions.settle_invocation st inv outcome att
  | .CrossOutput q => transitions.cross_output st bg q

/-! ## Canonical abstractions for explicit data inputs -/

/-- Canonical abstraction of an inspection attestation. -/
def inspectionA (att : types.InspectionAttestation) :
    Tzimtzum.InspectionAttestation types.InvocationId types.ChallengeId types.AttestationId
      types.PolicyDigest types.ContentHash where
  id := att.id
  inv := att.inv
  challenge := att.challenge
  args_hash := att.args_hash
  policy_digest := att.policy_digest
  positive := att.positive = true

@[simp] theorem inspectionA_rel (att : types.InspectionAttestation) :
    inspectionAttestationRel (inspectionA att) att := by
  simp [inspectionA, inspectionAttestationRel]

/-- Canonical abstraction of a quarantine-resolution attestation. -/
def resolutionA (att : types.ResolutionAttestation) :
    Tzimtzum.ResolutionAttestation types.InvocationId types.AttestationId where
  id := att.id
  inv := att.inv
  outcome := outcomeA att.outcome

@[simp] theorem resolutionA_rel (att : types.ResolutionAttestation) :
    resolutionAttestationRel (resolutionA att) att := by
  simp [resolutionA, resolutionAttestationRel]

@[simp] theorem resolutionOptionA_rel (att : Option types.ResolutionAttestation) :
    optRel resolutionAttestationRel (att.map resolutionA) att := by
  cases att <;> simp [optRel]

/-- Canonical abstraction of a conformance attestation carried by `CrossInput`. -/
def conformanceA (att : types.ConformanceAttestation) :
    Tzimtzum.ConformanceAttestation types.AgentId types.AttestationId types.AssignmentDigest
      types.ContentHash where
  id := att.id
  output := att.output
  src := att.src
  rcv := att.rcv
  descriptor := att.descriptor
  assignment := att.assignment
  positive := att.positive = true

@[simp] theorem conformanceA_rel (att : types.ConformanceAttestation) :
    conformanceAttestationRel (conformanceA att) att := by
  simp [conformanceA, conformanceAttestationRel]

@[simp] theorem conformanceOptionA_rel (att : Option types.ConformanceAttestation) :
    optRel conformanceAttestationRel (att.map conformanceA) att := by
  cases att <;> simp [optRel]

/-- Canonical abstraction of the explicit crossing input. -/
def crossA (q : types.CrossInput) :
    Tzimtzum.CrossInput types.AgentId types.AttestationId types.CrossingId
      types.AssignmentDigest types.ContentHash where
  src := q.src
  rcv := q.rcv
  crossing := q.crossing
  output_hash := q.output_hash
  descriptor := q.descriptor
  fallback := fallbackA q.fallback
  t_integ := integA q.t_integ
  t_conf := q.t_conf.map confA
  assignment := q.assignment
  evidence := q.evidence.map conformanceA
  released_conf := confA q.released_conf
  released_integ := integA q.released_integ

@[simp] theorem crossA_rel (q : types.CrossInput) : crossInputRel (crossA q) q := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  exact conformanceOptionA_rel q.evidence

/-! ## Abstract step selected by a concrete command -/

/-- The one V4 action refined by a command. Existentials expose only that action's internal branch
parameters; they do not widen the command to another action. -/
def AbsStep
    (snapRel : types.InvocationId → AbsSnapshot)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (auRel : types.InvocationId → Prop)
    (cmd : KernelCmd) (a a' : AbsState) : Prop :=
  match cmd with
  | .RegisterTool tool =>
      (Tzimtzum.register_tool tool).guard a ∧ (Tzimtzum.register_tool tool).next a a'
  | .UnregisterTool tool =>
      (Tzimtzum.unregister_tool tool).guard a ∧ (Tzimtzum.unregister_tool tool).next a a'
  | .Delegate grantor grantee =>
      (Tzimtzum.delegate grantor grantee).guard a ∧
        (Tzimtzum.delegate grantor grantee).next a a'
  | .GrantCapability parent child cap =>
      (Tzimtzum.grant_capability parent child cap).guard a ∧
        (Tzimtzum.grant_capability parent child cap).next a a'
  | .GrantCrossing grantor agent assignment n =>
      (Tzimtzum.grant_crossing grantor agent assignment n.val).guard a ∧
        (Tzimtzum.grant_crossing grantor agent assignment n.val).next a a'
  | .Revoke parent target =>
      (Tzimtzum.revoke parent target).guard a ∧ (Tzimtzum.revoke parent target).next a a'
  | .CascadeRevoke child parent =>
      (Tzimtzum.cascade_revoke child parent).guard a ∧
        (Tzimtzum.cascade_revoke child parent).next a a'
  | .Ingest agent src pconf pinteg =>
      ∃ dispo, (Tzimtzum.ingest agent src (confA pconf) (integA pinteg) dispo).guard a ∧
        (Tzimtzum.ingest agent src (confA pconf) (integA pinteg) dispo).next a a'
  | .BeginInvocation agent inv chal _snap _egr ah _authorized =>
      ∃ verdict,
        (Tzimtzum.begin_invocation agent inv chal (snapRel inv) (egRel inv) ah (auRel inv)
          verdict).guard a ∧
        (Tzimtzum.begin_invocation agent inv chal (snapRel inv) (egRel inv) ah (auRel inv)
          verdict).next a a'
  | .AuthorizeInspected inv att =>
      ∃ scope admit,
        (Tzimtzum.authorize_inspected inv scope (inspectionA att) admit).guard a ∧
        (Tzimtzum.authorize_inspected inv scope (inspectionA att) admit).next a a'
  | .SettleInvocation inv outcome att =>
      ∃ agent dispo clvl ilvl,
        (Tzimtzum.settle_invocation inv agent dispo (outcomeA outcome) clvl ilvl
          (att.map resolutionA)).guard a ∧
        (Tzimtzum.settle_invocation inv agent dispo (outcomeA outcome) clvl ilvl
          (att.map resolutionA)).next a a'
  | .CrossOutput q =>
      ∃ branch dispo,
        (Tzimtzum.cross_output (crossA q) branch dispo).guard a ∧
        (Tzimtzum.cross_output (crossA q) branch dispo).next a a'

/-! ## Exact per-command assumptions -/

/-- Branch-specific collection bounds and the begin snapshot prediction. The `grant_crossing`
`u32` bound is retained explicitly at the refinement boundary rather than silently discharged from
its concrete representation. -/
def StepPre (st : state.KernelState) (a : AbsState)
    (snapRel : types.InvocationId → AbsSnapshot) (cmd : KernelCmd) : Prop :=
  match cmd with
  | .RegisterTool _ => st.tool_registered.items.val.length < Usize.max
  | .UnregisterTool _ => True
  | .Delegate _ _ =>
      st.agent_active.items.val.length < Usize.max ∧
      st.agent_parent.entries.val.length < Usize.max
  | .GrantCapability _ _ _ =>
      st.agent_cap.entries.val.length < Usize.max ∧
      (∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
  | .GrantCrossing _ _ _ n =>
      st.crossing_grants.entries.val.length < Usize.max ∧ n.val < 2 ^ 32
  | .Revoke _ _ => True
  | .CascadeRevoke _ _ => True
  | .Ingest _ _ _ _ =>
      st.taint_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      st.integ_levels.entries.val.length < Usize.max ∧
      (∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max)
  | .BeginInvocation agent inv _ snap _ _ _ =>
      vmSetLen st.taint_levels agent + st.pending.entries.val.length ≤ Usize.max ∧
      vmSetLen st.integ_levels agent + st.pending.entries.val.length ≤ Usize.max ∧
      st.pending.entries.val.length < Usize.max ∧
      st.challenges.entries.val.length < Usize.max ∧
      st.consumed_ids.items.val.length < Usize.max ∧
      snapshotRel (snapRel inv) snap
  | .AuthorizeInspected inv _ =>
      (∀ sc, challengeC st inv = some sc →
        vmSetLen st.taint_levels sc.agent + st.pending.entries.val.length ≤ Usize.max) ∧
      (∀ sc, challengeC st inv = some sc →
        vmSetLen st.integ_levels sc.agent + st.pending.entries.val.length ≤ Usize.max) ∧
      st.pending.entries.val.length < Usize.max ∧
      st.consumed_attestations.items.val.length < Usize.max
  | .SettleInvocation _ outcome att =>
      (outcome = .Ambiguous → st.pending.entries.val.length < Usize.max) ∧
      (outcome ≠ .Ambiguous → st.taint_levels.entries.val.length < Usize.max) ∧
      (outcome ≠ .Ambiguous →
        ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      (outcome ≠ .Ambiguous → st.integ_levels.entries.val.length < Usize.max) ∧
      (outcome ≠ .Ambiguous →
        ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      (∀ r, att = some r → st.consumed_attestations.items.val.length < Usize.max)
  | .CrossOutput q =>
      (Tzimtzum.endorsedOK a (crossA q) →
        st.taint_levels.entries.val.length < Usize.max) ∧
      (Tzimtzum.endorsedOK a (crossA q) →
        ∀ p ∈ st.taint_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      (Tzimtzum.endorsedOK a (crossA q) →
        st.integ_levels.entries.val.length < Usize.max) ∧
      (Tzimtzum.endorsedOK a (crossA q) →
        ∀ p ∈ st.integ_levels.entries.val, p.2.items.val.length < Usize.max) ∧
      (¬Tzimtzum.endorsedOK a (crossA q) → (crossA q).fallback = .release_unendorsed →
        ∀ src, collections.VecMapKVecSet.get_set_or_empty
          types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          st.taint_levels q.src = .ok src → CopyCapacity st.taint_levels q.rcv src) ∧
      (¬Tzimtzum.endorsedOK a (crossA q) → (crossA q).fallback = .release_unendorsed →
        ∀ src, collections.VecMapKVecSet.get_set_or_empty
          types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
          types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
          st.integ_levels q.src = .ok src → CopyCapacity st.integ_levels q.rcv src) ∧
      st.consumed_crossings.items.val.length < Usize.max ∧
      (Tzimtzum.endorsedOK a (crossA q) →
        st.consumed_attestations.items.val.length < Usize.max) ∧
      (Tzimtzum.endorsedOK a (crossA q) →
        st.crossing_grants.entries.val.length < Usize.max)

/-- The only residual oracle agreement: authorizer verdict and egress classification at begin. -/
def StepFidelity (egRel : types.InvocationId → types.EgressKind → Prop)
    (auRel : types.InvocationId → Prop) (cmd : KernelCmd) : Prop :=
  match cmd with
  | .BeginInvocation _ inv _ _ egr _ authorized =>
      AuAgree authorized (auRel inv) ∧ EgressAgree egr (egRel inv)
  | _ => True

/-! ## Twelve-way preservation bundle -/

set_option maxHeartbeats 2000000

/-- Every successful extracted V4 transition performs exactly one corresponding abstract V4 action
and preserves the unified relation. -/
theorem step_refines
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (snapRel : types.InvocationId → AbsSnapshot)
    (egRel : types.InvocationId → types.EgressKind → Prop)
    (auRel : types.InvocationId → Prop)
    (cmd : KernelCmd) (hR : R st bg a)
    (hScoped : Tzimtzum.challenge_scoped a)
    (hPre : StepPre st a snapRel cmd)
    (hFid : StepFidelity egRel auRel cmd)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : kernelStep st bg cmd = .ok (.Ok (st', ev))) :
    ∃ a', AbsStep snapRel egRel auRel cmd a a' ∧ R st' bg a' := by
  cases cmd with
  | RegisterTool tool =>
      obtain ⟨a', hg, hn, hR'⟩ := register_tool_preservesR st bg a tool hR hPre st' ev hok
      exact ⟨a', ⟨hg, hn⟩, hR'⟩
  | UnregisterTool tool =>
      obtain ⟨a', hg, hn, hR'⟩ := unregister_tool_preservesR st bg a tool hR st' ev hok
      exact ⟨a', ⟨hg, hn⟩, hR'⟩
  | Delegate grantor grantee =>
      obtain ⟨a', hg, hn, hR'⟩ :=
        delegate_preservesR st bg a grantor grantee hR hPre.1 hPre.2 st' ev hok
      exact ⟨a', ⟨hg, hn⟩, hR'⟩
  | GrantCapability parent child cap =>
      obtain ⟨a', hg, hn, hR'⟩ :=
        grant_capability_preservesR st bg a parent child cap hR hPre.1 hPre.2 st' ev hok
      exact ⟨a', ⟨hg, hn⟩, hR'⟩
  | GrantCrossing grantor agent assignment n =>
      obtain ⟨a', hg, hn, hR'⟩ :=
        grant_crossing_preservesR st bg a grantor agent assignment n hR hPre.1 st' ev hok
      exact ⟨a', ⟨hg, hn⟩, hR'⟩
  | Revoke parent target =>
      obtain ⟨a', hg, hn, hR'⟩ := revoke_preservesR st bg a parent target hR st' ev hok
      exact ⟨a', ⟨hg, hn⟩, hR'⟩
  | CascadeRevoke child parent =>
      obtain ⟨a', hg, hn, hR'⟩ :=
        cascade_revoke_preservesR st bg a child parent hR st' ev hok
      exact ⟨a', ⟨hg, hn⟩, hR'⟩
  | Ingest agent src pconf pinteg =>
      obtain ⟨dispo, a', hg, hn, hR'⟩ :=
        ingest_preservesR st bg a agent src pconf pinteg hR hPre.1 hPre.2.1 hPre.2.2.1
          hPre.2.2.2 st' ev hok
      exact ⟨a', ⟨dispo, hg, hn⟩, hR'⟩
  | BeginInvocation agent inv chal snap egr ah authorized =>
      obtain ⟨hcapT, hcapI, hcapP, hcapCh, hcapIds, hsnap⟩ := hPre
      obtain ⟨hAu, hEg⟩ := hFid
      obtain ⟨verdict, a', hg, hn, hR'⟩ :=
        begin_invocation_preservesR st bg a agent inv chal snap (snapRel inv) hsnap egr
          (egRel inv) hEg ah authorized (auRel inv) hAu hR hcapT hcapI hcapP hcapCh hcapIds
          st' ev hok
      exact ⟨a', ⟨verdict, hg, hn⟩, hR'⟩
  | AuthorizeInspected inv att =>
      obtain ⟨hcapT, hcapI, hcapP, hcapAtt⟩ := hPre
      obtain ⟨scope, admit, a', hg, hn, hR'⟩ :=
        authorize_inspected_preservesR st bg a inv att (inspectionA att) (inspectionA_rel att) hR
          hScoped hcapT hcapI hcapP hcapAtt st' ev hok
      exact ⟨a', ⟨scope, admit, hg, hn⟩, hR'⟩
  | SettleInvocation inv outcome att =>
      obtain ⟨hcapP, hcapTE, hcapTS, hcapIE, hcapIS, hcapAtt⟩ := hPre
      obtain ⟨agent, dispo, clvl, ilvl, a', hg, hn, hR'⟩ :=
        settle_invocation_preservesR st bg a inv outcome att (att.map resolutionA)
          (resolutionOptionA_rel att) hR hcapP hcapTE hcapTS hcapIE hcapIS hcapAtt st' ev hok
      exact ⟨a', ⟨agent, dispo, clvl, ilvl, hg, hn⟩, hR'⟩
  | CrossOutput q =>
      obtain ⟨hcapEndT, hcapEndTS, hcapEndI, hcapEndIS, hcapCopyT, hcapCopyI, hcapCross,
        hcapAtt, hcapGrant⟩ := hPre
      obtain ⟨branch, dispo, a', hg, hn, hR'⟩ :=
        cross_output_preservesR st bg a hR q (crossA q) (crossA_rel q) hcapEndT hcapEndTS
          hcapEndI hcapEndIS hcapCopyT hcapCopyI hcapCross hcapAtt hcapGrant st' ev hok
      exact ⟨a', ⟨branch, dispo, hg, hn⟩, hR'⟩

end ArgusLean.Refinement
