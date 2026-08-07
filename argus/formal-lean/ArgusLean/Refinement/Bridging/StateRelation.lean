import ArgusLean.Refinement.Bridging.Collections
import Tzimtzum

/-! # Refinement — state relation (V4)

The abstract TzimtzumV4 state (`Tzimtzum.St`) instantiated at the kernel's concrete sorts, plus the
level-lattice correspondences and the record-correspondence predicates the unified relation `R`
(`Unified/Relation.lean`) is built from. V4 replaces the V3 declassification economy (budget /
overrides / instruction provenance) with the invocation domain: struct-valued `pending` /
`challenges` maps, a composite-key `crossing_grants` map, and three consumed-id histories. The
per-record correspondence between the abstract `Prop`-valued fields and the extracted `VecSet` / `Bool`
fields lives here (`snapshotRel` / `pendingRel` / `challengeRel` / `crossingGrantRel`), as do the pure
get-style views the kernel actually reads (`pendingC` / `challengeC` / `crossingGrantC`). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

set_option maxHeartbeats 1000000

/-- The abstract TzimtzumV4 state at the kernel's concrete sorts. `ConfLevel` and `IntegLevel` are
    concrete inductives baked into `St`; the remaining sorts are the extracted `String`/inductive
    types. -/
abbrev AbsState := Tzimtzum.St types.AgentId types.ToolId types.InvocationId
  capability.CapKind types.EgressKind types.ChallengeId types.AttestationId
  types.CrossingId types.AssignmentDigest types.PolicyDigest types.ContentHash

/-! ## Confidentiality correspondence

`ConfLevel` is a baked-in inductive of the abstract `St` (not a type parameter), so the taint
fields cross from the abstract lattice to the extracted `types.*` lattice. The two are
constructor-for-constructor identical; `confC` / `confA` are the obvious total maps. -/

/-- Abstract → concrete confidentiality level. -/
def confC : Tzimtzum.ConfLevel → types.ConfLevel
  | .«public»   => .Public
  | .«internal» => .Internal
  | .sensitive  => .Sensitive
  | .restricted => .Restricted

/-- Concrete → abstract confidentiality level (the inverse of `confC`). -/
def confA : types.ConfLevel → Tzimtzum.ConfLevel
  | .Public    => .«public»
  | .Internal  => .«internal»
  | .Sensitive => .sensitive
  | .Restricted => .restricted

@[simp] theorem confC_confA (l : types.ConfLevel) : confC (confA l) = l := by cases l <;> rfl
@[simp] theorem confA_confC (l : Tzimtzum.ConfLevel) : confA (confC l) = l := by cases l <;> rfl

theorem confC_injective : Function.Injective confC :=
  fun a b h => by have := congrArg confA h; simpa using this

/-! ## Integrity correspondence (dual of confidentiality) -/

/-- Abstract → concrete integrity level. -/
def integC : Tzimtzum.IntegLevel → types.IntegLevel
  | .untrusted => .Untrusted
  | .standard  => .Standard
  | .trusted   => .Trusted
  | .attested  => .Attested

/-- Concrete → abstract integrity level (the inverse of `integC`). -/
def integA : types.IntegLevel → Tzimtzum.IntegLevel
  | .Untrusted => .untrusted
  | .Standard  => .standard
  | .Trusted   => .trusted
  | .Attested  => .attested

@[simp] theorem integC_integA (l : types.IntegLevel) : integC (integA l) = l := by cases l <;> rfl
@[simp] theorem integA_integC (l : Tzimtzum.IntegLevel) : integA (integC l) = l := by cases l <;> rfl

theorem integC_injective : Function.Injective integC :=
  fun a b h => by have := congrArg integA h; simpa using this

/-! ## Verdict / disposition / mode / outcome correspondence

The enums cross constructor-for-constructor. `dispA` and `modeA` are the concrete → abstract maps
`R` reads (disposition on pending records, mode in background); `verdictA` / `outcomeA` /
`fallbackA` support the action-argument correspondences the preservation proofs consume. -/

/-- Concrete → abstract disposition. -/
def dispA : types.Disposition → Tzimtzum.Disposition
  | .Permitted       => .permitted
  | .Blocked         => .blocked
  | .MonitorBypassed => .monitor_bypassed

/-- Concrete → abstract enforcement mode. -/
def modeA : types.Mode → Tzimtzum.Mode
  | .Enforce => .enforce
  | .Monitor => .monitor

/-- Concrete → abstract verdict. -/
def verdictA : types.Verdict → Tzimtzum.Verdict
  | .Allow              => .allow
  | .InspectionRequired => .inspection_required
  | .Deny               => .deny

/-- Concrete → abstract outcome. -/
def outcomeA : types.Outcome → Tzimtzum.Outcome
  | .Success   => .success
  | .Failure   => .failure
  | .Ambiguous => .ambiguous

/-- Concrete → abstract fallback. -/
def fallbackA : types.Fallback → Tzimtzum.Fallback
  | .Fail              => .fail
  | .ReleaseUnendorsed => .release_unendorsed

/-! ## Record correspondence

Each abstract record has `Prop`-valued set fields (`required_caps`, `declared_egress`, `egress`)
and `Prop`-valued verdict fields (`authorized`, `quarantined`); the extracted record carries
`VecSet`s and `Bool`s. These predicates pin the field-by-field correspondence, crossing the level
enums via `confA` / `integA` and the disposition/admission enums via `dispA` / `admissionRel`. -/

/-- Abstract ↔ concrete frozen `ActionPolicySnapshot`. -/
def snapshotRel (ap : Tzimtzum.ActionPolicySnapshot types.ToolId capability.CapKind
    types.EgressKind types.PolicyDigest) (cp : types.ActionPolicySnapshot) : Prop :=
  ap.tool = cp.tool
  ∧ (∀ C, ap.required_caps C ↔ C ∈ cp.required_caps.items.val)
  ∧ ap.conf_clearance = confA cp.conf_clearance
  ∧ ap.integ_floor = integA cp.integ_floor
  ∧ ap.integ_inspect = integA cp.integ_inspect
  ∧ ap.output_conf = confA cp.output_conf
  ∧ ap.output_integ = integA cp.output_integ
  ∧ (∀ E, ap.declared_egress E ↔ E ∈ cp.declared_egress.items.val)
  ∧ ap.policy_digest = cp.policy_digest

/-- Abstract ↔ concrete `Admission` evidence. -/
def admissionRel (aa : Tzimtzum.Admission types.AttestationId) (ca : types.Admission) : Prop :=
  match aa, ca with
  | .plain, .Plain => True
  | .inspected att, .Inspected att' => att = att'
  | .bypassed, .Bypassed => True
  | _, _ => False

/-- Abstract ↔ concrete `PendingInvocation` record. -/
def pendingRel (aj : Tzimtzum.PendingInvocation types.AgentId types.ToolId capability.CapKind
    types.EgressKind types.AttestationId types.PolicyDigest) (cj : types.PendingInvocation) : Prop :=
  aj.agent = cj.agent
  ∧ snapshotRel aj.policy cj.policy
  ∧ (∀ E, aj.egress E ↔ E ∈ cj.egress.items.val)
  ∧ admissionRel aj.admission cj.admission
  ∧ aj.disposition = dispA cj.disposition
  ∧ (aj.authorized ↔ cj.authorized = true)
  ∧ (aj.quarantined ↔ cj.quarantined = true)

/-- Abstract ↔ concrete `ChallengeScope` record. -/
def challengeRel (ac : Tzimtzum.ChallengeScope types.AgentId types.ToolId capability.CapKind
    types.EgressKind types.ChallengeId types.PolicyDigest types.ContentHash)
    (cc : types.ChallengeScope) : Prop :=
  ac.challenge = cc.challenge
  ∧ ac.agent = cc.agent
  ∧ snapshotRel ac.policy cc.policy
  ∧ (∀ E, ac.egress E ↔ E ∈ cc.egress.items.val)
  ∧ ac.args_hash = cc.args_hash
  ∧ (ac.authorized ↔ cc.authorized = true)

/-- Abstract ↔ concrete `CrossingGrant` record (the `u32` counters carry their `Nat` values). -/
def crossingGrantRel (ag : Tzimtzum.CrossingGrant) (cg : types.CrossingGrant) : Prop :=
  ag.remaining = cg.remaining.val ∧ ag.provisioned = cg.provisioned.val

/-- Lift a record relation over the `Option` view: absent ↔ absent, present ↔ present-and-related. -/
def optRel {α β : Type} (rel : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => rel a b
  | _, _ => False

/-! ## Get-style views

The kernel reads its struct-valued maps through the last-match `get_cloned` (identity clone), so the
faithful abstraction is the last-match value view. -/

/-- Live (last-match) pending record bound to `I`, or `none`. -/
def pendingC (st : state.KernelState) (I : types.InvocationId) : Option types.PendingInvocation :=
  (vmLastEntry st.pending.entries.val I).map Prod.snd

/-- Live (last-match) challenge scope bound to `I`, or `none`. -/
def challengeC (st : state.KernelState) (I : types.InvocationId) : Option types.ChallengeScope :=
  (vmLastEntry st.challenges.entries.val I).map Prod.snd

/-- Live (last-match) crossing grant bound to the composite `(agent, assignment)` key, or `none`. -/
def crossingGrantC (st : state.KernelState) (key : types.CrossingKey) : Option types.CrossingGrant :=
  (vmLastEntry st.crossing_grants.entries.val key).map Prod.snd

/-! ## `agent_cap` last-match membership + key-uniqueness (unchanged substrate) -/

/-- Get-style membership for the cap map: `C` is a cap of `N` iff the *last* `N`-keyed entry
    (the live one under `VecMap` last-match semantics) holds `C`. Survives duplicate keys, so
    the `insert grantee ∅` that `delegate` uses to clear a grantee's caps reads as empty. -/
def capMem (vm : collections.VecMap types.AgentId (collections.VecSet capability.CapKind))
    (N : types.AgentId) (C : capability.CapKind) : Prop :=
  ∃ p, vmLastEntry vm.entries.val N = some p ∧ C ∈ p.2.items.val

/-- Key-uniqueness well-formedness for a `VecMap`: the entry keys are `Nodup`. The invariant that
    makes the get-style reading of a *functional* map faithful. -/
def vmNodupKeys {K V : Type} (vm : collections.VecMap K V) : Prop :=
  (vm.entries.val.map Prod.fst).Nodup

/-- `VecMap.remove key` read through `capMem`: the removed key resolves to no caps, every other
    agent's caps are untouched. -/
theorem capMem_filter_removeKept
    (vm' vm : collections.VecMap types.AgentId (collections.VecSet capability.CapKind))
    (key : types.AgentId)
    (h : vm'.entries.val = vm.entries.val.filter (removeKept key)) (N : types.AgentId)
    (C : capability.CapKind) :
    capMem vm' N C ↔ capMem vm N C ∧ N ≠ key := by
  unfold capMem
  rw [h, vmLastEntry_filter_removeKept]
  by_cases hN : N = key
  · simp [hN]
  · rw [if_neg hN]
    constructor
    · rintro ⟨p, hp, hC⟩; exact ⟨⟨p, hp, hC⟩, hN⟩
    · rintro ⟨⟨p, hp, hC⟩, _⟩; exact ⟨p, hp, hC⟩

end ArgusLean.Refinement
