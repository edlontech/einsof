import ArgusLean.Refinement.Bridging.StateRelation
import ArgusLean.Refinement.Bridging.FlowOracle
import ArgusLean.Refinement.Unified.ViewCoincidence
import ArgusLean.Refinement.Unified.NodupPreservation

/-! # Layer 1 — the unified state relation `R` (V4)

The single canonical refinement relation between an extracted `KernelState` / `BackgroundTheory` and
an abstract TzimtzumV4 `St`. It relates the **12** V4 state components with one canonical view per
field — set fields via `vsMem`, per-agent nested set fields via the last-match `vmsMemLast`, the
functional `agent_parent` via `vmLastEntry`, and the three struct-valued maps (`pending`,
`challenges`, `crossing_grants`) via the last-match `optRel` of their record-correspondence
predicates (`StateRelation`) — plus the key-uniqueness (`vmNodupKeys`) invariants that make those
last-match views faithful.

The V3 declassification economy is gone from `R`: no budget clause, no override clause, no
instruction/issuer clause. The V3 runtime-oracle agreement is also gone: the extracted
`begin_invocation` takes the authorizer verdict (`authorized : Bool`) and the attested egress set as
**plain arguments** (the oracle calls were lifted to the unverified Rust driver), and
inspection/conformance are one-use attestation DATA rather than oracle relations (README "Reshaped
refinement assumptions"). The only surviving per-invocation agreement is authorizer verdict + egress
classification, expressed as the argument-correspondence predicates `AuAgree` / `EgressAgree` the
bundle's `step_refines` threads at each `begin_invocation` / `authorize_inspected` step; they are the
narrowed `OracleFidelity` surface, not state carried in `R`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

/-! ## Abstract ↔ concrete ceiling-band bridge

The abstract flow gates are the derived band tests `St.flow_allows` / `St.flow_inspects`
(`ceilingAdmits` over the abstract ceiling fields); the kernel's are `ceilAdmitsC` over the two
ceiling `VecMap`s (read by `background.flow_allows` / `flow_inspects`). These lemmas cross between
them. -/

/-- `le_conf` against an abstracted concrete level is the kernel's rank compare. -/
theorem le_conf_confLeC (L : Tzimtzum.ConfLevel) (c : types.ConfLevel) :
    Tzimtzum.le_conf L (confA c) ↔ confLeC (confC L) c = true := by
  cases L <;> cases c <;> simp [Tzimtzum.le_conf, Tzimtzum.confRank, confA, confC, confLeC]

/-- `le_integ` against an abstracted concrete level is the kernel's rank compare (dual). -/
theorem le_integ_integLeC (L : Tzimtzum.IntegLevel) (c : types.IntegLevel) :
    Tzimtzum.le_integ L (integA c) ↔ integLeC (integC L) c = true := by
  cases L <;> cases c <;> simp [Tzimtzum.le_integ, Tzimtzum.integRank, integA, integC, integLeC]

/-- The abstract band test over the canonical abstraction of a concrete ceiling map coincides
    with the kernel's `ceilAdmitsC`. -/
theorem ceilingAdmits_mapA_iff (m : collections.VecMap types.EgressKind types.ConfLevel)
    (L : Tzimtzum.ConfLevel) (E : types.EgressKind) :
    Tzimtzum.ceilingAdmits (fun e => (ceilC m e).map confA) L E ↔
      ceilAdmitsC m (confC L) E = true := by
  rw [Tzimtzum.ceilingAdmits]
  unfold ceilAdmitsC
  cases hc : ceilC m E with
  | none => simp
  | some c =>
    simp only [Option.map_some, Option.some_inj]
    constructor
    · rintro ⟨ca, hca, hle⟩; subst hca; exact (le_conf_confLeC L c).mp hle
    · intro h; exact ⟨confA c, rfl, (le_conf_confLeC L c).mpr h⟩

/-- The unified refinement relation between an extracted `KernelState` / `BackgroundTheory` and the
    abstract TzimtzumV4 state. One canonical view per field (see module header). A `structure` (not a
    flat `∧`) so each per-action preservation proof names the exact conjunct it consumes. -/
structure R (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop where
  -- distinguished agent + governed mode (immutable background)
  root          : a.root_agent = bg.root_agent
  mode          : a.mode = modeA bg.mode
  -- mutable set / functional label fields
  active        : ∀ x, a.agent_active x ↔ vsMem st.agent_active x
  tool_reg      : ∀ t, a.tool_registered t ↔ vsMem st.tool_registered t
  parent        : ∀ C P, a.agent_parent C P ↔ vmLastEntry st.agent_parent.entries.val C = some (C, P)
  cap           : ∀ N C, a.agent_cap N C ↔ vmsMemLast st.agent_cap N C
  taint         : ∀ ag L, a.taint_levels ag L ↔ vmsMemLast st.taint_levels ag (confC L)
  integ         : ∀ ag L, a.integ_levels ag L ↔ vmsMemLast st.integ_levels ag (integC L)
  -- struct-valued invocation domain (last-match record correspondence)
  pending       : ∀ I, optRel pendingRel (a.pending I) (pendingC st I)
  challenges    : ∀ I, optRel challengeRel (a.challenges I) (challengeC st I)
  grants        : ∀ A D, optRel crossingGrantRel (a.crossing_grants A D)
                    (crossingGrantC st { agent := A, assignment := D })
  -- consumed histories (append-only sets)
  consumedIds   : ∀ I, a.consumed_ids I ↔ vsMem st.consumed_ids I
  consumedAtt   : ∀ Att, a.consumed_attestations Att ↔ vsMem st.consumed_attestations Att
  consumedCross : ∀ X, a.consumed_crossings X ↔ vsMem st.consumed_crossings X
  -- immutable background flow bands
  flowAllows    : ∀ L E, a.flow_allows L E ↔ ceilAdmitsC bg.allow_ceiling (confC L) E = true
  flowInspects  : ∀ L E, a.flow_inspects L E ↔ ceilAdmitsC bg.inspect_ceiling (confC L) E = true
  -- carried key-uniqueness well-formedness (makes every last-match view faithful)
  ndParent      : vmNodupKeys st.agent_parent
  ndCap         : vmNodupKeys st.agent_cap
  ndTaint       : vmNodupKeys st.taint_levels
  ndInteg       : vmNodupKeys st.integ_levels
  ndPending     : vmNodupKeys st.pending
  ndChallenges  : vmNodupKeys st.challenges
  ndGrants      : vmNodupKeys st.crossing_grants

/-! ## Per-invocation argument agreement (narrowed `OracleFidelity`)

The extracted transitions are pure functions of their arguments — the authorizer verdict and the
attested egress set enter `begin_invocation` / `authorize_inspected` as plain arguments, not oracle
calls. The refinement's only remaining fidelity obligation is therefore that these arguments agree
with the fixed per-invocation abstract interpretation the bundle uses. `AuAgree` pins the authorizer
verdict `Bool` to the abstract authorized proposition; `EgressAgree` pins the attested egress
`VecSet` to the abstract per-invocation egress relation. Both are keyed by the invocation whose gate
consumes them. The deleted V3 predicates (content-gate `CgAgree`, conformance `CfAgree`,
return-conformance `RcAgree`) have no V4 counterpart. -/

/-- Authorizer-verdict agreement for one invocation: the concrete verdict `Bool` matches the
    abstract authorized proposition. -/
def AuAgree (authorized : Bool) (P : Prop) : Prop := authorized = true ↔ P

/-- Attested-egress agreement for one invocation: the concrete egress `VecSet` has exactly the
    abstract per-invocation egress kinds as members. -/
def EgressAgree (egr : collections.VecSet types.EgressKind)
    (P : types.EgressKind → Prop) : Prop := ∀ E, E ∈ egr.items.val ↔ P E

end ArgusLean.Refinement
