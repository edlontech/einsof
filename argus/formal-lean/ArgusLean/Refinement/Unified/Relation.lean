import ArgusLean.Refinement.Bridging.StateRelation
import ArgusLean.Refinement.Bridging.FlowOracle
import ArgusLean.Refinement.Unified.ViewCoincidence
import ArgusLean.Refinement.Unified.NodupPreservation

/-! # Layer 1 — the unified state relation `R`

The per-action simulation proofs were each developed against their **own slice relation** (a focused
view of just the fields one action touches), and those slices disagree on the same fields' *views*
(`vmsMem` vs `vmsMemLast` vs `capMem`; raw-membership budget vs `budgetReadC`; guarded vs unguarded
budget). This module collapses them into **one** canonical relation `R`, picking the last-match /
get-style views the kernel actually computes and carrying the key-uniqueness (`vmNodupKeys`) and
well-formedness invariants that make those views faithful (and that every per-action slice silently
assumed for its own fields). The surviving slice relations (`Rstart` / `Rretu` / `Rsent`, for the
oracle/loop-heavy actions whose `Preservation` proof reuses the slice simulation) now live beside
their `R`-preservation proof in `Unified/Preservation/`; the simpler actions establish `R`
directly.

`R` is a `structure` (not a flat `∧`) so each per-action `R`-preservation proof can name the exact
conjunct it consumes/re-establishes.

V3 update (Campaign: integrity taint + unified boundary crossing): the ghost provenance relations
(`gh_taint_invoked` / `gh_taint_received`) are gone (deleted from the spec, design §5.2 "ghost
package") — dropped from `R` entirely, no integrity mirror was ever added. `agent_budget` is now a
total `AgentId → Nat` field on both sides, so its correspondence collapses to a plain equation (no
`agent_active` guard — the initial/absent value coincides on both sides: `budget_capacity` abstractly,
`BUDGET_CAPACITY` concretely, and every action that mutates a budget mutates it identically on both
sides). `integ_levels` / `invocation_used` / `invocation_egress` (the last restricted to used
invocations, per `StateRelation`'s `RinvocationEgress`) are new conjuncts. The three **runtime
oracle** fields deliberately are still *not* in `R`: they relate to the `Kernel<A,C,F,E>` oracle
parameters, not to stored state — the bundle's `step_refines` carries their agreement as separate
`OracleAgree`-style hypotheses (`CgAgree` / `AuAgree` / `CfAgree` / `RcAgree` below), now keyed
per-invocation (design §5.2 "Oracle verdict keying" — `output_conforms` / `authorizer_allows` /
`content_gate_passes` are gone from `St`, replaced by `invocation_conforms` / `invocation_authorized`
/ `invocation_gate_passes`). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

/-! ## Abstract ↔ concrete ceiling-band bridge

The abstract flow gates are the derived band tests `St.flow_allows` / `St.flow_inspects`
(`ceilingAdmits` over the abstract ceiling fields); the kernel's are `ceilAdmitsC` over the two
ceiling `VecMap`s. These two lemmas cross between them for the canonical abstraction of a ceiling
map, `fun E => (ceilC m E).map confA`. -/

/-- `le_conf` against an abstracted concrete level is the kernel's rank compare. -/
theorem le_conf_confLeC (L : Tzimtzum.ConfLevel) (c : types.ConfLevel) :
    Tzimtzum.le_conf L (confA c) ↔ confLeC (confC L) c = true := by
  cases L <;> cases c <;> simp [Tzimtzum.le_conf, Tzimtzum.confRank, confA, confC, confLeC]

/-- The abstract band test over the canonical abstraction of a concrete ceiling map coincides
    with the kernel's `ceilAdmitsC`. -/
theorem ceilingAdmits_mapA_iff (m : collections.VecMap types.EgressKind types.ConfLevel)
    (L : Tzimtzum.ConfLevel) (E : types.EgressKind) :
    Tzimtzum.ceilingAdmits (fun e => (ceilC m e).map confA) L E ↔
      ceilAdmitsC m (confC L) E = true := by
  rw [Tzimtzum.ceilingAdmits]
  unfold ceilAdmitsC
  cases hc : ceilC m E with
  | none => simp [hc]
  | some c =>
    simp only [hc, Option.map_some, Option.some_inj]
    constructor
    · rintro ⟨ca, hca, hle⟩; subst hca; exact (le_conf_confLeC L c).mp hle
    · intro h; exact ⟨confA c, rfl, (le_conf_confLeC L c).mpr h⟩

/-- `le_integ` against an abstracted concrete level is the kernel's rank compare (dual of
    `le_conf_confLeC`). -/
theorem le_integ_integLeC (L : Tzimtzum.IntegLevel) (c : types.IntegLevel) :
    Tzimtzum.le_integ L (integA c) ↔ integLeC (integC L) c = true := by
  cases L <;> cases c <;> simp [Tzimtzum.le_integ, Tzimtzum.integRank, integA, integC, integLeC]

/-- The unified refinement relation between an extracted `KernelState`/`BackgroundTheory` and the
    abstract TzimtzumV3 state. One canonical view per field:

    * set fields (`agent_active`, `tool_registered`, `invocation_used`) via `vsMem`;
    * per-agent nested set fields via the last-match `vmsMemLast` (what `get_set_or_empty` /
      `set_contains` read) — now including `integ_levels`, the integrity-taint dual of `taint_levels`;
    * the functional `agent_parent` via the get-style `vmLastEntry`, the functional `agent_budget`
      via the plain get-style `budgetReadC` equation (Campaign B: total `Nat` field on both sides, no
      `agent_active` guard — see module header);
    * the immutable background relations/functions to `bg` and the tool metadata `toolMetaC bg`,
      including the three V3 integrity-floor/emission fields and the two lever floors;

    plus the carried invariants: `vmNodupKeys` for every per-agent map (so last-match = `∃`-entry, the
    [[plausible-bridging-harness]] fix), the in-flight metadata well-formedness (every in-flight
    invocation is bound to a tool with metadata), and `RinvocationUsed` / `RinvocationEgress`
    (`Bridging/StateRelation`) for the two global invocation-history fields. -/
structure R (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop where
  root          : types.AgentId.root = .ok a.root_agent
  cap_declass   : a.cap_declassify = capability.CapKind.Declassify
  cap_refresh   : a.cap_credit_budget = capability.CapKind.CreditBudget
  cap_grantov   : a.cap_grant_override = capability.CapKind.GrantOverride
  -- mutable fields (canonical last-match / get-style views)
  active        : ∀ x, a.agent_active x ↔ vsMem st.agent_active x
  tool_reg      : ∀ t, a.tool_registered t ↔ vsMem st.tool_registered t
  parent        : ∀ C P, a.agent_parent C P ↔ vmLastEntry st.agent_parent.entries.val C = some (C, P)
  cap           : ∀ N C, a.agent_cap N C ↔ vmsMemLast st.agent_cap N C
  instr         : ∀ ag ins, a.agent_instruction ag ins ↔ vmsMemLast st.agent_instruction ag ins
  taint         : ∀ ag L, a.taint_levels ag L ↔ vmsMemLast st.taint_levels ag (confC L)
  integ         : ∀ ag L, a.integ_levels ag L ↔ vmsMemLast st.integ_levels ag (integC L)
  inflight      : ∀ ag I, a.in_flight ag I ↔ vmsMemLast st.in_flight ag I
  override      : ∀ ag t L, a.override_used ag t L ↔
                    vmsMemLast st.override_used ag { tool := t, level := confC L }
  budget        : ∀ G, a.agent_budget G = (budgetReadC st.agent_budget G).val
  invUsed       : RinvocationUsed st a
  invEgress     : RinvocationEgress st a
  -- immutable background relations / functions (relate to `bg`)
  toolCap       : ∀ t tmeta C, toolMetaC bg t = some tmeta →
                    (a.tool_cap t C ↔ C ∈ tmeta.capabilities.items.val)
  toolEgress    : ∀ T E, a.tool_egress T E ↔ E ∈ egItems bg T
  toolFloor     : ∀ t tmeta, toolMetaC bg t = some tmeta → a.tool_conf_floor t = confA tmeta.conf_floor
  toolIntegFloor : ∀ t tmeta, toolMetaC bg t = some tmeta →
                    a.tool_integ_floor t = integA tmeta.integ_floor
  toolIntegInspectFloor : ∀ t tmeta, toolMetaC bg t = some tmeta →
                    a.tool_integ_inspect_floor t = integA tmeta.integ_inspect_floor
  toolOutputInteg : ∀ t tmeta, toolMetaC bg t = some tmeta →
                    a.tool_output_integ t = integA tmeta.output_integ
  toolBounded   : ∀ t tmeta, toolMetaC bg t = some tmeta →
                    (a.tool_output_bounded t ↔ tmeta.output_bounded = true)
  toolIssuer    : ∀ t tmeta, toolMetaC bg t = some tmeta → a.tool_issuer t = tmeta.issuer
  trustedIss    : ∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i
  instrIssuer   : ∀ i issuer, background.BackgroundTheory.impl.instruction_issuer bg i = .ok (some issuer) →
                    a.instruction_issuer i = issuer
  flowAllows    : ∀ L E, a.flow_allows L E ↔ ceilAdmitsC bg.allow_ceiling (confC L) E = true
  flowInspects  : ∀ L E, a.flow_inspects L E ↔ ceilAdmitsC bg.inspect_ceiling (confC L) E = true
  leverFloor        : a.lever_integ_floor = integA bg.lever_integ_floor
  leverInspectFloor : a.lever_integ_inspect_floor = integA bg.lever_integ_inspect_floor
  flowOverride  : ∀ A T L, a.flow_override A T L ↔
                    vmsMemLast st.flow_override A { tool := T, level := confC L }
  invTool       : ∀ I t, invToolC st I = some t → a.invocation_tool I = t
  -- carried well-formedness invariants
  ndParent      : vmNodupKeys st.agent_parent
  ndCap         : vmNodupKeys st.agent_cap
  ndInstr       : vmNodupKeys st.agent_instruction
  ndTaint       : vmNodupKeys st.taint_levels
  ndInteg       : vmNodupKeys st.integ_levels
  ndInflight    : vmNodupKeys st.in_flight
  ndOverride    : vmNodupKeys st.override_used
  ndFlowOverride : vmNodupKeys st.flow_override
  ndBudget      : vmNodupKeys st.agent_budget
  wfInflight    : ∀ ag I, vmsMemLast st.in_flight ag I →
                    ∃ t tmeta, invToolC st I = some t ∧ toolMetaC bg t = some tmeta

/-! ## Runtime-oracle agreement

The kernel's three oracle calls (`ContentGateOracle.passes`, `AuthorizerOracle.allows`,
`ConformanceOracle.conforms`/`return_conforms`) are now all rekeyed by `InvocationId` (design §5.2
"Oracle verdict keying"): a static per-`(agent, tool)` relation cannot express "this output
conformed, the next didn't", so every per-decision verdict is attested per invocation instead. These
predicates package that agreement at the state level (`∀ agent tool inv, ∃ b, call = ok b ∧ (b ↔
abstract)`); the per-oracle-backed `step_refines` cases extract the `cgOf`/`auOf`/`cfOf` reductions
the action lemmas take. `return_conforms` stays pairwise — there is no reified return object to key
on (design's documented coarse spot); the conformance oracle calls remain **state-independent**
(`∀ s`), matching `invoke_complete_endorsed`/`invoke_complete_unendorsed`'s `hcf`.

The dual integrity floors (`tool_integ_floor` / `tool_integ_inspect_floor` / `tool_output_integ` /
`lever_integ_floor` / `lever_integ_inspect_floor`) are NOT runtime oracle calls — they are
deterministic background reads (tool metadata / `BackgroundTheory` fields), so their correspondence
is carried directly in `R` above (`toolIntegFloor` / `toolIntegInspectFloor` / `toolOutputInteg` /
`leverFloor` / `leverInspectFloor`), not as a separate `*Agree` predicate. -/

/-- Content-gate oracle agreement: every `(agent, tool, inv)` call succeeds with a boolean that
    matches the abstract `invocation_gate_passes inv`. -/
def CgAgree {C : Type} (cgInst : traits.ContentGateOracle C) (content_gate : C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  ∀ ag t inv, ∃ b : Bool, cgInst.passes content_gate ag t inv st bg = .ok b ∧
    (b = true ↔ a.invocation_gate_passes inv)

/-- Authorizer oracle agreement: every `(agent, tool, inv)` call succeeds with a boolean that
    matches the abstract `invocation_authorized inv`. -/
def AuAgree {A : Type} (aInst : traits.AuthorizerOracle A) (authorizer : A)
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  ∀ ag t inv, ∃ b : Bool, aInst.allows authorizer ag t inv st bg = .ok b ∧
    (b = true ↔ a.invocation_authorized inv)

/-- Conformance oracle agreement (state-independent, as the kernel's `invocation_conforms` is):
    every `(agent, tool, inv)` call matches the abstract `invocation_conforms inv`. -/
def CfAgree {F : Type} (cfInst : traits.ConformanceOracle F) (conformance : F)
    (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  ∀ ag t inv, ∃ b : Bool, (∀ s, cfInst.conforms conformance ag t inv s bg = .ok b) ∧
    (b = true ↔ a.invocation_conforms inv)

/-- Return-conformance oracle agreement (Campaign B P2, unchanged shape). The kernel's
    `ConformanceOracle.return_conforms` is the second verdict in the same trait, keyed `child parent`;
    like `conforms` it is modelled state-independent (`∀ s`), agreeing with the abstract
    `return_conforms` field. `return_endorsed`'s preservation takes this as a hypothesis; threading it
    into the `OracleFidelity` bundle is Task 14. -/
def RcAgree {F : Type} (cfInst : traits.ConformanceOracle F) (conformance : F)
    (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  ∀ c p, ∃ b : Bool, (∀ s, cfInst.return_conforms conformance c p s bg = .ok b) ∧
    (b = true ↔ a.return_conforms c p)

end ArgusLean.Refinement
