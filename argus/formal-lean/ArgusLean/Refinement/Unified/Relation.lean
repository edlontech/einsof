import ArgusLean.Refinement.Bridging.StateRelation
import ArgusLean.Refinement.Bridging.ReturnUnendorsedFlow
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
conjunct it consumes/re-establishes — there are ~36 of them.

The three **runtime oracle** fields (`content_gate_passes`, `authorizer_allows`, `output_conforms`)
are deliberately *not* in `R`: they relate to the `Kernel<A,C,F,E>` oracle parameters, not to stored
state. The bundle's `step_refines` carries their agreement as separate `OracleAgree` hypotheses, the
same way each oracle-backed `_refines` lemma takes its `hcg`/`hcgA` (etc.) pair. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

/-- The unified refinement relation between an extracted `KernelState`/`BackgroundTheory` and the
    abstract TzimtzumV2 state. One canonical view per field:

    * set fields (`agent_active`, `tool_registered`) via `vsMem`;
    * per-agent nested set fields via the last-match `vmsMemLast` (what `get_set_or_empty` /
      `set_contains` read);
    * the functional `agent_parent` via the get-style `vmLastEntry`, the functional `agent_budget`
      via `budgetReadC`, **guarded by `agent_active`** (a removed agent's deleted budget reads back as
      a stale "full", observable only off the active set — see `Rcasc`);
    * the immutable background relations/functions to `bg` and the tool metadata `toolMetaC bg`;

    plus the carried invariants: `vmNodupKeys` for every per-agent map (so last-match = `∃`-entry, the
    [[plausible-bridging-harness]] fix) and the in-flight metadata well-formedness (every in-flight
    invocation is bound to a tool with metadata — the conjunct `invoke_start` / `return_unendorsed` /
    `invoke_complete` need). -/
structure R (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop where
  root          : types.AgentId.root = .ok a.root_agent
  cap_declass   : a.cap_declassify = capability.CapKind.Declassify
  cap_refresh   : a.cap_refresh_budget = capability.CapKind.RefreshBudget
  -- mutable fields (canonical last-match / get-style views)
  active        : ∀ x, a.agent_active x ↔ vsMem st.agent_active x
  tool_reg      : ∀ t, a.tool_registered t ↔ vsMem st.tool_registered t
  parent        : ∀ C P, a.agent_parent C P ↔ vmLastEntry st.agent_parent.entries.val C = some (C, P)
  cap           : ∀ N C, a.agent_cap N C ↔ vmsMemLast st.agent_cap N C
  instr         : ∀ ag ins, a.agent_instruction ag ins ↔ vmsMemLast st.agent_instruction ag ins
  taint         : ∀ ag L, a.taint_levels ag L ↔ vmsMemLast st.taint_levels ag (confC L)
  inflight      : ∀ ag I, a.in_flight ag I ↔ vmsMemLast st.in_flight ag I
  ghInvoked     : ∀ ag L, a.gh_taint_invoked ag L ↔ vmsMemLast st.gh_taint_invoked ag (confC L)
  ghReceived    : ∀ ag L, a.gh_taint_received ag L ↔ vmsMemLast st.gh_taint_received ag (confC L)
  override      : ∀ ag t L, a.override_used ag t L ↔
                    vmsMemLast st.override_used ag { tool := t, level := confC L }
  budget        : ∀ G L, a.agent_active G →
                    (a.agent_budget G L ↔ budgetReadC st.agent_budget G = budgetC L)
  -- immutable background relations / functions (relate to `bg`)
  toolCap       : ∀ t tmeta C, toolMetaC bg t = some tmeta →
                    (a.tool_cap t C ↔ C ∈ tmeta.capabilities.items.val)
  toolEgress    : ∀ T E, a.tool_egress T E ↔ E ∈ egItems bg T
  toolFloor     : ∀ t tmeta, toolMetaC bg t = some tmeta → a.tool_conf_floor t = confA tmeta.conf_floor
  toolBounded   : ∀ t tmeta, toolMetaC bg t = some tmeta →
                    (a.tool_output_bounded t ↔ tmeta.output_bounded = true)
  toolIssuer    : ∀ t tmeta, toolMetaC bg t = some tmeta → a.tool_issuer t = tmeta.issuer
  trustedIss    : ∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i
  instrIssuer   : ∀ i issuer, background.BackgroundTheory.impl.instruction_issuer bg i = .ok (some issuer) →
                    a.instruction_issuer i = issuer
  flowAllows    : ∀ L E, a.flow_allows L E ↔ flowModeC bg (confC L) E = background.FlowMode.Allow
  flowInspects  : ∀ L E, a.flow_inspects L E ↔ flowModeC bg (confC L) E = background.FlowMode.Inspect
  flowOverride  : ∀ A T L, a.flow_override A T L ↔
                    vsMem bg.flow_overrides { agent := A, tool := T, level := confC L }
  invTool       : ∀ I t, invToolC st I = some t → a.invocation_tool I = t
  -- carried well-formedness invariants
  ndParent      : vmNodupKeys st.agent_parent
  ndCap         : vmNodupKeys st.agent_cap
  ndInstr       : vmNodupKeys st.agent_instruction
  ndTaint       : vmNodupKeys st.taint_levels
  ndInflight    : vmNodupKeys st.in_flight
  ndGhInvoked   : vmNodupKeys st.gh_taint_invoked
  ndGhReceived  : vmNodupKeys st.gh_taint_received
  ndOverride    : vmNodupKeys st.override_used
  ndBudget      : vmNodupKeys st.agent_budget
  wfInflight    : ∀ ag I, vmsMemLast st.in_flight ag I →
                    ∃ t tmeta, invToolC st I = some t ∧ toolMetaC bg t = some tmeta

/-! ## Runtime-oracle agreement

The kernel's three oracle calls (`ContentGateOracle.passes`, `AuthorizerOracle.allows`,
`ConformanceOracle.conforms`) must agree with the abstract state's oracle fields. These predicates
package that agreement at the state level (`∀ agent tool, ∃ b, call = ok b ∧ (b ↔ abstract)`); the
per-oracle-backed `step_refines` cases extract the `cgOf`/`auOf`/`cfOf` reductions the action lemmas
take. The conformance oracle is **state-independent** (`∀ s`), matching `invoke_complete`'s `hcf`. -/

/-- Content-gate oracle agreement: every `(agent, tool)` call succeeds with a boolean that matches the
    abstract `content_gate_passes`. -/
def CgAgree {C : Type} (cgInst : traits.ContentGateOracle C) (content_gate : C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  ∀ ag t, ∃ b : Bool, cgInst.passes content_gate ag t st bg = .ok b ∧ (b = true ↔ a.content_gate_passes ag t)

/-- Authorizer oracle agreement. -/
def AuAgree {A : Type} (aInst : traits.AuthorizerOracle A) (authorizer : A)
    (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  ∀ ag t, ∃ b : Bool, aInst.allows authorizer ag t st bg = .ok b ∧ (b = true ↔ a.authorizer_allows ag t)

/-- Conformance oracle agreement (state-independent, as the kernel's `output_conforms` is). -/
def CfAgree {F : Type} (cfInst : traits.ConformanceOracle F) (conformance : F)
    (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  ∀ ag t, ∃ b : Bool, (∀ s, cfInst.conforms conformance ag t s bg = .ok b) ∧
    (b = true ↔ a.output_conforms ag t)

end ArgusLean.Refinement
