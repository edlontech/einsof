import Tzimtzum.State
import Kav.Action
import Kav.Transition

/-! # TzimtzumV2 — structural actions (Kav port)

Faithful port of the first six (structural) actions of the Veil spec
`tzimtzum/TzimtzumV2.lean` into the Kav framework:
`register_tool`, `load_instruction`, `delegate`, `grant_capability`,
`revoke`, `cascade_revoke`.

Definitions only — proofs are a later task.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

-- register_tool (Veil lines 393-397).
kav_action register_tool (tool : ToolId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require ¬ s.tool_registered tool
  require s.trusted_issuer (s.tool_issuer tool)
  tool_registered := fun T => s.tool_registered T ∨ T = tool

-- unregister_tool (design §5.6 "Unregistration", 15th action). A compromised tool can
-- finally leave the authorization surface: the guard forbids removing a tool with an
-- in-flight invocation, which preserves `in_flight_registered` by construction. Re-registration
-- later is permitted — `register_tool`'s guard only requires ¬registered + a trusted issuer, so
-- no new machinery is needed for a tool to come back. Issuer distrust (key revocation) stays in
-- the mesh (design §3 non-goal); this action is tool lifecycle only.
kav_action unregister_tool (tool : ToolId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.tool_registered tool
  require ∀ (A : AgentId) (I : InvocationId), s.in_flight A I → s.invocation_tool I ≠ tool
  tool_registered := fun T => s.tool_registered T ∧ T ≠ tool

-- load_instruction (Veil lines 408-412).
kav_action load_instruction (a : AgentId) (instr : InstructionId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require s.trusted_issuer (s.instruction_issuer instr)
  agent_instruction := fun A I => s.agent_instruction A I ∨ (A = a ∧ I = instr)

-- delegate (Veil lines 426-441). Budget mint fix (design finding 5): the grantee spawns at
-- budget 0, not full capacity — `sentinel_credit_budget` is the only faucet.
open Classical in
kav_action delegate (grantor grantee : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active grantor
  require ¬ s.agent_active grantee
  require grantee ≠ s.root_agent
  agent_active := fun A => s.agent_active A ∨ A = grantee
  agent_parent := fun C P =>
    (C = grantee ∧ P = grantor) ∨ (s.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)
  agent_cap := fun N C => s.agent_cap N C ∧ N ≠ grantee
  agent_instruction := fun A I => s.agent_instruction A I ∧ A ≠ grantee
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ grantee
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ grantee
  agent_budget := fun G => if G = grantee then 0 else s.agent_budget G
  in_flight := fun A I => s.in_flight A I ∧ A ≠ grantee
  override_used := fun A T L => s.override_used A T L ∧ A ≠ grantee
  flow_override := fun A T L => s.flow_override A T L ∧ A ≠ grantee

-- grant_capability (Veil lines 450-456).
kav_action grant_capability (prnt child : AgentId) (cap : CapKind) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active prnt
  require s.agent_active child
  require s.agent_parent child prnt
  require s.agent_cap prnt cap
  agent_cap := fun N C => (N = child ∧ C = cap) ∨ s.agent_cap N C

-- revoke (Veil lines 467-482). `agent_budget` is left framed: a revoked agent's budget
-- value is inert (it can no longer act), and `delegate` resets it to 0 deterministically
-- if the id is ever reused as a grantee.
kav_action revoke (prnt target : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent target prnt
  require s.agent_active prnt
  require s.agent_active target
  require target ≠ s.root_agent
  agent_active := fun A => s.agent_active A ∧ A ≠ target
  agent_parent := fun C P => s.agent_parent C P ∧ C ≠ target
  agent_cap := fun A C => s.agent_cap A C ∧ A ≠ target
  agent_instruction := fun A I => s.agent_instruction A I ∧ A ≠ target
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ target
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ target
  in_flight := fun A I => s.in_flight A I ∧ A ≠ target
  override_used := fun A T L => s.override_used A T L ∧ A ≠ target
  flow_override := fun A T L => s.flow_override A T L ∧ A ≠ target

-- cascade_revoke (Veil lines 505-520). `agent_budget` left framed, same rationale as `revoke`.
kav_action cascade_revoke (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent child prnt
  require ¬ s.agent_active prnt
  require s.agent_active child
  require child ≠ s.root_agent
  agent_active := fun A => s.agent_active A ∧ A ≠ child
  agent_parent := fun C P => s.agent_parent C P ∧ C ≠ child
  agent_cap := fun A C => s.agent_cap A C ∧ A ≠ child
  agent_instruction := fun A I => s.agent_instruction A I ∧ A ≠ child
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ child
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ child
  in_flight := fun A I => s.in_flight A I ∧ A ≠ child
  override_used := fun A T L => s.override_used A T L ∧ A ≠ child
  flow_override := fun A T L => s.flow_override A T L ∧ A ≠ child

-- invoke_start (Veil lines 550-606). THE BIG ONE: freshness + attestation guards,
-- CHECK 1 + 2a + 2b + 2c + 3 + 4a + 4b + 4c, override_used full-redefinition (clauses
-- 2a/2c/2b), and the in_flight point-set.
-- Eager consumption (design doc "Override consumption semantics"): an armed override is
-- marked used whenever the gate examined a pair it was armed for, regardless of whether
-- another arm (ALLOW / INSPECT+gate) would have admitted the flow — no negated gate arms,
-- no inner egress existentials.
-- Freshness (`invocation_used`) closes the id-reuse hole that would let a stale
-- `invocation_egress` attestation ride a new call; narrowing/coverage keep the attested
-- egress anchored to (and, on egress-bearing tools, non-vacuously covering) the tool's
-- declared set, so CHECK 2 can gate over the attested set instead of the static one.
-- CHECK 4 a/b/c (design §5.3) mirror CHECK 2's three sub-checks on the integrity side; all
-- three needed for inductiveness of the pairwise in-flight invariant including the self-pair
-- (Task 14). The "web_fetch completes while delete_repo is in flight" hazard is CHECK 4b. No
-- override arm anywhere — endorsement is the only way up.
kav_action invoke_start (a : AgentId) (tool : ToolId) (inv : InvocationId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require a ≠ s.root_agent
  require s.tool_registered tool
  require s.invocation_tool inv = tool
  require ∀ AG, ¬ s.in_flight AG inv
  -- Freshness: this invocation id has never been used before.
  require ¬ s.invocation_used inv
  -- Narrowing: the attested egress cannot exceed the tool's declared set.
  require ∀ E, s.invocation_egress inv E → s.tool_egress tool E
  -- Coverage: an egress-bearing tool cannot be admitted on an empty attestation.
  require (∃ E, s.tool_egress tool E) → (∃ E, s.invocation_egress inv E)
  -- CHECK 1: Capability gate
  require ∀ C, s.tool_cap tool C → s.agent_cap a C
  -- CHECK 2a: Flow gate (existing speculative taint × new invocation's attested egress).
  -- The vouch is the NEW invocation's content-gate verdict.
  require ∀ L E,
    Tzimtzum.speculative_taint s a L ∧ s.invocation_egress inv E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.invocation_gate_passes inv)
      ∨ (s.flow_override a tool L ∧ ¬ s.override_used a tool L)
  -- CHECK 2b: Flow gate (new tool's taint × existing in-flight I's attested egress). The
  -- vouch is the IN-FLIGHT invocation I's content-gate verdict (being re-examined against
  -- the new floor).
  require ∀ I E,
    s.in_flight a I ∧ s.invocation_egress I E →
      s.flow_allows (s.tool_conf_floor tool) E
      ∨ (s.flow_inspects (s.tool_conf_floor tool) E
          ∧ s.invocation_gate_passes I)
      ∨ (s.flow_override a (s.invocation_tool I) (s.tool_conf_floor tool)
          ∧ ¬ s.override_used a (s.invocation_tool I) (s.tool_conf_floor tool))
  -- CHECK 2c: Self-flow gate (tool's own taint × the new invocation's own attested egress).
  -- The vouch is again the NEW invocation's content-gate verdict.
  require ∀ E,
    s.invocation_egress inv E →
      s.flow_allows (s.tool_conf_floor tool) E
      ∨ (s.flow_inspects (s.tool_conf_floor tool) E ∧ s.invocation_gate_passes inv)
      ∨ (s.flow_override a tool (s.tool_conf_floor tool)
          ∧ ¬ s.override_used a tool (s.tool_conf_floor tool))
  -- CHECK 3: Authorizer gate, keyed on this invocation.
  require s.invocation_authorized inv
  -- CHECK 4 a/b/c: integrity gate (mirrors CHECK 2's three sub-checks on the integrity
  -- side — all three needed for inductiveness of the pairwise in-flight invariant
  -- including the self-pair, Task 14). NO override arm anywhere: endorsement is the only
  -- way up (design §3 non-goal, §5.3).
  -- CHECK 4a: speculative integrity (existing + in-flight emissions) × new tool's floor.
  require ∀ L,
    Tzimtzum.speculative_integ s a L →
      s.integ_allows L tool ∨ (s.integ_inspects L tool ∧ s.invocation_gate_passes inv)
  -- CHECK 4b: new tool's emission × every in-flight tool's floor (the "web_fetch
  -- completes while delete_repo is in flight" hazard). The vouch keys the IN-FLIGHT
  -- invocation I — the one whose floor is being crossed, mirroring CHECK 2b's vouch of I.
  require ∀ I,
    s.in_flight a I →
      s.integ_allows (s.tool_output_integ tool) (s.invocation_tool I)
      ∨ (s.integ_inspects (s.tool_output_integ tool) (s.invocation_tool I)
          ∧ s.invocation_gate_passes I)
  -- CHECK 4c: new tool's own emission × its own floor.
  require
    s.integ_allows (s.tool_output_integ tool) tool
    ∨ (s.integ_inspects (s.tool_output_integ tool) tool ∧ s.invocation_gate_passes inv)
  override_used := fun A T L =>
    s.override_used A T L
    -- 2a: new tool armed against existing speculative taint L
    ∨ (A = a ∧ T = tool ∧ s.flow_override a tool L ∧ Tzimtzum.speculative_taint s a L)
    -- 2c: new tool's own floor armed against its own egress
    ∨ (A = a ∧ T = tool ∧ L = s.tool_conf_floor tool ∧ s.flow_override a tool (s.tool_conf_floor tool))
    -- 2b: pre-existing in-flight tool I armed against new tool's floor (keyed on I's tool)
    ∨ (A = a ∧ L = s.tool_conf_floor tool
        ∧ (∃ I, s.in_flight a I ∧ T = s.invocation_tool I
           ∧ s.flow_override a (s.invocation_tool I) (s.tool_conf_floor tool)))
  in_flight := fun A I => s.in_flight A I ∨ (A = a ∧ I = inv)
  invocation_used := fun I => s.invocation_used I ∨ I = inv

-- The two-dimension crossing helpers (design §5.4). `conf_helps` mirrors the old
-- `¬ already-tainted-at-floor` conjunct; `integ_helps` is its integrity dual (would this
-- crossing newly LOWER the agent's held floor, i.e. is the agent not already degraded there).
def conf_helps
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (inv : InvocationId) : Prop :=
  ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv))

def integ_helps
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (inv : InvocationId) : Prop :=
  ¬ s.integ_levels a (s.tool_output_integ (s.invocation_tool inv))

-- Dimension-adjusted debit (design §5.4): pay `declass_weight` only if the conf insert would
-- be new, `integ_weight` only if the integ drop would be real — an already-conf-tainted agent
-- endorsing an untrusted-emission tool pays only the integrity half. Classical `ite` on the
-- (undecidable, type-variable-keyed) `conf_helps`/`integ_helps` Props, same denylisted-`ite`
-- pattern as every other budget point-update in this file (Task 1/3); `noncomputable` because
-- the branch conditions route through `Classical.propDecidable`, not a real `Decidable`
-- instance — harmless, the spec is proof-only.
open Classical in
noncomputable def crossing_weight
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (inv : InvocationId) : Nat :=
  (if conf_helps s a inv then declass_weight (s.tool_conf_floor (s.invocation_tool inv)) else 0)
  + (if integ_helps s a inv then integ_weight (s.tool_output_integ (s.invocation_tool inv)) else 0)

-- The shared crossing-guard predicate (design §5.4 "invoke_complete shape" / §4). Replaces
-- the endorsed predicate that used to be inlined (and repeated) three times inside a single
-- `invoke_complete`: the 5-conjunct
--   `output_bounded ∧ invocation_conforms ∧ cap_declassify ∧ affordable crossing_weight
--    ∧ (conf_helps ∨ integ_helps)`
-- `cap_declassify` is required at BOTH crossing sites — invocation completion and endorsed
-- return — closing an undocumented asymmetry (design finding 11); missing the capability
-- routes to the unendorsed action, fail-safe. The last conjunct GENERALIZES the old
-- `¬ already-tainted` conjunct (Task 7/8) to both dimensions (Task 12): when NEITHER
-- dimension helps, the crossing is pointless and routes unendorsed with zero debit — the
-- wasted-budget generalization (design §6 "Neither-dimension-helps crossings").
-- Used POSITIVELY by `invoke_complete_endorsed` and NEGATIVELY (syntactic negation, not a
-- re-derived condition) by `invoke_complete_unendorsed`, so the split is a total,
-- complementary partition and the environment's choice between the two actions is forced —
-- zero semantic change versus the old embedded conditional.
--
-- Deliberately NOT `@[irreducible]`: `#kav_check_action`'s `collectUnfoldNamesTransitive`
-- (`kav/Kav/CheckAction.lean`) transitively unfolds every non-irreducible, non-denylisted
-- `def` reachable from the goal, so a plain `def` here is inlined automatically at every gate
-- site exactly as the old textual duplication was. `irreducible` is reserved for defs the
-- cascades must NOT see through (e.g. `ceilingAdmits`, whose existential blows up congruence
-- closure) — `crossing_ok`'s conjuncts are exactly what the invariants need exposed, so
-- keeping it (and `conf_helps`/`integ_helps`/`crossing_weight`) transparent is what keeps the
-- checks automatic.
def crossing_ok
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (a : AgentId) (inv : InvocationId) : Prop :=
  s.tool_output_bounded (s.invocation_tool inv)
    ∧ s.invocation_conforms inv
    ∧ s.agent_cap a s.cap_declassify
    ∧ s.affordable a (crossing_weight s a inv)
    ∧ (conf_helps s a inv ∨ integ_helps s a inv)

-- invoke_complete_endorsed (Veil lines 619-654, endorsed branch — split per design
-- "invoke_complete shape": complementary total guards instead of one embedded conditional, so
-- each branch of the Rust kernel's `if/else` refines exactly one spec action). Requires
-- `crossing_ok` positively: removes in_flight (point-clear) and self-debits the
-- dimension-adjusted `crossing_weight`. No taint/integ insert — the crossing was clean.
open Classical in
kav_action invoke_complete_endorsed (a : AgentId) (inv : InvocationId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.in_flight a inv
  require s.agent_active a
  require crossing_ok s a inv
  in_flight := fun A I => s.in_flight A I ∧ ¬ (A = a ∧ I = inv)
  agent_budget := fun A =>
    if A = a then s.agent_budget a - crossing_weight s a inv else s.agent_budget A

-- invoke_complete_unendorsed (Veil lines 619-654, unendorsed branch — split per design
-- "invoke_complete shape"). Requires the SYNTACTIC NEGATION of `crossing_ok`: removes
-- in_flight (point-clear) and inserts the tool's conf floor into taint AND the tool's output
-- integrity into integ (Task 12: the unendorsed branch now degrades both dimensions). No
-- budget change — an agent that cannot cross cleanly is never charged (the wasted-budget fix).
kav_action invoke_complete_unendorsed (a : AgentId) (inv : InvocationId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.in_flight a inv
  require s.agent_active a
  require ¬ crossing_ok s a inv
  in_flight := fun A I => s.in_flight A I ∧ ¬ (A = a ∧ I = inv)
  taint_levels := fun A L =>
    s.taint_levels A L ∨ (A = a ∧ s.tool_conf_floor (s.invocation_tool inv) = L)
  integ_levels := fun A L =>
    s.integ_levels A L ∨ (A = a ∧ L = s.tool_output_integ (s.invocation_tool inv))

-- return_endorsed (Veil lines 674-688). Capability-gated, recipient-budget-charged
-- cross-boundary declassification. Both dimensions are now declared, coverage-guarded, and
-- weighted (Task 12): `clvl` bounds the child's held taint set, `ilvl` LOWER-bounds the
-- child's held integ set (integrity is a meet/min lattice — the declared level must sit
-- at-or-below every level the child holds, dual of `clvl`'s at-or-above bound); debit is
-- `declass_weight clvl + integ_weight ilvl`. Endorsed return blocks BOTH propagations — no
-- `taint_levels` update (unchanged since Task 8) and no `integ_levels` update (new here): the
-- parent absorbs nothing of either set, only pays for the declaration.
-- Level-parameterized weighted debit (design §4 "Return debit" / §5.4 "Weighted endorsed
-- return", closes the child-laundering arbitrage: flat pricing undercharged a restricted
-- return relative to the restricted invoke it shortcuts). The caller declares `clvl`/`ilvl`;
-- the coverage requires verify the declarations bound the child's entire sets; the debit
-- follows the declarations, not the sets themselves. A clean child returns at
-- `(clvl, ilvl) = (public, attested)` for debit 0 (`declass_weight public = integ_weight
-- attested = 0`) — endorsing nothing costs nothing.
-- Robust declassification (design §5.5, Zdancewic/Myers): the CHILD is the declassifying
-- party here, so it is the child's held integrity that must clear the shared lever floor, or
-- sit in the lever's vouchable inspect band. The vouch is `return_conforms child prnt` — this
-- action's existing conformance require doubles as the vouch (one oracle, no new relation,
-- consistent with the unified-crossing philosophy). This makes the vouch arm honest but
-- partially redundant with the `return_conforms` require above; it is kept anyway for
-- shape-fidelity with the design's graduated-gate shape and forward-compat in case the two
-- requires ever decouple. Untrusted influence cannot reach this lever: the headline claim
-- strengthens from "can't fire destructive tools" to "can't fire destructive tools AND can't
-- launder anything past the lattice."
open Classical in
kav_action return_endorsed (child prnt : AgentId) (clvl : ConfLevel) (ilvl : IntegLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent child prnt
  require s.agent_active child
  require s.agent_active prnt
  require ∀ I, ¬ s.in_flight child I
  require s.agent_cap child s.cap_declassify
  require s.return_conforms child prnt
  -- Robust declassification lever floor (Task 13): the child's held integrity clears the
  -- lever, or sits in the inspect band vouched by `return_conforms` (already required above).
  require ∀ L, s.integ_levels child L → s.lever_allows L ∨ (s.lever_inspects L ∧ s.return_conforms child prnt)
  -- Coverage: the declared level bounds the child's entire taint set.
  require ∀ L, s.taint_levels child L → le_conf L clvl
  -- Coverage: the declared integ level LOWER-bounds the child's entire integ set.
  require ∀ L, s.integ_levels child L → le_integ ilvl L
  require s.affordable prnt (declass_weight clvl + integ_weight ilvl)
  agent_budget := fun A =>
    if A = prnt
    then s.agent_budget prnt - (declass_weight clvl + integ_weight ilvl)
    else s.agent_budget A

-- return_unendorsed (Veil lines 708-732). Parent inherits child's taint set; flow-gated
-- against parent's in-flight tools; eager override consumption (marks used whenever the
-- gate examined an armed pair, regardless of another arm admitting the flow).
-- Task 12: the parent ALSO inherits the child's integ set, gated against the parent's
-- in-flight tools' integrity floors (graduated, vouchable, no override arm — endorsement is
-- the only way up, so the integ side has no eager-consumption clause to mirror).
kav_action return_unendorsed (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent child prnt
  require s.agent_active child
  require s.agent_active prnt
  require ∀ I, ¬ s.in_flight child I
  require ∀ L I E,
    s.taint_levels child L ∧ s.in_flight prnt I ∧ s.invocation_egress I E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.invocation_gate_passes I)
      ∨ (s.flow_override prnt (s.invocation_tool I) L
          ∧ ¬ s.override_used prnt (s.invocation_tool I) L)
  require ∀ L I,
    s.integ_levels child L ∧ s.in_flight prnt I →
      s.integ_allows L (s.invocation_tool I)
      ∨ (s.integ_inspects L (s.invocation_tool I) ∧ s.invocation_gate_passes I)
  taint_levels := fun A L => s.taint_levels A L ∨ (A = prnt ∧ s.taint_levels child L)
  integ_levels := fun A L => s.integ_levels A L ∨ (A = prnt ∧ s.integ_levels child L)
  override_used := fun A T L =>
    s.override_used A T L
    ∨ (A = prnt ∧ s.taint_levels child L
        ∧ (∃ I, s.in_flight prnt I ∧ T = s.invocation_tool I
           ∧ s.flow_override prnt (s.invocation_tool I) L))

-- sentinel_elevate_taint (Veil lines 751-769). Raises agent taint to `l`, flow-gated against
-- in-flight tools; CONSUMES overrides eagerly (single-use property: marked used whenever the
-- gate examined an armed pair, regardless of another arm admitting the flow).
kav_action sentinel_elevate_taint (a : AgentId) (l : ConfLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require ∀ I E,
    s.in_flight a I ∧ s.invocation_egress I E →
      s.flow_allows l E
      ∨ (s.flow_inspects l E ∧ s.invocation_gate_passes I)
      ∨ (s.flow_override a (s.invocation_tool I) l
          ∧ ¬ s.override_used a (s.invocation_tool I) l)
  override_used := fun A T L =>
    s.override_used A T L
    ∨ (A = a ∧ L = l
        ∧ (∃ I, s.in_flight a I ∧ T = s.invocation_tool I
           ∧ s.flow_override a (s.invocation_tool I) l))
  taint_levels := fun A L => s.taint_levels A L ∨ (A = a ∧ L = l)

-- sentinel_degrade_integrity (design §5.6, dual of `sentinel_elevate_taint`). The platform
-- reports ingestion at level `l` (an LLM completion over degraded context, or content
-- delivery) — inserts `l` into `integ_levels`, gated against every in-flight tool's floor
-- (graduated, vouchable). Blocked degrade = the Warden must HOLD the ingestion, never skip
-- the record (design §6 platform obligation: an in-flight invocation's parameters predate
-- the ingestion). NO override arm — endorsement is the only way up.
kav_action sentinel_degrade_integrity (a : AgentId) (l : IntegLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require ∀ I,
    s.in_flight a I →
      s.integ_allows l (s.invocation_tool I)
      ∨ (s.integ_inspects l (s.invocation_tool I) ∧ s.invocation_gate_passes I)
  integ_levels := fun A L => s.integ_levels A L ∨ (A = a ∧ L = l)

-- sentinel_credit_budget (Veil lines 780-784). Capability-gated budget credit of `n`,
-- saturating at capacity (a full refresh = credit `budget_capacity`).
open Classical in
kav_action sentinel_credit_budget (a : AgentId) (n : Nat) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require s.agent_cap a s.cap_credit_budget
  agent_budget := fun A =>
    if A = a then budget_saturating_credit (s.agent_budget a) n else s.agent_budget A

-- grant_override (Campaign A, 13th action). Capability-gated, granter-budget-debited
-- arming/re-arming of a single-use flow override for (target, tool, lvl). The re-arm
-- guard (target has no in-flight invocations) makes both single-use invariants vacuous
-- for the target at grant time. Self-grant (granter = target) is legal — the guard then
-- binds the granter.
-- Weighted debit (design §4 "Return debit" / §5.4 "Weighted override grant"): the primitive
-- that pushes data through a DENY band is priced by the level it arms, not a flat 1 — closes
-- the cheap-override arbitrage. Public-level overrides are free, deliberately: public data
-- through a deny-all channel is harmless.
-- Robust declassification (design §5.5, Zdancewic/Myers): the GRANTER, not the target, is the
-- declassifying party arming this lever, so it is the granter's held integrity that must clear
-- the lever floor — STRICT, two-verdict, no inspect/vouch arm. Unlike `return_endorsed` there
-- is no conformance object to vouch a near-miss granter with, so a degraded granter has no
-- band at all. Untrusted influence cannot reach this lever: the headline claim strengthens
-- from "can't fire destructive tools" to "can't fire destructive tools AND can't launder
-- anything past the lattice."
open Classical in
kav_action grant_override (granter target : AgentId) (tool : ToolId) (lvl : ConfLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active granter
  require s.agent_active target
  require s.agent_cap granter s.cap_grant_override
  -- Robust declassification lever floor (Task 13): strict, no vouch arm.
  require ∀ L, s.integ_levels granter L → s.lever_allows L
  require s.affordable granter (declass_weight lvl)
  require ∀ (I : InvocationId), ¬ s.in_flight target I
  flow_override := fun A T L =>
    s.flow_override A T L ∨ (A = target ∧ T = tool ∧ L = lvl)
  override_used := fun A T L =>
    s.override_used A T L ∧ ¬ (A = target ∧ T = tool ∧ L = lvl)
  agent_budget := fun A =>
    if A = granter then s.agent_budget granter - declass_weight lvl else s.agent_budget A

/-! ## Full 15-action transition system -/

def system : Kav.TransitionSystem
    (St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) :=
  { init := initial
    actions :=
      [ ("register_tool",              Kav.close1 register_tool)
      , ("unregister_tool",            Kav.close1 unregister_tool)
      , ("load_instruction",           Kav.close2 load_instruction)
      , ("delegate",                   Kav.close2 delegate)
      , ("grant_capability",           Kav.close3 grant_capability)
      , ("revoke",                     Kav.close2 revoke)
      , ("cascade_revoke",             Kav.close2 cascade_revoke)
      , ("invoke_start",               Kav.close3 invoke_start)
      , ("invoke_complete_endorsed",   Kav.close2 invoke_complete_endorsed)
      , ("invoke_complete_unendorsed", Kav.close2 invoke_complete_unendorsed)
      , ("return_endorsed",            Kav.close4 return_endorsed)
      , ("return_unendorsed",          Kav.close2 return_unendorsed)
      , ("sentinel_elevate_taint",     Kav.close2 sentinel_elevate_taint)
      , ("sentinel_degrade_integrity", Kav.close2 sentinel_degrade_integrity)
      , ("sentinel_credit_budget",     Kav.close2 sentinel_credit_budget)
      , ("grant_override",             Kav.close4 grant_override) ] }

end Tzimtzum
