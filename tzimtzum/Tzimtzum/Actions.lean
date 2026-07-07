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
  in_flight := fun A I => s.in_flight A I ∧ A ≠ child
  override_used := fun A T L => s.override_used A T L ∧ A ≠ child
  flow_override := fun A T L => s.flow_override A T L ∧ A ≠ child

-- invoke_start (Veil lines 550-606). THE BIG ONE: CHECK 1 + 2a + 2b + 2c + 3,
-- override_used full-redefinition (clauses 2a/2c/2b), and the in_flight point-set.
-- Eager consumption (design doc "Override consumption semantics"): an armed override is
-- marked used whenever the gate examined a pair it was armed for, regardless of whether
-- another arm (ALLOW / INSPECT+gate) would have admitted the flow — no negated gate arms,
-- no inner egress existentials.
kav_action invoke_start (a : AgentId) (tool : ToolId) (inv : InvocationId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require a ≠ s.root_agent
  require s.tool_registered tool
  require s.invocation_tool inv = tool
  require ∀ AG, ¬ s.in_flight AG inv
  -- CHECK 1: Capability gate
  require ∀ C, s.tool_cap tool C → s.agent_cap a C
  -- CHECK 2a: Flow gate (existing speculative taint × new tool's egress). The vouch is the
  -- NEW invocation's content-gate verdict.
  require ∀ L E,
    Tzimtzum.speculative_taint s a L ∧ s.tool_egress tool E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.invocation_gate_passes inv)
      ∨ (s.flow_override a tool L ∧ ¬ s.override_used a tool L)
  -- CHECK 2b: Flow gate (new tool's taint × existing in-flight's egress). The vouch is the
  -- IN-FLIGHT invocation I's content-gate verdict (being re-examined against the new floor).
  require ∀ I E,
    s.in_flight a I ∧ s.tool_egress (s.invocation_tool I) E →
      s.flow_allows (s.tool_conf_floor tool) E
      ∨ (s.flow_inspects (s.tool_conf_floor tool) E
          ∧ s.invocation_gate_passes I)
      ∨ (s.flow_override a (s.invocation_tool I) (s.tool_conf_floor tool)
          ∧ ¬ s.override_used a (s.invocation_tool I) (s.tool_conf_floor tool))
  -- CHECK 2c: Self-flow gate (tool's own taint × its own egress). The vouch is again the
  -- NEW invocation's content-gate verdict.
  require ∀ E,
    s.tool_egress tool E →
      s.flow_allows (s.tool_conf_floor tool) E
      ∨ (s.flow_inspects (s.tool_conf_floor tool) E ∧ s.invocation_gate_passes inv)
      ∨ (s.flow_override a tool (s.tool_conf_floor tool)
          ∧ ¬ s.override_used a tool (s.tool_conf_floor tool))
  -- CHECK 3: Authorizer gate, keyed on this invocation.
  require s.invocation_authorized inv
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

-- invoke_complete (Veil lines 619-654). Removes in_flight (point-clear), conditionally adds
-- taint, and self-debits the weighted budget on the endorsed (zero-taint) path. The endorsed
-- predicate (inlined at each site, no `let` in action bodies) is the 4-conjunct
--   `endorsed := output_bounded ∧ invocation_conforms ∧ affordable (declass_weight floor)
--                ∧ ¬ already-tainted-at-floor`
-- where `floor = s.tool_conf_floor (s.invocation_tool inv)`. An agent already tainted at
-- `floor` takes the `¬ endorsed` branch: idempotent taint insert, ZERO debit (the
-- wasted-budget fix).
open Classical in
kav_action invoke_complete (a : AgentId) (inv : InvocationId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.in_flight a inv
  require s.agent_active a
  in_flight := fun A I => s.in_flight A I ∧ ¬ (A = a ∧ I = inv)
  taint_levels := fun A L =>
    s.taint_levels A L
    ∨ (A = a
        ∧ ¬ (s.tool_output_bounded (s.invocation_tool inv)
                ∧ s.invocation_conforms inv
                ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
                ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
        ∧ s.tool_conf_floor (s.invocation_tool inv) = L)
  agent_budget := fun A =>
    if A = a then
      if s.tool_output_bounded (s.invocation_tool inv)
          ∧ s.invocation_conforms inv
          ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
          ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv))
      then s.agent_budget a - declass_weight (s.tool_conf_floor (s.invocation_tool inv))
      else s.agent_budget a
    else s.agent_budget A

-- return_endorsed (Veil lines 674-688). Capability-gated, recipient-budget-charged
-- cross-boundary declassification (no taint propagation).
open Classical in
kav_action return_endorsed (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent child prnt
  require s.agent_active child
  require s.agent_active prnt
  require ∀ I, ¬ s.in_flight child I
  require s.agent_cap child s.cap_declassify
  require s.return_conforms child prnt
  require s.affordable prnt 2
  agent_budget := fun A => if A = prnt then s.agent_budget prnt - 2 else s.agent_budget A

-- return_unendorsed (Veil lines 708-732). Parent inherits child's taint set; flow-gated
-- against parent's in-flight tools; eager override consumption (marks used whenever the
-- gate examined an armed pair, regardless of another arm admitting the flow).
kav_action return_unendorsed (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent child prnt
  require s.agent_active child
  require s.agent_active prnt
  require ∀ I, ¬ s.in_flight child I
  require ∀ L I E,
    s.taint_levels child L ∧ s.in_flight prnt I ∧ s.tool_egress (s.invocation_tool I) E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.invocation_gate_passes I)
      ∨ (s.flow_override prnt (s.invocation_tool I) L
          ∧ ¬ s.override_used prnt (s.invocation_tool I) L)
  taint_levels := fun A L => s.taint_levels A L ∨ (A = prnt ∧ s.taint_levels child L)
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
    s.in_flight a I ∧ s.tool_egress (s.invocation_tool I) E →
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
open Classical in
kav_action grant_override (granter target : AgentId) (tool : ToolId) (lvl : ConfLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active granter
  require s.agent_active target
  require s.agent_cap granter s.cap_grant_override
  require s.affordable granter 1
  require ∀ (I : InvocationId), ¬ s.in_flight target I
  flow_override := fun A T L =>
    s.flow_override A T L ∨ (A = target ∧ T = tool ∧ L = lvl)
  override_used := fun A T L =>
    s.override_used A T L ∧ ¬ (A = target ∧ T = tool ∧ L = lvl)
  agent_budget := fun A => if A = granter then s.agent_budget granter - 1 else s.agent_budget A

/-! ## Full 13-action transition system -/

def system : Kav.TransitionSystem
    (St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) :=
  { init := initial
    actions :=
      [ ("register_tool",          Kav.close1 register_tool)
      , ("load_instruction",       Kav.close2 load_instruction)
      , ("delegate",               Kav.close2 delegate)
      , ("grant_capability",       Kav.close3 grant_capability)
      , ("revoke",                 Kav.close2 revoke)
      , ("cascade_revoke",         Kav.close2 cascade_revoke)
      , ("invoke_start",           Kav.close3 invoke_start)
      , ("invoke_complete",        Kav.close2 invoke_complete)
      , ("return_endorsed",        Kav.close2 return_endorsed)
      , ("return_unendorsed",      Kav.close2 return_unendorsed)
      , ("sentinel_elevate_taint", Kav.close2 sentinel_elevate_taint)
      , ("sentinel_credit_budget", Kav.close2 sentinel_credit_budget)
      , ("grant_override",         Kav.close4 grant_override) ] }

end Tzimtzum
