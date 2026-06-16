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

-- delegate (Veil lines 426-441).
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
  agent_budget := fun G L =>
    (G = grantee ∧ L = BudgetLevel.bl5) ∨ (s.agent_budget G L ∧ G ≠ grantee)
  in_flight := fun A I => s.in_flight A I ∧ A ≠ grantee
  gh_taint_invoked := fun A L => s.gh_taint_invoked A L ∧ A ≠ grantee
  gh_taint_received := fun A L => s.gh_taint_received A L ∧ A ≠ grantee
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

-- revoke (Veil lines 467-482).
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
  agent_budget := fun A L => s.agent_budget A L ∧ A ≠ target
  in_flight := fun A I => s.in_flight A I ∧ A ≠ target
  gh_taint_invoked := fun A L => s.gh_taint_invoked A L ∧ A ≠ target
  gh_taint_received := fun A L => s.gh_taint_received A L ∧ A ≠ target
  override_used := fun A T L => s.override_used A T L ∧ A ≠ target
  flow_override := fun A T L => s.flow_override A T L ∧ A ≠ target

-- cascade_revoke (Veil lines 505-520).
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
  agent_budget := fun A L => s.agent_budget A L ∧ A ≠ child
  in_flight := fun A I => s.in_flight A I ∧ A ≠ child
  gh_taint_invoked := fun A L => s.gh_taint_invoked A L ∧ A ≠ child
  gh_taint_received := fun A L => s.gh_taint_received A L ∧ A ≠ child
  override_used := fun A T L => s.override_used A T L ∧ A ≠ child
  flow_override := fun A T L => s.flow_override A T L ∧ A ≠ child

-- invoke_start (Veil lines 550-606). THE BIG ONE: CHECK 1 + 2a + 2b + 2c + 3,
-- override_used full-redefinition (clauses 2a/2c/2b), and the in_flight point-set.
kav_action invoke_start (a : AgentId) (tool : ToolId) (inv : InvocationId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require a ≠ s.root_agent
  require s.tool_registered tool
  require s.invocation_tool inv = tool
  require ∀ AG, ¬ s.in_flight AG inv
  -- CHECK 1: Capability gate
  require ∀ C, s.tool_cap tool C → s.agent_cap a C
  -- CHECK 2a: Flow gate (existing speculative taint × new tool's egress)
  require ∀ L E,
    Tzimtzum.speculative_taint s a L ∧ s.tool_egress tool E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.content_gate_passes a tool)
      ∨ (s.flow_override a tool L ∧ ¬ s.override_used a tool L)
  -- CHECK 2b: Flow gate (new tool's taint × existing in-flight's egress)
  require ∀ I E,
    s.in_flight a I ∧ s.tool_egress (s.invocation_tool I) E →
      s.flow_allows (s.tool_conf_floor tool) E
      ∨ (s.flow_inspects (s.tool_conf_floor tool) E
          ∧ s.content_gate_passes a (s.invocation_tool I))
      ∨ (s.flow_override a (s.invocation_tool I) (s.tool_conf_floor tool)
          ∧ ¬ s.override_used a (s.invocation_tool I) (s.tool_conf_floor tool))
  -- CHECK 2c: Self-flow gate (tool's own taint × its own egress)
  require ∀ E,
    s.tool_egress tool E →
      s.flow_allows (s.tool_conf_floor tool) E
      ∨ (s.flow_inspects (s.tool_conf_floor tool) E ∧ s.content_gate_passes a tool)
      ∨ (s.flow_override a tool (s.tool_conf_floor tool)
          ∧ ¬ s.override_used a tool (s.tool_conf_floor tool))
  -- CHECK 3: Authorizer gate
  require s.authorizer_allows a tool
  override_used := fun A T L =>
    s.override_used A T L
    -- 2a: new tool admitted against existing speculative taint L
    ∨ (A = a ∧ T = tool ∧ s.flow_override a tool L ∧ Tzimtzum.speculative_taint s a L
        ∧ (∃ E, s.tool_egress tool E
           ∧ ¬ s.flow_allows L E
           ∧ ¬ (s.flow_inspects L E ∧ s.content_gate_passes a tool)))
    -- 2c: new tool's own floor against its own egress
    ∨ (A = a ∧ T = tool ∧ L = s.tool_conf_floor tool
        ∧ s.flow_override a tool (s.tool_conf_floor tool)
        ∧ (∃ E, s.tool_egress tool E
           ∧ ¬ s.flow_allows (s.tool_conf_floor tool) E
           ∧ ¬ (s.flow_inspects (s.tool_conf_floor tool) E ∧ s.content_gate_passes a tool)))
    -- 2b: pre-existing in-flight tool I against new tool's floor (keyed on I's tool)
    ∨ (A = a ∧ L = s.tool_conf_floor tool
        ∧ (∃ I, s.in_flight a I ∧ T = s.invocation_tool I
           ∧ s.flow_override a (s.invocation_tool I) (s.tool_conf_floor tool)
           ∧ (∃ E, s.tool_egress (s.invocation_tool I) E
              ∧ ¬ s.flow_allows (s.tool_conf_floor tool) E
              ∧ ¬ (s.flow_inspects (s.tool_conf_floor tool) E
                      ∧ s.content_gate_passes a (s.invocation_tool I)))))
  in_flight := fun A I => s.in_flight A I ∨ (A = a ∧ I = inv)

-- invoke_complete (Veil lines 619-654). Removes in_flight (point-clear), conditionally adds
-- taint, and self-debits the weighted budget on the endorsed (zero-taint) path. The endorsed
-- predicate (inlined at each site, no `let` in action bodies) is the 4-conjunct
--   `endorsed := output_bounded ∧ output_conforms ∧ affordable (declass_weight floor)
--                ∧ ¬ already-tainted-at-floor`
-- where `floor = s.tool_conf_floor (s.invocation_tool inv)`. An agent already tainted at
-- `floor` takes the `¬ endorsed` branch: idempotent taint insert, ZERO debit (the
-- wasted-budget fix).
kav_action invoke_complete (a : AgentId) (inv : InvocationId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.in_flight a inv
  require s.agent_active a
  in_flight := fun A I => s.in_flight A I ∧ ¬ (A = a ∧ I = inv)
  taint_levels := fun A L =>
    s.taint_levels A L
    ∨ (A = a
        ∧ ¬ (s.tool_output_bounded (s.invocation_tool inv)
                ∧ s.output_conforms a (s.invocation_tool inv)
                ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
                ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
        ∧ s.tool_conf_floor (s.invocation_tool inv) = L)
  gh_taint_invoked := fun A L =>
    s.gh_taint_invoked A L
    ∨ (A = a
        ∧ ¬ (s.tool_output_bounded (s.invocation_tool inv)
                ∧ s.output_conforms a (s.invocation_tool inv)
                ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
                ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
        ∧ s.tool_conf_floor (s.invocation_tool inv) = L)
  agent_budget := fun A L =>
    (A = a ∧
      ( ( (s.tool_output_bounded (s.invocation_tool inv)
           ∧ s.output_conforms a (s.invocation_tool inv)
           ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
           ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
          ∧ ∀ b, s.agent_budget a b →
              L = b - declass_weight (s.tool_conf_floor (s.invocation_tool inv)) )
        ∨ ( ¬ (s.tool_output_bounded (s.invocation_tool inv)
               ∧ s.output_conforms a (s.invocation_tool inv)
               ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
               ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
            ∧ s.agent_budget a L ) ))
    ∨ (A ≠ a ∧ s.agent_budget A L)

-- return_endorsed (Veil lines 674-688). Capability-gated, recipient-budget-charged
-- cross-boundary declassification (no taint propagation).
kav_action return_endorsed (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent child prnt
  require s.agent_active child
  require s.agent_active prnt
  require ∀ I, ¬ s.in_flight child I
  require s.agent_cap child s.cap_declassify
  require True
  require ¬ s.agent_budget prnt BudgetLevel.bl_exhausted
  agent_budget := fun A L =>
    (A = prnt
      ∧ ( (s.agent_budget prnt BudgetLevel.bl5 ∧ L = BudgetLevel.bl4)
       ∨ (s.agent_budget prnt BudgetLevel.bl4 ∧ L = BudgetLevel.bl3)
       ∨ (s.agent_budget prnt BudgetLevel.bl3 ∧ L = BudgetLevel.bl2)
       ∨ (s.agent_budget prnt BudgetLevel.bl2 ∧ L = BudgetLevel.bl1)
       ∨ (s.agent_budget prnt BudgetLevel.bl1 ∧ L = BudgetLevel.bl_exhausted) ))
    ∨ (A ≠ prnt ∧ s.agent_budget A L)

-- return_unendorsed (Veil lines 708-732). Parent inherits child's taint set; flow-gated
-- against parent's in-flight tools; consumes overrides used as sole justification.
kav_action return_unendorsed (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_parent child prnt
  require s.agent_active child
  require s.agent_active prnt
  require ∀ I, ¬ s.in_flight child I
  require ∀ L I E,
    s.taint_levels child L ∧ s.in_flight prnt I ∧ s.tool_egress (s.invocation_tool I) E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.content_gate_passes prnt (s.invocation_tool I))
      ∨ (s.flow_override prnt (s.invocation_tool I) L
          ∧ ¬ s.override_used prnt (s.invocation_tool I) L)
  taint_levels := fun A L => s.taint_levels A L ∨ (A = prnt ∧ s.taint_levels child L)
  gh_taint_received := fun A L => s.gh_taint_received A L ∨ (A = prnt ∧ s.taint_levels child L)
  override_used := fun A T L =>
    s.override_used A T L
    ∨ (A = prnt ∧ s.taint_levels child L
        ∧ (∃ I, s.in_flight prnt I ∧ T = s.invocation_tool I
           ∧ s.flow_override prnt (s.invocation_tool I) L
           ∧ (∃ E, s.tool_egress (s.invocation_tool I) E
              ∧ ¬ s.flow_allows L E
              ∧ ¬ (s.flow_inspects L E ∧ s.content_gate_passes prnt (s.invocation_tool I)))))

-- sentinel_elevate_taint (Veil lines 751-769). Raises agent taint to `l`, flow-gated against
-- in-flight tools; CONSUMES overrides (single-use property).
kav_action sentinel_elevate_taint (a : AgentId) (l : ConfLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require ∀ I E,
    s.in_flight a I ∧ s.tool_egress (s.invocation_tool I) E →
      s.flow_allows l E
      ∨ (s.flow_inspects l E ∧ s.content_gate_passes a (s.invocation_tool I))
      ∨ (s.flow_override a (s.invocation_tool I) l
          ∧ ¬ s.override_used a (s.invocation_tool I) l)
  override_used := fun A T L =>
    s.override_used A T L
    ∨ (A = a ∧ L = l
        ∧ (∃ I, s.in_flight a I ∧ T = s.invocation_tool I
           ∧ s.flow_override a (s.invocation_tool I) l
           ∧ (∃ E, s.tool_egress (s.invocation_tool I) E
              ∧ ¬ s.flow_allows l E
              ∧ ¬ (s.flow_inspects l E ∧ s.content_gate_passes a (s.invocation_tool I)))))
  taint_levels := fun A L => s.taint_levels A L ∨ (A = a ∧ L = l)
  gh_taint_invoked := fun A L => s.gh_taint_invoked A L ∨ (A = a ∧ L = l)

-- sentinel_refresh_budget (Veil lines 780-784). Capability-gated budget reset to full.
kav_action sentinel_refresh_budget (a : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active a
  require s.agent_cap a s.cap_refresh_budget
  agent_budget := fun A L => (A = a ∧ L = BudgetLevel.bl5) ∨ (A ≠ a ∧ s.agent_budget A L)

-- grant_override (Campaign A, 13th action). Capability-gated, granter-budget-debited
-- arming/re-arming of a single-use flow override for (target, tool, lvl). The re-arm
-- guard (target has no in-flight invocations) makes both single-use invariants vacuous
-- for the target at grant time. Self-grant (granter = target) is legal — the guard then
-- binds the granter.
kav_action grant_override (granter target : AgentId) (tool : ToolId) (lvl : ConfLevel) :
    St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId where
  require s.agent_active granter
  require s.agent_active target
  require s.agent_cap granter s.cap_grant_override
  require ¬ s.agent_budget granter BudgetLevel.bl_exhausted
  require ∀ (I : InvocationId), ¬ s.in_flight target I
  flow_override := fun A T L =>
    s.flow_override A T L ∨ (A = target ∧ T = tool ∧ L = lvl)
  override_used := fun A T L =>
    s.override_used A T L ∧ ¬ (A = target ∧ T = tool ∧ L = lvl)
  agent_budget := fun A L =>
    (A = granter
      ∧ ( (s.agent_budget granter BudgetLevel.bl5 ∧ L = BudgetLevel.bl4)
       ∨ (s.agent_budget granter BudgetLevel.bl4 ∧ L = BudgetLevel.bl3)
       ∨ (s.agent_budget granter BudgetLevel.bl3 ∧ L = BudgetLevel.bl2)
       ∨ (s.agent_budget granter BudgetLevel.bl2 ∧ L = BudgetLevel.bl1)
       ∨ (s.agent_budget granter BudgetLevel.bl1 ∧ L = BudgetLevel.bl_exhausted) ))
    ∨ (A ≠ granter ∧ s.agent_budget A L)

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
      , ("sentinel_refresh_budget", Kav.close1 sentinel_refresh_budget)
      , ("grant_override",         Kav.close4 grant_override) ] }

end Tzimtzum
