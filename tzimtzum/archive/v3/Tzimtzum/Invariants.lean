import Tzimtzum.Actions

/-! # TzimtzumV2 — safety properties + strengthening invariants (Kav port)

Faithful port of the Veil spec's safety properties and strengthening invariants
(`tzimtzum/TzimtzumV2.lean`, lines 799-976) into the Kav framework as `Prop`
predicates over the state, plus the assembled invariant bundle.

Translation notes:
- Veil relation/field accesses gain an `s.` prefix.
- Prop-valued state relations replace Veil's `Bool`-typed relations, so Veil's
  `R … = false` / `R … = true` become `¬ s.R …` / `s.R …`.
- Named individuals: `root_agent` → `s.root_agent`, `cl_X` → `ConfLevel.X`, etc.
- Capital quantifier binders carry explicit type annotations to avoid
  `autoImplicit` capture.

Definitions only — no proofs (proving is the next task). -/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-! ## Safety properties (Veil lines 799-907) -/

/-- **root_always_active**: the root agent can never be deactivated. -/
def root_always_active
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  s.agent_active s.root_agent

/-- **default_deny**: every in-flight invocation was explicitly authorized — the authorizer
allowed this invocation and the agent holds every capability the tool requires. -/
def default_deny
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I : InvocationId),
    s.in_flight A I →
      s.invocation_authorized I
      ∧ (∀ (C : CapKind), s.tool_cap (s.invocation_tool I) C → s.agent_cap A C)

/-- **flow_confinement**: a tainted agent's in-flight egress is permitted by the flow policy
(ALLOW, or INSPECT + content gate, or a scoped override). -/
def flow_confinement
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (L : ConfLevel) (I : InvocationId) (E : EgressKind),
    s.taint_levels A L ∧ s.in_flight A I ∧ s.invocation_egress I E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.invocation_gate_passes I)
      ∨ s.flow_override A (s.invocation_tool I) L

/-- **flow_confinement_weak**: oracle-independent flow safety — DENY-mode pairs are
structurally blocked regardless of oracle behavior. -/
def flow_confinement_weak
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (L : ConfLevel) (I : InvocationId) (E : EgressKind),
    s.taint_levels A L ∧ s.in_flight A I ∧ s.invocation_egress I E →
      s.flow_allows L E
      ∨ s.flow_inspects L E
      ∨ s.flow_override A (s.invocation_tool I) L

/-- **capability_subsumption**: for any active parent-child pair, the child's capabilities are a
subset of the parent's. -/
def capability_subsumption
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (C P : AgentId),
    s.agent_parent C P ∧ s.agent_active C ∧ s.agent_active P →
      ∀ (Cap : CapKind), s.agent_cap C Cap → s.agent_cap P Cap

/-- **revocation_clean**: inactive agents leave no residue (no in-flight invocations, no
taint, no integrity levels). -/
def revocation_clean
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I : InvocationId) (L : ConfLevel) (Li : IntegLevel),
    ¬ s.agent_active A → ¬ s.in_flight A I ∧ ¬ s.taint_levels A L ∧ ¬ s.integ_levels A Li

/-- **tool_attestation_intact**: every registered tool's labels come from a trusted issuer. -/
def tool_attestation_intact
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (T : ToolId), s.tool_registered T → s.trusted_issuer (s.tool_issuer T)

/-- **instruction_attestation_intact**: every instruction an agent operates under comes from a
trusted issuer. -/
def instruction_attestation_intact
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I : InstructionId),
    s.agent_instruction A I → s.trusted_issuer (s.instruction_issuer I)

/-- **override_consumed_when_sole_justification**: if a `flow_override` is the ONLY thing admitting
a tainted in-flight egress flow (the pair is DENY and the content gate does not pass), that
override has been consumed (`override_used`). -/
def override_consumed_when_sole_justification
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (L : ConfLevel) (I : InvocationId) (E : EgressKind),
    s.taint_levels A L ∧ s.in_flight A I ∧ s.invocation_egress I E
    ∧ ¬ s.flow_allows L E
    ∧ ¬ (s.flow_inspects L E ∧ s.invocation_gate_passes I)
    ∧ s.flow_override A (s.invocation_tool I) L →
      s.override_used A (s.invocation_tool I) L

/-- **integrity_confinement** (headline): an active agent holding integrity level `L` has no
in-flight invocation of a tool whose floor `L` fails to clear, unless the pair sits in the
inspect band with a content-gate vouch (dual of `flow_confinement`, minus the override arm —
endorsement is the only way up). -/
def integrity_confinement
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (L : IntegLevel) (I : InvocationId),
    s.integ_levels A L ∧ s.in_flight A I →
      s.integ_allows L (s.invocation_tool I)
      ∨ (s.integ_inspects L (s.invocation_tool I) ∧ s.invocation_gate_passes I)

/-- **integrity_confinement_weak**: oracle-independent integrity safety — below-inspect-band
pairs are structurally impossible regardless of oracle behavior. -/
def integrity_confinement_weak
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (L : IntegLevel) (I : InvocationId),
    s.integ_levels A L ∧ s.in_flight A I →
      s.integ_allows L (s.invocation_tool I) ∨ s.integ_inspects L (s.invocation_tool I)

/-! ## Strengthening invariants (Veil lines 909-976) -/

/-- **parent_implies_active**: the parent relation is consistent with active status. -/
def parent_implies_active
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (C P : AgentId), s.agent_parent C P → s.agent_active C

/-- **single_parent**: an active agent has at most one parent. -/
def single_parent
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (C P1 P2 : AgentId),
    s.agent_parent C P1 ∧ s.agent_parent C P2 ∧ s.agent_active C → P1 = P2

/-- **no_self_parent**: no agent is its own parent. -/
def no_self_parent
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId), ¬ s.agent_parent A A

/-- **root_no_parent**: root has no parent. -/
def root_no_parent
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (P : AgentId), ¬ s.agent_parent s.root_agent P

/-- **in_flight_active**: in-flight invocations only exist for active agents. -/
def in_flight_active
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I : InvocationId), s.in_flight A I → s.agent_active A

/-- **in_flight_registered**: in-flight invocations only exist for registered tools. -/
def in_flight_registered
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I : InvocationId), s.in_flight A I → s.tool_registered (s.invocation_tool I)

/-- **in_flight_unique**: an invocation is held by at most one agent. -/
def in_flight_unique
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A1 A2 : AgentId) (I : InvocationId), s.in_flight A1 I ∧ s.in_flight A2 I → A1 = A2

/-- **root_all_caps**: root holds every capability. -/
def root_all_caps
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (C : CapKind), s.agent_cap s.root_agent C

/-- **root_no_in_flight**: root never invokes tools directly. -/
def root_no_in_flight
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (I : InvocationId), ¬ s.in_flight s.root_agent I

/-- **budget_bounded**: every agent's budget is within capacity (keeps the state space
finite). -/
def budget_bounded
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId), s.agent_budget A ≤ budget_capacity

/-- **in_flight_flow_compat**: any two concurrent in-flight invocations for the same agent are
mutually compatible under the flow policy (I1's conf-floor taint vs I2's egress). -/
def in_flight_flow_compat
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I1 I2 : InvocationId) (E : EgressKind),
    s.in_flight A I1 ∧ s.in_flight A I2
    ∧ s.invocation_egress I2 E →
      s.flow_allows (s.tool_conf_floor (s.invocation_tool I1)) E
      ∨ (s.flow_inspects (s.tool_conf_floor (s.invocation_tool I1)) E
          ∧ s.invocation_gate_passes I2)
      ∨ s.flow_override A (s.invocation_tool I2) (s.tool_conf_floor (s.invocation_tool I1))

/-- **in_flight_override_consumed**: if two in-flight invocations are mutually flow-compatible ONLY
via an override, that override is already consumed. -/
def in_flight_override_consumed
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I1 I2 : InvocationId) (E : EgressKind),
    s.in_flight A I1 ∧ s.in_flight A I2
    ∧ s.invocation_egress I2 E
    ∧ ¬ s.flow_allows (s.tool_conf_floor (s.invocation_tool I1)) E
    ∧ ¬ (s.flow_inspects (s.tool_conf_floor (s.invocation_tool I1)) E
          ∧ s.invocation_gate_passes I2)
    ∧ s.flow_override A (s.invocation_tool I2) (s.tool_conf_floor (s.invocation_tool I1)) →
      s.override_used A (s.invocation_tool I2) (s.tool_conf_floor (s.invocation_tool I1))

/-- **in_flight_egress_attested**: every in-flight invocation's attested egress narrows to
(and, when the tool is egress-bearing, covers) its tool's declared egress set — what the
`invoke_start` narrowing/coverage requires make inductive. -/
def in_flight_egress_attested
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I : InvocationId),
    s.in_flight A I →
      (∀ (E : EgressKind), s.invocation_egress I E → s.tool_egress (s.invocation_tool I) E)
      ∧ ((∃ (E : EgressKind), s.tool_egress (s.invocation_tool I) E)
          → (∃ (E : EgressKind), s.invocation_egress I E))

/-- **in_flight_implies_used**: every in-flight invocation has been recorded in the global
freshness history — what makes the `invoke_start` freshness require inductive. -/
def in_flight_implies_used
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I : InvocationId), s.in_flight A I → s.invocation_used I

/-- **in_flight_integ_compat**: any two concurrent in-flight invocations for the same agent
(including the self-pair) are mutually compatible under the integrity gate — one's emission
clears the other's floor, or the pair sits in the inspect band with a vouch. What CHECK
4b/4c make inductive. -/
def in_flight_integ_compat
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId) : Prop :=
  ∀ (A : AgentId) (I1 I2 : InvocationId),
    s.in_flight A I1 ∧ s.in_flight A I2 →
      s.integ_allows (s.tool_output_integ (s.invocation_tool I1)) (s.invocation_tool I2)
      ∨ (s.integ_inspects (s.tool_output_integ (s.invocation_tool I1)) (s.invocation_tool I2)
          ∧ s.invocation_gate_passes I2)

/-! ## Invariant bundle

All safety properties and strengthening invariants, assembled into the single bundle Kav's
inductive check consumes (it treats safeties and invariants uniformly). -/

def allInvariants :
    List (Kav.Invariant
      (St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)) :=
  [ ("root_always_active", root_always_active)
  , ("default_deny", default_deny)
  , ("flow_confinement", flow_confinement)
  , ("flow_confinement_weak", flow_confinement_weak)
  , ("capability_subsumption", capability_subsumption)
  , ("revocation_clean", revocation_clean)
  , ("tool_attestation_intact", tool_attestation_intact)
  , ("instruction_attestation_intact", instruction_attestation_intact)
  , ("override_consumed_when_sole_justification", override_consumed_when_sole_justification)
  , ("parent_implies_active", parent_implies_active)
  , ("single_parent", single_parent)
  , ("no_self_parent", no_self_parent)
  , ("root_no_parent", root_no_parent)
  , ("in_flight_active", in_flight_active)
  , ("in_flight_registered", in_flight_registered)
  , ("in_flight_unique", in_flight_unique)
  , ("root_all_caps", root_all_caps)
  , ("root_no_in_flight", root_no_in_flight)
  , ("budget_bounded", budget_bounded)
  , ("in_flight_flow_compat", in_flight_flow_compat)
  , ("in_flight_override_consumed", in_flight_override_consumed)
  , ("in_flight_egress_attested", in_flight_egress_attested)
  , ("in_flight_implies_used", in_flight_implies_used)
  , ("integrity_confinement", integrity_confinement)
  , ("integrity_confinement_weak", integrity_confinement_weak)
  , ("in_flight_integ_compat", in_flight_integ_compat) ]

end Tzimtzum
