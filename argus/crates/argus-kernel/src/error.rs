/// Structured, payload-free kernel errors. Each variant names a precondition class so the
/// extracted Lean model carries no `format!`/`Display` machinery and each `Err` corresponds to a
/// spec-guard violation. Human-readable diagnostics, if needed, belong in the (unverified) adapter,
/// not in the verified kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    /// Tool has no metadata in the background theory.
    ToolNotInTheory,
    /// Tool is already registered.
    ToolAlreadyRegistered,
    /// Tool is not registered.
    ToolNotRegistered,
    /// Issuer (of a tool or instruction) is not trusted.
    UntrustedIssuer,
    /// Instruction has no registered issuer in the background theory.
    InstructionIssuerUnknown,
    /// Named agent (actor / grantor / parent / child / target) is not active.
    AgentInactive,
    /// Grantee is already active.
    AgentAlreadyActive,
    /// The operation may not target / be performed by the root agent.
    RootNotAllowed,
    /// The agent is not a direct child of the named parent.
    NotDirectChild,
    /// Parent is still active (use `revoke`, not `cascade_revoke`).
    ParentStillActive,
    /// A required capability is missing (required tool cap / declassify / credit-budget).
    CapabilityMissing,
    /// An invocation with this id already exists.
    InvocationExists,
    /// The invocation is already in-flight.
    InvocationInFlight,
    /// The invocation is not in-flight for the agent.
    NotInFlight,
    /// The child still has in-flight invocations.
    ChildHasInFlight,
    /// The grant target still has in-flight invocations (re-arm guard).
    TargetHasInFlight,
    /// A flow-policy gate blocked the (level, egress) pair.
    FlowGateBlocked,
    /// The authorizer denied the (agent, tool) pair.
    AuthorizerDenied,
    /// A cross-boundary endorsed return failed the runtime conformance oracle.
    NotConforming,
    /// The declassification budget is exhausted.
    BudgetExhausted,
    /// An in-flight invocation has no tool binding.
    MissingToolBinding,
    /// The invocation id has already been used (freshness violation).
    InvocationReplayed,
    /// The attested egress fails narrowing (a kind outside the tool's declared set) or
    /// coverage (an empty attestation on an egress-bearing tool).
    AttestationInvalid,
    /// An integrity floor was not cleared (CHECK 4 a/b/c) -- no override arm rescues this;
    /// endorsement is the only way up.
    IntegrityFloorDenied,
    /// A declassification lever's integrity floor rejected the declassifying party
    /// (`return_endorsed`'s child or `grant_override`'s granter) -- no override arm rescues this.
    LeverIntegrityDenied,
    /// A declared confidentiality/integrity level fails to bound the child's held taint/integ
    /// sets (`return_endorsed`'s coverage guards).
    DeclarationNotCovering,
    /// The tool still has in-flight invocations (`unregister_tool`'s guard).
    ToolInFlight,
    /// The event store failed to persist an event.
    EventStore,
}
