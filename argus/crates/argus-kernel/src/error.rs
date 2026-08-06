/// Payload-free kernel rejection reasons. Zero-dependency by design (no `thiserror`); the ex_argus
/// adapter maps these onto its own error surface. Variants are added as the V4 transitions land.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelError {
    // --- tool registry ---
    ToolAlreadyRegistered,
    ToolNotRegistered,
    /// `unregister_tool` while a pending/quarantined invocation or open challenge references it.
    ToolInUse,

    // --- agent tree / capabilities ---
    AgentInactive,
    AgentAlreadyActive,
    RootNotAllowed,
    NotDirectChild,
    ParentStillActive,
    /// `delegate` grantee id is already some active child's parent (would orphan them).
    AgentHasChildren,
    CapabilityMissing,
    /// `grant_crossing` attempted by a non-root agent.
    NotRoot,

    // --- invocation lifecycle ---
    InvocationExists,
    /// The invocation id is already in the consumed-ids history.
    InvocationReplayed,
    NotPending,
    EgressNotNarrowing,
    EgressNotCovering,
    /// The frozen snapshot's inspect floor is above its allow floor (incoherent band).
    IncoherentPolicy,
    /// A challenge is already open for this invocation id.
    ChallengeAlreadyOpen,

    // --- gates ---
    ClearanceDenied,
    FlowGateBlocked,
    AuthorizerDenied,
    IntegrityFloorDenied,
    /// A pairwise in-flight compatibility check failed in either dimension.
    PairwiseConflict,

    // --- inspection / evidence ---
    ChallengeNotOpen,
    ChallengeScopeMismatch,
    AttestationConsumed,
    InspectionNegative,

    // --- settlement / quarantine ---
    NotQuarantined,
    QuarantineResolutionRequired,
    ResolutionAttestationInvalid,

    // --- ingest ---
    IngestHoldFailed,
    ProvenanceNotDominated,

    // --- crossing ---
    CrossingReplayed,
    GrantMissing,
    GrantExhausted,
    /// The source agent still has pending (in-flight) work, so it cannot cross output.
    SourceInFlight,
    /// Endorsed release violates the frozen assignment's integrity/confidentiality bound.
    CrossingBoundViolated,
    /// A release branch's receiver holds fail under enforce mode.
    CrossingHoldFailed,

    // --- infrastructure ---
    EventStore,
}
