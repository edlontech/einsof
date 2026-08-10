//! Compile coverage for the V4 types consumed by external bindings.

use argus_kernel::{
    AgentId, AssignmentDigest, AttestationId, ChallengeId, ConfLevel, ConformanceAttestation,
    ContentHash, CrossBranch, CrossInput, CrossingId, Fallback, InspectionAttestation, IntegLevel,
    InvocationId, Outcome, PolicyDigest, ResolutionAttestation,
};

#[test]
fn constructs_v4_binding_types_from_public_exports() {
    let conformance = ConformanceAttestation {
        id: AttestationId::new("conformance"),
        output: ContentHash::new("output"),
        src: AgentId::new("source"),
        rcv: AgentId::new("receiver"),
        descriptor: ContentHash::new("descriptor"),
        assignment: AssignmentDigest::new("assignment"),
        positive: true,
    };

    let _cross_input = CrossInput {
        src: AgentId::new("source"),
        rcv: AgentId::new("receiver"),
        crossing: CrossingId::new("crossing"),
        output_hash: ContentHash::new("output"),
        descriptor: ContentHash::new("descriptor"),
        fallback: Fallback::Fail,
        t_integ: IntegLevel::Attested,
        t_conf: Some(ConfLevel::Public),
        assignment: AssignmentDigest::new("assignment"),
        evidence: Some(conformance),
        released_conf: ConfLevel::Public,
        released_integ: IntegLevel::Attested,
    };

    let _inspection = InspectionAttestation {
        id: AttestationId::new("inspection"),
        inv: InvocationId::new("invocation"),
        challenge: ChallengeId::new("challenge"),
        args_hash: ContentHash::new("arguments"),
        policy_digest: PolicyDigest::new("policy"),
        positive: true,
    };

    let _resolution = ResolutionAttestation {
        id: AttestationId::new("resolution"),
        inv: InvocationId::new("invocation"),
        outcome: Outcome::Success,
    };

    assert!(matches!(CrossBranch::Endorsed, CrossBranch::Endorsed));
}
