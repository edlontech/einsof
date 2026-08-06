use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::collections::VecSet;
use crate::error::KernelError;
use crate::event::{KernelAction, KernelEvent};
use crate::state::KernelState;
use crate::traits::{AuthorizerOracle, EventStore};
use crate::transitions;
use crate::types::{
    ActionPolicySnapshot, AgentId, AssignmentDigest, ChallengeId, ConfLevel, ContentHash,
    CrossInput, EgressKind, InspectionAttestation, IntegLevel, InvocationId, Outcome,
    ResolutionAttestation, ToolId,
};

/// The stateful V4 kernel driver. Structural commands are wired here; the invocation/crossing
/// commands (needing the authorizer + egress-classifier oracles) arrive in Tasks A4–A5, which
/// extend the generic parameter list. Every command appends its event before advancing state, so
/// an event-store failure leaves state and sequence unchanged.
pub struct Kernel<A: AuthorizerOracle, E: EventStore> {
    state: KernelState,
    background: BackgroundTheory,
    sequence: u64,
    authorizer: A,
    events: E,
}

impl<A: AuthorizerOracle, E: EventStore> Kernel<A, E> {
    pub fn new(background: BackgroundTheory, authorizer: A, events: E) -> Self {
        Self {
            state: KernelState::initial(),
            background,
            sequence: 0,
            authorizer,
            events,
        }
    }

    pub fn state(&self) -> &KernelState {
        &self.state
    }

    pub fn background(&self) -> &BackgroundTheory {
        &self.background
    }

    pub fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Append-before-commit: append the event, and only on success advance the sequence and adopt
    /// the new state. On append failure state and sequence are unchanged.
    fn apply(
        &mut self,
        result: Result<(KernelState, KernelAction), KernelError>,
    ) -> Result<KernelEvent, KernelError> {
        let (new_state, action) = result?;
        let next_seq = self.sequence + 1;
        let event = KernelEvent::new(next_seq, action);
        self.events.append(&event)?;
        self.sequence = next_seq;
        self.state = new_state;
        Ok(event)
    }

    pub fn register_tool(&mut self, tool: ToolId) -> Result<KernelEvent, KernelError> {
        let r = transitions::register_tool(self.state.clone(), tool);
        self.apply(r)
    }

    pub fn unregister_tool(&mut self, tool: ToolId) -> Result<KernelEvent, KernelError> {
        let r = transitions::unregister_tool(self.state.clone(), tool);
        self.apply(r)
    }

    pub fn delegate(
        &mut self,
        grantor: AgentId,
        grantee: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let r = transitions::delegate(self.state.clone(), &self.background, grantor, grantee);
        self.apply(r)
    }

    pub fn grant_capability(
        &mut self,
        parent: AgentId,
        child: AgentId,
        cap: CapKind,
    ) -> Result<KernelEvent, KernelError> {
        let r = transitions::grant_capability(self.state.clone(), parent, child, cap);
        self.apply(r)
    }

    pub fn grant_crossing(
        &mut self,
        grantor: AgentId,
        agent: AgentId,
        assignment: AssignmentDigest,
        n: u32,
    ) -> Result<KernelEvent, KernelError> {
        let r = transitions::grant_crossing(
            self.state.clone(),
            &self.background,
            grantor,
            agent,
            assignment,
            n,
        );
        self.apply(r)
    }

    pub fn revoke(&mut self, parent: AgentId, target: AgentId) -> Result<KernelEvent, KernelError> {
        let r = transitions::revoke(self.state.clone(), &self.background, parent, target);
        self.apply(r)
    }

    pub fn cascade_revoke(
        &mut self,
        child: AgentId,
        parent: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let r = transitions::cascade_revoke(self.state.clone(), &self.background, child, parent);
        self.apply(r)
    }

    pub fn ingest(
        &mut self,
        agent: AgentId,
        src: Option<AgentId>,
        pconf: ConfLevel,
        pinteg: IntegLevel,
    ) -> Result<KernelEvent, KernelError> {
        let r = transitions::ingest(
            self.state.clone(),
            &self.background,
            agent,
            src,
            pconf,
            pinteg,
        );
        self.apply(r)
    }

    pub fn settle_invocation(
        &mut self,
        inv: InvocationId,
        outcome: Outcome,
        att: Option<ResolutionAttestation>,
    ) -> Result<KernelEvent, KernelError> {
        let r = transitions::settle_invocation(self.state.clone(), inv, outcome, att);
        self.apply(r)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn begin_invocation(
        &mut self,
        agent: AgentId,
        inv: InvocationId,
        chal: ChallengeId,
        snap: ActionPolicySnapshot,
        attested_egress: VecSet<EgressKind>,
        args_hash: ContentHash,
    ) -> Result<KernelEvent, KernelError> {
        // The authorizer verdict is a per-invocation oracle input (OracleFidelity).
        let authorized =
            self.authorizer
                .allows(&agent, &snap.tool, &inv, &self.state, &self.background);
        let r = transitions::begin_invocation(
            self.state.clone(),
            &self.background,
            agent,
            inv,
            chal,
            snap,
            attested_egress,
            args_hash,
            authorized,
        );
        self.apply(r)
    }

    pub fn authorize_inspected(
        &mut self,
        inv: InvocationId,
        att: InspectionAttestation,
    ) -> Result<KernelEvent, KernelError> {
        let r = transitions::authorize_inspected(self.state.clone(), &self.background, inv, att);
        self.apply(r)
    }

    pub fn cross_output(&mut self, q: CrossInput) -> Result<KernelEvent, KernelError> {
        let r = transitions::cross_output(self.state.clone(), &self.background, q);
        self.apply(r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::BackgroundTheoryBuilder;
    use crate::collections::VecSet;
    use crate::types::{
        ActionPolicySnapshot, Admission, AttestationId, ChallengeId, ConfLevel,
        ConformanceAttestation, ContentHash, CrossInput, CrossingId, CrossingKey, Disposition,
        EgressKind, Fallback, InspectionAttestation, IntegLevel, Mode, PendingInvocation,
        PolicyDigest,
    };
    use std::cell::RefCell;

    fn snap(
        clearance: ConfLevel,
        integ_floor: IntegLevel,
        integ_inspect: IntegLevel,
        oc: ConfLevel,
        oi: IntegLevel,
        egress: VecSet<EgressKind>,
    ) -> ActionPolicySnapshot {
        ActionPolicySnapshot {
            tool: ToolId::new("t"),
            required_caps: VecSet::new(),
            conf_clearance: clearance,
            integ_floor,
            integ_inspect,
            output_conf: oc,
            output_integ: oi,
            declared_egress: egress.clone(),
            policy_digest: PolicyDigest::new("d"),
        }
    }

    fn permitted(agent: &str, policy: ActionPolicySnapshot) -> PendingInvocation {
        let egress = policy.declared_egress.clone();
        PendingInvocation {
            agent: AgentId::new(agent),
            policy,
            egress,
            admission: Admission::Plain,
            disposition: Disposition::Permitted,
            authorized: true,
            quarantined: false,
        }
    }

    struct VecStore(RefCell<Vec<KernelEvent>>);
    impl VecStore {
        fn new() -> Self {
            Self(RefCell::new(Vec::new()))
        }
        fn len(&self) -> usize {
            self.0.borrow().len()
        }
    }
    impl EventStore for VecStore {
        fn append(&self, event: &KernelEvent) -> Result<(), KernelError> {
            self.0.borrow_mut().push(event.clone());
            Ok(())
        }
    }

    struct FailStore;
    impl EventStore for FailStore {
        fn append(&self, _: &KernelEvent) -> Result<(), KernelError> {
            Err(KernelError::EventStore)
        }
    }

    struct AllowAll;
    impl AuthorizerOracle for AllowAll {
        fn allows(
            &self,
            _: &AgentId,
            _: &ToolId,
            _: &InvocationId,
            _: &KernelState,
            _: &BackgroundTheory,
        ) -> bool {
            true
        }
    }

    struct DenyAll;
    impl AuthorizerOracle for DenyAll {
        fn allows(
            &self,
            _: &AgentId,
            _: &ToolId,
            _: &InvocationId,
            _: &KernelState,
            _: &BackgroundTheory,
        ) -> bool {
            false
        }
    }

    fn kernel() -> Kernel<AllowAll, VecStore> {
        Kernel::new(
            BackgroundTheoryBuilder::new().build(),
            AllowAll,
            VecStore::new(),
        )
    }

    #[test]
    fn structural_lifecycle_sequences_and_mutates() {
        let mut k = kernel();
        assert_eq!(k.register_tool(ToolId::new("t")).unwrap().sequence, 1);
        assert_eq!(
            k.delegate(AgentId::root(), AgentId::new("a1"))
                .unwrap()
                .sequence,
            2
        );
        assert_eq!(
            k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead)
                .unwrap()
                .sequence,
            3
        );
        assert!(
            k.state()
                .agent_cap
                .set_contains(&AgentId::new("a1"), &CapKind::FilesystemRead)
        );

        assert_eq!(
            k.grant_crossing(
                AgentId::root(),
                AgentId::new("a1"),
                AssignmentDigest::new("d"),
                3
            )
            .unwrap()
            .sequence,
            4
        );
        let key = CrossingKey {
            agent: AgentId::new("a1"),
            assignment: AssignmentDigest::new("d"),
        };
        assert_eq!(
            k.state()
                .crossing_grants
                .get_cloned(&key)
                .unwrap()
                .remaining,
            3
        );

        assert_eq!(
            k.revoke(AgentId::root(), AgentId::new("a1"))
                .unwrap()
                .sequence,
            5
        );
        assert!(!k.state().agent_active.contains(&AgentId::new("a1")));
        // revocation destroys the grant but never the sequence/history.
        assert!(k.state().crossing_grants.get_cloned(&key).is_none());
    }

    #[test]
    fn ingest_permitted_with_no_pending_absorbs_pair() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.ingest(
            AgentId::new("a1"),
            None,
            ConfLevel::Sensitive,
            IntegLevel::Standard,
        )
        .unwrap();
        assert!(
            k.state()
                .taint_levels
                .set_contains(&AgentId::new("a1"), &ConfLevel::Sensitive)
        );
        assert!(
            k.state()
                .integ_levels
                .set_contains(&AgentId::new("a1"), &IntegLevel::Standard)
        );
    }

    #[test]
    fn ingest_refused_in_enforce_when_clearance_hold_fails() {
        let mut k = kernel(); // enforce
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        // pending record of a1 whose clearance is Public: ingesting Sensitive breaks its clearance.
        k.state.pending.insert(
            InvocationId::new("inv"),
            permitted(
                "a1",
                snap(
                    ConfLevel::Public,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Public,
                    IntegLevel::Attested,
                    VecSet::new(),
                ),
            ),
        );
        assert_eq!(
            k.ingest(
                AgentId::new("a1"),
                None,
                ConfLevel::Sensitive,
                IntegLevel::Attested
            )
            .unwrap_err(),
            KernelError::IngestHoldFailed
        );
    }

    #[test]
    fn ingest_monitor_bypass_demotes_and_absorbs() {
        let mut k = Kernel::new(
            {
                let mut b = BackgroundTheoryBuilder::new();
                b.set_mode(Mode::Monitor);
                b.build()
            },
            AllowAll,
            VecStore::new(),
        );
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.state.pending.insert(
            InvocationId::new("inv"),
            permitted(
                "a1",
                snap(
                    ConfLevel::Public,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Public,
                    IntegLevel::Attested,
                    VecSet::new(),
                ),
            ),
        );
        k.ingest(
            AgentId::new("a1"),
            None,
            ConfLevel::Sensitive,
            IntegLevel::Attested,
        )
        .unwrap();
        assert_eq!(
            k.state()
                .pending
                .get_cloned(&InvocationId::new("inv"))
                .unwrap()
                .disposition,
            Disposition::MonitorBypassed
        );
        assert!(
            k.state()
                .taint_levels
                .set_contains(&AgentId::new("a1"), &ConfLevel::Sensitive)
        );
    }

    #[test]
    fn ingest_rejects_undominated_a2a_provenance() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("src")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.state
            .taint_levels
            .insert_into(AgentId::new("src"), ConfLevel::Restricted);
        // Declaring the delivery as Public under-taints the Restricted source.
        assert_eq!(
            k.ingest(
                AgentId::new("a1"),
                Some(AgentId::new("src")),
                ConfLevel::Public,
                IntegLevel::Attested
            )
            .unwrap_err(),
            KernelError::ProvenanceNotDominated
        );
    }

    #[test]
    fn settle_success_absorbs_both_dimensions_and_closes() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.state.pending.insert(
            InvocationId::new("inv"),
            permitted(
                "a1",
                snap(
                    ConfLevel::Restricted,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Sensitive,
                    IntegLevel::Untrusted,
                    VecSet::new(),
                ),
            ),
        );
        k.settle_invocation(InvocationId::new("inv"), Outcome::Success, None)
            .unwrap();
        assert!(
            k.state()
                .pending
                .get_cloned(&InvocationId::new("inv"))
                .is_none()
        );
        assert!(
            k.state()
                .taint_levels
                .set_contains(&AgentId::new("a1"), &ConfLevel::Sensitive)
        );
        assert!(
            k.state()
                .integ_levels
                .set_contains(&AgentId::new("a1"), &IntegLevel::Untrusted)
        );
    }

    #[test]
    fn settle_ambiguous_quarantines_and_absorbs_nothing() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.state.pending.insert(
            InvocationId::new("inv"),
            permitted(
                "a1",
                snap(
                    ConfLevel::Restricted,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Sensitive,
                    IntegLevel::Untrusted,
                    VecSet::new(),
                ),
            ),
        );
        k.settle_invocation(InvocationId::new("inv"), Outcome::Ambiguous, None)
            .unwrap();
        assert!(
            k.state()
                .pending
                .get_cloned(&InvocationId::new("inv"))
                .unwrap()
                .quarantined
        );
        assert!(
            !k.state()
                .taint_levels
                .set_contains(&AgentId::new("a1"), &ConfLevel::Sensitive)
        );
    }

    #[test]
    fn quarantined_settles_only_with_scoped_one_use_attestation() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        let mut rec = permitted(
            "a1",
            snap(
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
                IntegLevel::Untrusted,
                ConfLevel::Sensitive,
                IntegLevel::Untrusted,
                VecSet::new(),
            ),
        );
        rec.quarantined = true;
        k.state.pending.insert(InvocationId::new("inv"), rec);
        // No attestation -> rejected.
        assert_eq!(
            k.settle_invocation(InvocationId::new("inv"), Outcome::Success, None)
                .unwrap_err(),
            KernelError::ResolutionAttestationInvalid
        );
        // Scoped one-use attestation -> closes and consumes.
        let att = ResolutionAttestation {
            id: AttestationId::new("att1"),
            inv: InvocationId::new("inv"),
            outcome: Outcome::Success,
        };
        k.settle_invocation(InvocationId::new("inv"), Outcome::Success, Some(att))
            .unwrap();
        assert!(
            k.state()
                .pending
                .get_cloned(&InvocationId::new("inv"))
                .is_none()
        );
        assert!(
            k.state()
                .consumed_attestations
                .contains(&AttestationId::new("att1"))
        );
    }

    #[test]
    fn non_quarantined_settlement_forbids_an_attestation() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.state.pending.insert(
            InvocationId::new("inv"),
            permitted(
                "a1",
                snap(
                    ConfLevel::Restricted,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Public,
                    IntegLevel::Attested,
                    VecSet::new(),
                ),
            ),
        );
        let att = ResolutionAttestation {
            id: AttestationId::new("att1"),
            inv: InvocationId::new("inv"),
            outcome: Outcome::Success,
        };
        assert_eq!(
            k.settle_invocation(InvocationId::new("inv"), Outcome::Success, Some(att))
                .unwrap_err(),
            KernelError::NotQuarantined
        );
    }

    #[test]
    fn begin_allow_pends_a_permitted_plain_record() {
        let mut k = kernel();
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.begin_invocation(
            AgentId::new("a1"),
            InvocationId::new("inv"),
            ChallengeId::new("c"),
            snap(
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
                IntegLevel::Untrusted,
                ConfLevel::Public,
                IntegLevel::Attested,
                VecSet::new(),
            ),
            VecSet::new(),
            ContentHash::new("ah"),
        )
        .unwrap();
        let rec = k
            .state()
            .pending
            .get_cloned(&InvocationId::new("inv"))
            .unwrap();
        assert_eq!(rec.disposition, Disposition::Permitted);
        assert_eq!(rec.admission, Admission::Plain);
        assert!(k.state().consumed_ids.contains(&InvocationId::new("inv")));
    }

    #[test]
    fn begin_rejects_replayed_invocation_id() {
        let mut k = kernel();
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        let go = |k: &mut Kernel<AllowAll, VecStore>| {
            k.begin_invocation(
                AgentId::new("a1"),
                InvocationId::new("inv"),
                ChallengeId::new("c"),
                snap(
                    ConfLevel::Restricted,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Public,
                    IntegLevel::Attested,
                    VecSet::new(),
                ),
                VecSet::new(),
                ContentHash::new("ah"),
            )
        };
        go(&mut k).unwrap();
        // The record settles (freeing the pending slot) but consumed_ids retains the id.
        k.settle_invocation(InvocationId::new("inv"), Outcome::Success, None)
            .unwrap();
        assert_eq!(go(&mut k).unwrap_err(), KernelError::InvocationReplayed);
    }

    #[test]
    fn enforce_inspection_creates_challenge_then_resolves_to_inspected_permit() {
        let mut k = kernel();
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        // Sensitive output over an egress whose allow ceiling is Internal, inspect ceiling Sensitive:
        // strict flow fails, admissible flow passes -> inspection_required.
        k.background = {
            let mut b = BackgroundTheoryBuilder::new();
            b.set_egress_ceilings(
                EgressKind::NetworkExternal,
                Some(ConfLevel::Internal),
                Some(ConfLevel::Sensitive),
            );
            b.build()
        };
        let egress = VecSet::from([EgressKind::NetworkExternal]);
        k.begin_invocation(
            AgentId::new("a1"),
            InvocationId::new("inv"),
            ChallengeId::new("c"),
            snap(
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
                IntegLevel::Untrusted,
                ConfLevel::Sensitive,
                IntegLevel::Attested,
                egress,
            ),
            VecSet::from([EgressKind::NetworkExternal]),
            ContentHash::new("ah"),
        )
        .unwrap();
        assert!(k.state().challenges.contains_key(&InvocationId::new("inv")));
        assert!(!k.state().pending.contains_key(&InvocationId::new("inv")));

        // Positive, scope-matching attestation -> live gate re-admits -> inspected permit.
        let att = InspectionAttestation {
            id: AttestationId::new("att1"),
            inv: InvocationId::new("inv"),
            challenge: ChallengeId::new("c"),
            args_hash: ContentHash::new("ah"),
            policy_digest: PolicyDigest::new("d"),
            positive: true,
        };
        k.authorize_inspected(InvocationId::new("inv"), att)
            .unwrap();
        let rec = k
            .state()
            .pending
            .get_cloned(&InvocationId::new("inv"))
            .unwrap();
        assert_eq!(rec.disposition, Disposition::Permitted);
        assert_eq!(
            rec.admission,
            Admission::Inspected(AttestationId::new("att1"))
        );
        assert!(!k.state().challenges.contains_key(&InvocationId::new("inv")));
        assert!(
            k.state()
                .consumed_attestations
                .contains(&AttestationId::new("att1"))
        );
    }

    #[test]
    fn scope_mismatched_attestation_leaves_challenge_open() {
        let mut k = kernel();
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.background = {
            let mut b = BackgroundTheoryBuilder::new();
            b.set_egress_ceilings(
                EgressKind::NetworkExternal,
                Some(ConfLevel::Internal),
                Some(ConfLevel::Sensitive),
            );
            b.build()
        };
        k.begin_invocation(
            AgentId::new("a1"),
            InvocationId::new("inv"),
            ChallengeId::new("c"),
            snap(
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
                IntegLevel::Untrusted,
                ConfLevel::Sensitive,
                IntegLevel::Attested,
                VecSet::from([EgressKind::NetworkExternal]),
            ),
            VecSet::from([EgressKind::NetworkExternal]),
            ContentHash::new("ah"),
        )
        .unwrap();
        let bad = InspectionAttestation {
            id: AttestationId::new("att1"),
            inv: InvocationId::new("inv"),
            challenge: ChallengeId::new("WRONG"),
            args_hash: ContentHash::new("ah"),
            policy_digest: PolicyDigest::new("d"),
            positive: true,
        };
        assert_eq!(
            k.authorize_inspected(InvocationId::new("inv"), bad)
                .unwrap_err(),
            KernelError::ChallengeScopeMismatch
        );
        // Challenge survives the boundary rejection (E24); no attestation consumed.
        assert!(k.state().challenges.contains_key(&InvocationId::new("inv")));
        assert!(
            !k.state()
                .consumed_attestations
                .contains(&AttestationId::new("att1"))
        );
    }

    /// Register `t`, delegate `a1`, set NetworkExternal ceilings (allow=Internal, inspect=Sensitive)
    /// and begin a Sensitive-output invocation over that egress -> opens an enforce-mode challenge.
    fn open_challenge(k: &mut Kernel<AllowAll, VecStore>) {
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.background = {
            let mut b = BackgroundTheoryBuilder::new();
            b.set_egress_ceilings(
                EgressKind::NetworkExternal,
                Some(ConfLevel::Internal),
                Some(ConfLevel::Sensitive),
            );
            b.build()
        };
        k.begin_invocation(
            AgentId::new("a1"),
            InvocationId::new("inv"),
            ChallengeId::new("c"),
            snap(
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
                IntegLevel::Untrusted,
                ConfLevel::Sensitive,
                IntegLevel::Attested,
                VecSet::from([EgressKind::NetworkExternal]),
            ),
            VecSet::from([EgressKind::NetworkExternal]),
            ContentHash::new("ah"),
        )
        .unwrap();
    }

    fn positive_att() -> InspectionAttestation {
        InspectionAttestation {
            id: AttestationId::new("att1"),
            inv: InvocationId::new("inv"),
            challenge: ChallengeId::new("c"),
            args_hash: ContentHash::new("ah"),
            policy_digest: PolicyDigest::new("d"),
            positive: true,
        }
    }

    #[test]
    fn monitor_mode_deny_pends_a_bypassed_record() {
        let mut k = Kernel::new(
            {
                let mut b = BackgroundTheoryBuilder::new();
                b.set_mode(Mode::Monitor);
                b.build()
            },
            DenyAll,
            VecStore::new(),
        );
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.begin_invocation(
            AgentId::new("a1"),
            InvocationId::new("inv"),
            ChallengeId::new("c"),
            snap(
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
                IntegLevel::Untrusted,
                ConfLevel::Public,
                IntegLevel::Attested,
                VecSet::new(),
            ),
            VecSet::new(),
            ContentHash::new("ah"),
        )
        .unwrap();
        let rec = k
            .state()
            .pending
            .get_cloned(&InvocationId::new("inv"))
            .unwrap();
        assert_eq!(rec.disposition, Disposition::MonitorBypassed);
        assert_eq!(rec.admission, Admission::Bypassed);
    }

    #[test]
    fn one_use_attestation_replay_rejected_challenge_survives() {
        let mut k = kernel();
        open_challenge(&mut k);
        k.state
            .consumed_attestations
            .insert(AttestationId::new("att1"));
        assert_eq!(
            k.authorize_inspected(InvocationId::new("inv"), positive_att())
                .unwrap_err(),
            KernelError::AttestationConsumed
        );
        assert!(k.state().challenges.contains_key(&InvocationId::new("inv")));
    }

    #[test]
    fn positive_attestation_denied_by_live_gate_closes_fail_closed() {
        let mut k = kernel();
        open_challenge(&mut k);
        // Tighten policy so the live re-evaluation no longer admits the Sensitive egress.
        k.background = BackgroundTheoryBuilder::new().build();
        k.authorize_inspected(InvocationId::new("inv"), positive_att())
            .unwrap();
        assert!(!k.state().pending.contains_key(&InvocationId::new("inv")));
        assert!(!k.state().challenges.contains_key(&InvocationId::new("inv")));
        assert!(
            k.state()
                .consumed_attestations
                .contains(&AttestationId::new("att1"))
        );
    }

    #[test]
    fn begin_authorizer_denied_is_typed_in_enforce() {
        let mut k = Kernel::new(
            BackgroundTheoryBuilder::new().build(),
            DenyAll,
            VecStore::new(),
        );
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        assert_eq!(
            k.begin_invocation(
                AgentId::new("a1"),
                InvocationId::new("inv"),
                ChallengeId::new("c"),
                snap(
                    ConfLevel::Restricted,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Public,
                    IntegLevel::Attested,
                    VecSet::new(),
                ),
                VecSet::new(),
                ContentHash::new("ah"),
            )
            .unwrap_err(),
            KernelError::AuthorizerDenied
        );
    }

    #[test]
    fn grant_crossing_is_root_only() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a2")).unwrap();
        let err = k
            .grant_crossing(
                AgentId::new("a1"),
                AgentId::new("a2"),
                AssignmentDigest::new("d"),
                1,
            )
            .unwrap_err();
        assert_eq!(err, KernelError::NotRoot);
    }

    #[test]
    fn grant_crossing_is_idempotent_set_to_n() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        let key = CrossingKey {
            agent: AgentId::new("a1"),
            assignment: AssignmentDigest::new("d"),
        };
        k.grant_crossing(
            AgentId::root(),
            AgentId::new("a1"),
            AssignmentDigest::new("d"),
            2,
        )
        .unwrap();
        k.grant_crossing(
            AgentId::root(),
            AgentId::new("a1"),
            AssignmentDigest::new("d"),
            2,
        )
        .unwrap();
        let g = k.state().crossing_grants.get_cloned(&key).unwrap();
        assert_eq!(g.remaining, 2);
        assert_eq!(g.provisioned, 2);
    }

    #[test]
    fn cascade_revoke_after_parent_gone() {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("p")).unwrap();
        k.delegate(AgentId::new("p"), AgentId::new("c")).unwrap();
        // revoke the parent: child is orphaned-but-active until cascade.
        k.revoke(AgentId::root(), AgentId::new("p")).unwrap();
        assert!(k.state().agent_active.contains(&AgentId::new("c")));
        // cannot re-delegate the parent id while it still parents an active child.
        assert_eq!(
            k.delegate(AgentId::root(), AgentId::new("p")).unwrap_err(),
            KernelError::AgentHasChildren
        );
        k.cascade_revoke(AgentId::new("c"), AgentId::new("p"))
            .unwrap();
        assert!(!k.state().agent_active.contains(&AgentId::new("c")));
    }

    #[test]
    fn unregister_blocked_by_pending_reference() {
        use crate::collections::VecSet;
        use crate::types::{
            ActionPolicySnapshot, Admission, Disposition, InvocationId, PendingInvocation,
            PolicyDigest,
        };
        use crate::types::{ConfLevel, IntegLevel};

        let mut k = kernel();
        k.register_tool(ToolId::new("t")).unwrap();
        // Splice a pending record naming the tool directly into state (begin_invocation lands A4).
        k.state.pending.insert(
            InvocationId::new("inv"),
            PendingInvocation {
                agent: AgentId::new("a"),
                policy: ActionPolicySnapshot {
                    tool: ToolId::new("t"),
                    required_caps: VecSet::new(),
                    conf_clearance: ConfLevel::Restricted,
                    integ_floor: IntegLevel::Untrusted,
                    integ_inspect: IntegLevel::Untrusted,
                    output_conf: ConfLevel::Public,
                    output_integ: IntegLevel::Attested,
                    declared_egress: VecSet::new(),
                    policy_digest: PolicyDigest::new("d"),
                },
                egress: VecSet::new(),
                admission: Admission::Plain,
                disposition: Disposition::Permitted,
                authorized: true,
                quarantined: false,
            },
        );
        assert_eq!(
            k.unregister_tool(ToolId::new("t")).unwrap_err(),
            KernelError::ToolInUse
        );
    }

    #[test]
    fn event_store_failure_leaves_state_and_sequence_unchanged() {
        let mut k = Kernel::new(BackgroundTheoryBuilder::new().build(), AllowAll, FailStore);
        assert_eq!(
            k.register_tool(ToolId::new("t")).unwrap_err(),
            KernelError::EventStore
        );
        assert_eq!(k.sequence(), 0);
        assert!(k.state().tool_registered.is_empty());
    }

    #[test]
    fn all_events_reach_the_store() {
        let mut k = kernel();
        k.register_tool(ToolId::new("t")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
        assert_eq!(k.events.len(), 2);
    }

    fn two_agents() -> Kernel<AllowAll, VecStore> {
        let mut k = kernel();
        k.delegate(AgentId::root(), AgentId::new("src")).unwrap();
        k.delegate(AgentId::root(), AgentId::new("rcv")).unwrap();
        k
    }

    fn cross(
        crossing: &str,
        fallback: Fallback,
        evidence: Option<ConformanceAttestation>,
    ) -> CrossInput {
        CrossInput {
            src: AgentId::new("src"),
            rcv: AgentId::new("rcv"),
            crossing: CrossingId::new(crossing),
            output_hash: ContentHash::new("out"),
            descriptor: ContentHash::new("desc"),
            fallback,
            t_integ: IntegLevel::Attested,
            t_conf: Some(ConfLevel::Public),
            assignment: AssignmentDigest::new("asg"),
            evidence,
            released_conf: ConfLevel::Public,
            released_integ: IntegLevel::Attested,
        }
    }

    #[test]
    fn endorsed_cross_releases_bounded_pair_and_decrements_grant() {
        let mut k = two_agents();
        k.grant_crossing(
            AgentId::root(),
            AgentId::new("rcv"),
            AssignmentDigest::new("asg"),
            2,
        )
        .unwrap();
        let evidence = ConformanceAttestation {
            id: AttestationId::new("att1"),
            output: ContentHash::new("out"),
            src: AgentId::new("src"),
            rcv: AgentId::new("rcv"),
            descriptor: ContentHash::new("desc"),
            assignment: AssignmentDigest::new("asg"),
            positive: true,
        };
        k.cross_output(cross("x1", Fallback::Fail, Some(evidence)))
            .unwrap();
        assert!(
            k.state()
                .taint_levels
                .set_contains(&AgentId::new("rcv"), &ConfLevel::Public)
        );
        assert!(
            k.state()
                .integ_levels
                .set_contains(&AgentId::new("rcv"), &IntegLevel::Attested)
        );
        let key = CrossingKey {
            agent: AgentId::new("rcv"),
            assignment: AssignmentDigest::new("asg"),
        };
        assert_eq!(
            k.state()
                .crossing_grants
                .get_cloned(&key)
                .unwrap()
                .remaining,
            1
        );
        assert!(
            k.state()
                .consumed_crossings
                .contains(&CrossingId::new("x1"))
        );
        assert!(
            k.state()
                .consumed_attestations
                .contains(&AttestationId::new("att1"))
        );
    }

    #[test]
    fn unendorsed_fallback_releases_source_labels() {
        let mut k = two_agents();
        k.state
            .taint_levels
            .insert_into(AgentId::new("src"), ConfLevel::Sensitive);
        k.state
            .integ_levels
            .insert_into(AgentId::new("src"), IntegLevel::Standard);
        // No grant, no evidence -> endorsedOK false -> declared release_unendorsed fallback.
        let mut q = cross("x1", Fallback::ReleaseUnendorsed, None);
        q.t_conf = None;
        k.cross_output(q).unwrap();
        assert!(
            k.state()
                .taint_levels
                .set_contains(&AgentId::new("rcv"), &ConfLevel::Sensitive)
        );
        assert!(
            k.state()
                .integ_levels
                .set_contains(&AgentId::new("rcv"), &IntegLevel::Standard)
        );
        assert!(
            k.state()
                .consumed_crossings
                .contains(&CrossingId::new("x1"))
        );
    }

    #[test]
    fn fail_fallback_releases_nothing_but_consumes_crossing() {
        let mut k = two_agents();
        k.state
            .taint_levels
            .insert_into(AgentId::new("src"), ConfLevel::Sensitive);
        k.cross_output(cross("x1", Fallback::Fail, None)).unwrap();
        assert!(
            !k.state()
                .taint_levels
                .set_contains(&AgentId::new("rcv"), &ConfLevel::Sensitive)
        );
        assert!(
            k.state()
                .consumed_crossings
                .contains(&CrossingId::new("x1"))
        );
    }

    #[test]
    fn crossing_id_is_one_use() {
        let mut k = two_agents();
        k.cross_output(cross("x1", Fallback::Fail, None)).unwrap();
        assert_eq!(
            k.cross_output(cross("x1", Fallback::Fail, None))
                .unwrap_err(),
            KernelError::CrossingReplayed
        );
    }

    #[test]
    fn source_with_pending_work_cannot_cross() {
        let mut k = two_agents();
        k.state.pending.insert(
            InvocationId::new("inv"),
            permitted(
                "src",
                snap(
                    ConfLevel::Restricted,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Public,
                    IntegLevel::Attested,
                    VecSet::new(),
                ),
            ),
        );
        assert_eq!(
            k.cross_output(cross("x1", Fallback::Fail, None))
                .unwrap_err(),
            KernelError::SourceInFlight
        );
    }

    #[test]
    fn enforce_refuses_release_that_breaks_a_receiver_permit() {
        let mut k = two_agents();
        // A Public-clearance receiver permit; an unendorsed Sensitive source label breaks its
        // clearance hold, so enforce mode refuses.
        k.state.pending.insert(
            InvocationId::new("rinv"),
            permitted(
                "rcv",
                snap(
                    ConfLevel::Public,
                    IntegLevel::Untrusted,
                    IntegLevel::Untrusted,
                    ConfLevel::Public,
                    IntegLevel::Attested,
                    VecSet::new(),
                ),
            ),
        );
        k.state
            .taint_levels
            .insert_into(AgentId::new("src"), ConfLevel::Sensitive);
        let mut q = cross("x1", Fallback::ReleaseUnendorsed, None);
        q.t_conf = None;
        assert_eq!(
            k.cross_output(q).unwrap_err(),
            KernelError::CrossingHoldFailed
        );
    }

    #[test]
    fn non_declassifying_endorsement_must_dominate_source_taint() {
        let mut k = two_agents();
        k.grant_crossing(
            AgentId::root(),
            AgentId::new("rcv"),
            AssignmentDigest::new("asg"),
            1,
        )
        .unwrap();
        k.state
            .taint_levels
            .insert_into(AgentId::new("src"), ConfLevel::Sensitive);
        let evidence = ConformanceAttestation {
            id: AttestationId::new("att1"),
            output: ContentHash::new("out"),
            src: AgentId::new("src"),
            rcv: AgentId::new("rcv"),
            descriptor: ContentHash::new("desc"),
            assignment: AssignmentDigest::new("asg"),
            positive: true,
        };
        // Non-declassifying (t_conf=None) release at Public cannot dominate a Sensitive source.
        let mut q = cross("x1", Fallback::Fail, Some(evidence));
        q.t_conf = None;
        q.released_conf = ConfLevel::Public;
        assert_eq!(
            k.cross_output(q).unwrap_err(),
            KernelError::CrossingBoundViolated
        );
    }
}
