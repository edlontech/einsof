use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::error::KernelError;
use crate::event::{KernelAction, KernelEvent};
use crate::state::KernelState;
use crate::traits::EventStore;
use crate::transitions;
use crate::types::{AgentId, AssignmentDigest, ToolId};

/// The stateful V4 kernel driver. Structural commands are wired here; the invocation/crossing
/// commands (needing the authorizer + egress-classifier oracles) arrive in Tasks A4–A5, which
/// extend the generic parameter list. Every command appends its event before advancing state, so
/// an event-store failure leaves state and sequence unchanged.
pub struct Kernel<E: EventStore> {
    state: KernelState,
    background: BackgroundTheory,
    sequence: u64,
    events: E,
}

impl<E: EventStore> Kernel<E> {
    pub fn new(background: BackgroundTheory, events: E) -> Self {
        Self {
            state: KernelState::initial(),
            background,
            sequence: 0,
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::BackgroundTheoryBuilder;
    use crate::types::CrossingKey;
    use std::cell::RefCell;

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

    fn kernel() -> Kernel<VecStore> {
        Kernel::new(BackgroundTheoryBuilder::new().build(), VecStore::new())
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
        let mut k = Kernel::new(BackgroundTheoryBuilder::new().build(), FailStore);
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
}
