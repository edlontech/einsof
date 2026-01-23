use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::error::KernelError;
use crate::event::{KernelAction, KernelEvent};
use crate::state::KernelState;
use crate::traits::{AuthorizerOracle, ContentGateOracle, EventStore};
use crate::transitions;
use crate::types::{AgentId, InvocationId, ToolId};

pub struct Kernel<A: AuthorizerOracle, C: ContentGateOracle, E: EventStore> {
    state: KernelState,
    background: BackgroundTheory,
    sequence: u64,
    authorizer: A,
    content_gate: C,
    events: E,
}

impl<A: AuthorizerOracle, C: ContentGateOracle, E: EventStore> Kernel<A, C, E> {
    pub fn new(
        background: BackgroundTheory,
        authorizer: A,
        content_gate: C,
        events: E,
    ) -> Self {
        Self {
            state: KernelState::initial(),
            background,
            sequence: 0,
            authorizer,
            content_gate,
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
        let result = transitions::register_tool(self.state.clone(), &self.background, tool);
        self.apply(result)
    }

    pub fn delegate(
        &mut self,
        grantor: AgentId,
        grantee: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let result =
            transitions::delegate(self.state.clone(), &self.background, grantor, grantee);
        self.apply(result)
    }

    pub fn grant_capability(
        &mut self,
        parent: AgentId,
        child: AgentId,
        cap: CapKind,
    ) -> Result<KernelEvent, KernelError> {
        let result = transitions::grant_capability(
            self.state.clone(),
            &self.background,
            parent,
            child,
            cap,
        );
        self.apply(result)
    }

    pub fn revoke(
        &mut self,
        parent: AgentId,
        target: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let result =
            transitions::revoke(self.state.clone(), &self.background, parent, target);
        self.apply(result)
    }

    pub fn cascade_revoke(
        &mut self,
        child: AgentId,
        parent: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let result =
            transitions::cascade_revoke(self.state.clone(), &self.background, child, parent);
        self.apply(result)
    }

    pub fn invoke_start(
        &mut self,
        agent: AgentId,
        tool: ToolId,
        inv: InvocationId,
    ) -> Result<KernelEvent, KernelError> {
        let result = transitions::invoke_start(
            self.state.clone(),
            &self.background,
            &self.authorizer,
            &self.content_gate,
            agent,
            tool,
            inv,
        );
        self.apply(result)
    }

    pub fn invoke_complete(
        &mut self,
        agent: AgentId,
        inv: InvocationId,
    ) -> Result<KernelEvent, KernelError> {
        let result =
            transitions::invoke_complete(self.state.clone(), &self.background, agent, inv);
        self.apply(result)
    }

    pub fn return_endorsed(
        &mut self,
        child: AgentId,
        parent: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let result =
            transitions::return_endorsed(self.state.clone(), &self.background, child, parent);
        self.apply(result)
    }

    pub fn return_unendorsed(
        &mut self,
        child: AgentId,
        parent: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let result = transitions::return_unendorsed(
            self.state.clone(),
            &self.background,
            &self.content_gate,
            child,
            parent,
        );
        self.apply(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheory, BackgroundTheoryBuilder, FlowMode, ToolMetadata};
    use crate::types::{ConfLevel, EgressKind};
    use std::cell::RefCell;
    use std::collections::BTreeSet;

    struct AllowAll;
    impl AuthorizerOracle for AllowAll {
        fn allows(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct PassAll;
    impl ContentGateOracle for PassAll {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct VecStore(RefCell<Vec<KernelEvent>>);
    impl VecStore {
        fn new() -> Self {
            Self(RefCell::new(Vec::new()))
        }
    }
    impl EventStore for VecStore {
        fn append(&self, event: &KernelEvent) -> Result<(), KernelError> {
            self.0.borrow_mut().push(event.clone());
            Ok(())
        }
    }

    #[test]
    fn full_lifecycle() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_tool(
            ToolId::new("read_file"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                endorsed: false,
            },
        );
        builder.set_flow(
            ConfLevel::Public,
            EgressKind::NetworkExternal,
            FlowMode::Allow,
        );
        let bg = builder.build();

        let store = VecStore::new();
        let mut kernel = Kernel::new(bg, AllowAll, PassAll, store);

        let e1 = kernel.register_tool(ToolId::new("read_file")).unwrap();
        assert_eq!(e1.sequence, 1);

        let e2 = kernel
            .delegate(AgentId::root(), AgentId::new("a1"))
            .unwrap();
        assert_eq!(e2.sequence, 2);

        let e3 = kernel
            .grant_capability(
                AgentId::root(),
                AgentId::new("a1"),
                CapKind::FilesystemRead,
            )
            .unwrap();
        assert_eq!(e3.sequence, 3);

        let e4 = kernel
            .invoke_start(
                AgentId::new("a1"),
                ToolId::new("read_file"),
                InvocationId::new("inv-1"),
            )
            .unwrap();
        assert_eq!(e4.sequence, 4);

        let e5 = kernel
            .invoke_complete(AgentId::new("a1"), InvocationId::new("inv-1"))
            .unwrap();
        assert_eq!(e5.sequence, 5);
        assert!(kernel
            .state()
            .taint_levels
            .get(&AgentId::new("a1"))
            .unwrap()
            .contains(&ConfLevel::Sensitive));

        let e6 = kernel
            .return_endorsed(AgentId::new("a1"), AgentId::root())
            .unwrap();
        assert_eq!(e6.sequence, 6);

        let e7 = kernel
            .revoke(AgentId::root(), AgentId::new("a1"))
            .unwrap();
        assert_eq!(e7.sequence, 7);
        assert!(!kernel.state().agent_active.contains(&AgentId::new("a1")));
    }

    #[test]
    fn event_store_receives_all_events() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_tool(
            ToolId::new("t"),
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Public,
                endorsed: true,
            },
        );
        let bg = builder.build();
        let store = VecStore::new();
        let mut kernel = Kernel::new(bg, AllowAll, PassAll, store);

        kernel.register_tool(ToolId::new("t")).unwrap();
        kernel
            .delegate(AgentId::root(), AgentId::new("a1"))
            .unwrap();

        assert_eq!(kernel.events.0.borrow().len(), 2);
        assert_eq!(kernel.events.0.borrow()[0].sequence, 1);
        assert_eq!(kernel.events.0.borrow()[1].sequence, 2);
    }

    #[test]
    fn sequence_not_incremented_on_error() {
        let bg = BackgroundTheoryBuilder::new().build();
        let store = VecStore::new();
        let mut kernel = Kernel::new(bg, AllowAll, PassAll, store);

        let result = kernel.register_tool(ToolId::new("unknown"));
        assert!(result.is_err());
        assert_eq!(kernel.sequence(), 0);
    }
}
