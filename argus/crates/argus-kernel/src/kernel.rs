use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::collections::VecSet;
use crate::error::KernelError;
use crate::event::{KernelAction, KernelEvent};
use crate::state::KernelState;
use crate::traits::{AuthorizerOracle, ConformanceOracle, ContentGateOracle, EventStore};
use crate::transitions;
use crate::types::{AgentId, ConfLevel, EgressKind, InstructionId, IntegLevel, InvocationId, ToolId};

pub struct Kernel<
    A: AuthorizerOracle,
    C: ContentGateOracle,
    F: ConformanceOracle,
    E: EventStore,
> {
    state: KernelState,
    background: BackgroundTheory,
    sequence: u64,
    authorizer: A,
    content_gate: C,
    conformance: F,
    events: E,
}

impl<A: AuthorizerOracle, C: ContentGateOracle, F: ConformanceOracle, E: EventStore>
    Kernel<A, C, F, E>
{
    pub fn new(
        background: BackgroundTheory,
        authorizer: A,
        content_gate: C,
        conformance: F,
        events: E,
    ) -> Self {
        Self {
            state: KernelState::initial(),
            background,
            sequence: 0,
            authorizer,
            content_gate,
            conformance,
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

    pub fn load_instruction(
        &mut self,
        agent: AgentId,
        instr: InstructionId,
    ) -> Result<KernelEvent, KernelError> {
        let result =
            transitions::load_instruction(self.state.clone(), &self.background, agent, instr);
        self.apply(result)
    }

    pub fn delegate(
        &mut self,
        grantor: AgentId,
        grantee: AgentId,
    ) -> Result<KernelEvent, KernelError> {
        let result = transitions::delegate(self.state.clone(), &self.background, grantor, grantee);
        self.apply(result)
    }

    pub fn grant_capability(
        &mut self,
        parent: AgentId,
        child: AgentId,
        cap: CapKind,
    ) -> Result<KernelEvent, KernelError> {
        let result =
            transitions::grant_capability(self.state.clone(), &self.background, parent, child, cap);
        self.apply(result)
    }

    pub fn revoke(&mut self, parent: AgentId, target: AgentId) -> Result<KernelEvent, KernelError> {
        let result = transitions::revoke(self.state.clone(), &self.background, parent, target);
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
        attested_egress: VecSet<EgressKind>,
    ) -> Result<KernelEvent, KernelError> {
        let result = transitions::invoke_start(
            self.state.clone(),
            &self.background,
            &self.authorizer,
            &self.content_gate,
            agent,
            tool,
            inv,
            attested_egress,
        );
        self.apply(result)
    }

    pub fn invoke_complete(
        &mut self,
        agent: AgentId,
        inv: InvocationId,
    ) -> Result<KernelEvent, KernelError> {
        let result = transitions::invoke_complete(
            self.state.clone(),
            &self.background,
            &self.conformance,
            agent,
            inv,
        );
        self.apply(result)
    }

    pub fn return_endorsed(
        &mut self,
        child: AgentId,
        parent: AgentId,
        clvl: ConfLevel,
        ilvl: IntegLevel,
    ) -> Result<KernelEvent, KernelError> {
        let result = transitions::return_endorsed(
            self.state.clone(),
            &self.background,
            &self.conformance,
            child,
            parent,
            clvl,
            ilvl,
        );
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

    pub fn sentinel_elevate_taint(
        &mut self,
        agent: AgentId,
        level: ConfLevel,
    ) -> Result<KernelEvent, KernelError> {
        self.apply(transitions::sentinel_elevate_taint(
            self.state.clone(),
            &self.background,
            &self.content_gate,
            agent,
            level,
        ))
    }

    pub fn sentinel_degrade_integrity(
        &mut self,
        agent: AgentId,
        level: IntegLevel,
    ) -> Result<KernelEvent, KernelError> {
        self.apply(transitions::sentinel_degrade_integrity(
            self.state.clone(),
            &self.background,
            &self.content_gate,
            agent,
            level,
        ))
    }

    pub fn sentinel_credit_budget(
        &mut self,
        agent: AgentId,
        amount: u8,
    ) -> Result<KernelEvent, KernelError> {
        self.apply(transitions::sentinel_credit_budget(
            self.state.clone(),
            &self.background,
            agent,
            amount,
        ))
    }

    pub fn grant_override(
        &mut self,
        granter: AgentId,
        target: AgentId,
        tool: ToolId,
        level: ConfLevel,
    ) -> Result<KernelEvent, KernelError> {
        self.apply(transitions::grant_override(
            self.state.clone(),
            &self.background,
            granter,
            target,
            tool,
            level,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheory, BackgroundTheoryBuilder, ToolMetadata};
    use crate::types::{ConfLevel, EgressKind, IntegLevel, IssuerId};
    use std::cell::RefCell;
    use crate::collections::VecSet;

    struct AllowAll;
    impl AuthorizerOracle for AllowAll {
        fn allows(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct PassAll;
    impl ContentGateOracle for PassAll {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct ConformsAll;
    impl ConformanceOracle for ConformsAll {
        fn conforms(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
        fn return_conforms(
            &self,
            _: &AgentId,
            _: &AgentId,
            _: &KernelState,
            _: &BackgroundTheory,
        ) -> bool {
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
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("read_file"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::FilesystemRead]),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        builder.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        let bg = builder.build();

        let store = VecStore::new();
        let mut kernel = Kernel::new(bg, AllowAll, PassAll, ConformsAll, store);

        let e1 = kernel.register_tool(ToolId::new("read_file")).unwrap();
        assert_eq!(e1.sequence, 1);

        let e2 = kernel
            .delegate(AgentId::root(), AgentId::new("a1"))
            .unwrap();
        assert_eq!(e2.sequence, 2);

        let e3 = kernel
            .grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead)
            .unwrap();
        assert_eq!(e3.sequence, 3);

        // return_endorsed is now a cross-boundary declassification: the child needs cap_declassify.
        let e4 = kernel
            .grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::Declassify)
            .unwrap();
        assert_eq!(e4.sequence, 4);

        let e5 = kernel
            .invoke_start(
                AgentId::new("a1"),
                ToolId::new("read_file"),
                InvocationId::new("inv-1"),
                VecSet::new(),
            )
            .unwrap();
        assert_eq!(e5.sequence, 5);

        let e6 = kernel
            .invoke_complete(AgentId::new("a1"), InvocationId::new("inv-1"))
            .unwrap();
        assert_eq!(e6.sequence, 6);
        assert!(
            kernel
                .state()
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive)
        );

        let e7 = kernel
            .return_endorsed(
                AgentId::new("a1"),
                AgentId::root(),
                ConfLevel::Sensitive,
                IntegLevel::Attested,
            )
            .unwrap();
        assert_eq!(e7.sequence, 7);

        let e8 = kernel.revoke(AgentId::root(), AgentId::new("a1")).unwrap();
        assert_eq!(e8.sequence, 8);
        assert!(!kernel.state().agent_active.contains(&AgentId::new("a1")));
    }

    #[test]
    fn event_store_receives_all_events() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("t"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();
        let store = VecStore::new();
        let mut kernel = Kernel::new(bg, AllowAll, PassAll, ConformsAll, store);

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
        let mut kernel = Kernel::new(bg, AllowAll, PassAll, ConformsAll, store);

        let result = kernel.register_tool(ToolId::new("unknown"));
        assert!(result.is_err());
        assert_eq!(kernel.sequence(), 0);
    }

    #[test]
    fn kernel_load_instruction_records_provenance() {
        use crate::types::{InstructionId, IssuerId};
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_instruction(InstructionId::new("sys"), IssuerId::new("trusted"));
        let bg = builder.build();

        let store = VecStore::new();
        let mut kernel = Kernel::new(bg, AllowAll, PassAll, ConformsAll, store);
        kernel
            .delegate(AgentId::root(), AgentId::new("a1"))
            .unwrap();
        let ev = kernel
            .load_instruction(AgentId::new("a1"), InstructionId::new("sys"))
            .unwrap();
        assert_eq!(ev.sequence, 2);
        assert!(
            kernel
                .state()
                .agent_instruction
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&InstructionId::new("sys"))
        );
    }
}
