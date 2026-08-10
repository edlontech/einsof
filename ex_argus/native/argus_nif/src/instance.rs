use std::sync::{Mutex, TryLockError};

use argus_kernel::{BackgroundTheory, KernelState};
use rustler::{Resource, ResourceArc};

use crate::{
    BackgroundN, ChainN, CommandN, EnvelopeN, ErrorN, NativeResult, StateN, VERSION, genesis,
    limits, link,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct InstanceState {
    kernel: KernelState,
    sequence: u64,
    head: crate::DigestN,
}

impl InstanceState {
    fn initial(background: &BackgroundN) -> Self {
        Self {
            kernel: KernelState::initial(),
            sequence: 0,
            head: genesis(background),
        }
    }
}

/// A live resource cannot be passed where recovery is required, or vice versa.
///
/// ```compile_fail
/// use argus_nif::{LiveInstance, RecoveryInstance};
/// use rustler::ResourceArc;
///
/// fn apply_live(_: ResourceArc<LiveInstance>) {}
/// fn replay_recovery(_: ResourceArc<RecoveryInstance>) {}
///
/// fn cross_resource_misuse(
///     live: ResourceArc<LiveInstance>,
///     recovery: ResourceArc<RecoveryInstance>,
/// ) {
///     apply_live(recovery);
///     replay_recovery(live);
/// }
/// ```
pub struct LiveInstance {
    background: BackgroundTheory,
    inner: Mutex<InstanceState>,
}

pub struct RecoveryInstance {
    background: BackgroundTheory,
    inner: Mutex<Option<InstanceState>>,
}

#[rustler::resource_impl]
impl Resource for LiveInstance {}

#[rustler::resource_impl]
impl Resource for RecoveryInstance {}

impl LiveInstance {
    pub(crate) fn new(background: BackgroundN) -> Self {
        let state = InstanceState::initial(&background);
        Self::from_state(background.into_kernel(), state)
    }

    fn from_state(background: BackgroundTheory, state: InstanceState) -> Self {
        Self {
            background,
            inner: Mutex::new(state),
        }
    }

    pub(crate) fn status(&self) -> Result<ChainN, ErrorN> {
        let current = self.inner.try_lock().map_err(map_try_lock)?;
        Ok(ChainN {
            version: VERSION,
            sequence: current.sequence,
            head: current.head,
        })
    }

    pub(crate) fn state(&self) -> Result<StateN, ErrorN> {
        let current = self.inner.try_lock().map_err(map_try_lock)?;
        limits::check_state(&current.kernel)?;
        Ok(StateN::from_kernel(&current.kernel))
    }

    pub(crate) fn apply(&self, command: CommandN) -> Result<EnvelopeN, ErrorN> {
        let mut current = self.inner.try_lock().map_err(map_try_lock)?;
        let applied = apply_without_commit(&current, &self.background, command)?;
        *current = applied.next;
        Ok(applied.envelope)
    }
}

impl RecoveryInstance {
    pub(crate) fn new(background: BackgroundN) -> Self {
        let state = InstanceState::initial(&background);
        Self {
            background: background.into_kernel(),
            inner: Mutex::new(Some(state)),
        }
    }

    pub(crate) fn replay(&self, recorded: EnvelopeN) -> Result<(), ErrorN> {
        let mut slot = self.inner.try_lock().map_err(map_try_lock)?;
        let current = slot.as_ref().ok_or(ErrorN::RecoveryConsumed)?;
        limits::check_recovery_link(&current.kernel, current.sequence)?;
        if recorded.version != VERSION {
            return Err(ErrorN::InvalidVersion);
        }
        let expected_sequence = current
            .sequence
            .checked_add(1)
            .ok_or(ErrorN::SequenceExhausted)?;
        if recorded.sequence != expected_sequence {
            return Err(ErrorN::SequenceMismatch);
        }
        if recorded.previous_digest != current.head {
            return Err(ErrorN::PreviousDigestMismatch);
        }
        let applied = apply_without_commit(current, &self.background, recorded.command.clone())
            .map_err(|error| match error {
                ErrorN::Kernel(cause) => ErrorN::ReplayRefused(cause),
                other => other,
            })?;
        if applied.envelope.action != recorded.action {
            return Err(ErrorN::ActionMismatch);
        }
        if applied.envelope.digest != recorded.digest {
            return Err(ErrorN::DigestMismatch);
        }
        *slot = Some(applied.next);
        Ok(())
    }

    pub(crate) fn finalize(&self, expected: ChainN) -> Result<LiveInstance, ErrorN> {
        let mut slot = self.inner.try_lock().map_err(map_try_lock)?;
        let current = slot.as_ref().ok_or(ErrorN::RecoveryConsumed)?;
        if expected.version != VERSION {
            return Err(ErrorN::InvalidVersion);
        }
        if expected.sequence != current.sequence || expected.head != current.head {
            return Err(ErrorN::FinalAnchorMismatch);
        }
        let state = slot.take().ok_or(ErrorN::RecoveryConsumed)?;
        Ok(LiveInstance::from_state(self.background.clone(), state))
    }
}

struct Applied {
    next: InstanceState,
    envelope: EnvelopeN,
}

fn apply_without_commit(
    current: &InstanceState,
    background: &BackgroundTheory,
    command: CommandN,
) -> Result<Applied, ErrorN> {
    limits::preflight(&current.kernel, current.sequence, &command)?;
    let sequence = current
        .sequence
        .checked_add(1)
        .ok_or(ErrorN::SequenceExhausted)?;
    let (kernel, action) = command
        .clone()
        .apply(current.kernel.clone(), background)
        .map_err(ErrorN::kernel)?;
    let previous_digest = current.head;
    let digest = link(previous_digest, sequence, &command, &action);
    Ok(Applied {
        next: InstanceState {
            kernel,
            sequence,
            head: digest,
        },
        envelope: EnvelopeN {
            version: VERSION,
            sequence,
            previous_digest,
            digest,
            command,
            action,
        },
    })
}

fn map_try_lock<T>(error: TryLockError<T>) -> ErrorN {
    match error {
        TryLockError::WouldBlock => ErrorN::InstanceBusy,
        TryLockError::Poisoned(_) => ErrorN::ResourcePoisoned,
    }
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_new(background: BackgroundN) -> NativeResult<ResourceArc<LiveInstance>> {
    Ok(ResourceArc::new(LiveInstance::new(background)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_apply(
    instance: ResourceArc<LiveInstance>,
    command: CommandN,
) -> NativeResult<EnvelopeN> {
    instance.apply(command)
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_status(instance: ResourceArc<LiveInstance>) -> NativeResult<ChainN> {
    instance.status()
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_state(instance: ResourceArc<LiveInstance>) -> NativeResult<StateN> {
    instance.state()
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn recovery_new(background: BackgroundN) -> NativeResult<ResourceArc<RecoveryInstance>> {
    Ok(ResourceArc::new(RecoveryInstance::new(background)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn recovery_replay(
    recovery: ResourceArc<RecoveryInstance>,
    envelope: EnvelopeN,
) -> NativeResult<()> {
    recovery.replay(envelope)
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn recovery_finalize(
    recovery: ResourceArc<RecoveryInstance>,
    expected: ChainN,
) -> NativeResult<ResourceArc<LiveInstance>> {
    recovery.finalize(expected).map(ResourceArc::new)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::sync::Arc;
    use std::thread;

    use argus_kernel::{AgentId, ToolId};

    use crate::{
        ActionN, BackgroundN, ChainN, CommandN, DelegateCommandN, EgressKindN, EnvelopeN, ErrorN,
        KernelErrorN, ModeN, RegisterToolActionN, RegisterToolCommandN, StateN, VERSION, genesis,
        limits, link,
    };

    use super::LiveInstance;

    fn background() -> BackgroundN {
        BackgroundN {
            mode: ModeN::Enforce,
            allow_ceiling: HashMap::from(EgressKindN::ALL.map(|egress| (egress, None))),
            inspect_ceiling: HashMap::from(EgressKindN::ALL.map(|egress| (egress, None))),
        }
    }

    fn register_tool(tool: &str) -> CommandN {
        CommandN::RegisterTool(RegisterToolCommandN {
            tool: tool.to_owned(),
        })
    }

    fn triple(instance: &LiveInstance) -> super::InstanceState {
        instance.inner.try_lock().unwrap().clone()
    }

    fn recovery_triple(instance: &super::RecoveryInstance) -> Option<super::InstanceState> {
        instance.inner.try_lock().unwrap().clone()
    }

    fn assert_replay_failure(
        recovery: &super::RecoveryInstance,
        envelope: EnvelopeN,
        expected: ErrorN,
    ) {
        let before = recovery_triple(recovery);
        assert_eq!(
            (recovery.replay(envelope), recovery_triple(recovery)),
            (Err(expected), before)
        );
    }

    #[test]
    fn new_instance_has_fixed_root_and_genesis_status() {
        let semantic = background();
        let expected_head = genesis(&semantic);
        let instance = LiveInstance::new(semantic);

        assert_eq!(
            (instance.background.root_agent(), instance.status()),
            (
                &AgentId::root(),
                Ok(ChainN {
                    version: VERSION,
                    sequence: 0,
                    head: expected_head,
                }),
            )
        );
    }

    #[test]
    fn accepted_command_returns_complete_envelope_and_advances_once() {
        let semantic = background();
        let previous = genesis(&semantic);
        let instance = LiveInstance::new(semantic);
        let command = register_tool("tool");
        let action = ActionN::RegisterTool(RegisterToolActionN {
            tool: "tool".to_owned(),
        });
        let digest = link(previous, 1, &command, &action);

        assert_eq!(
            (instance.apply(command.clone()), instance.status()),
            (
                Ok(EnvelopeN {
                    version: VERSION,
                    sequence: 1,
                    previous_digest: previous,
                    digest,
                    command,
                    action,
                }),
                Ok(ChainN {
                    version: VERSION,
                    sequence: 1,
                    head: digest,
                }),
            )
        );
    }

    #[test]
    fn kernel_refusal_leaves_state_sequence_and_head_unchanged() {
        let instance = LiveInstance::new(background());
        assert!(instance.apply(register_tool("tool")).is_ok());
        let before = triple(&instance);

        assert_eq!(
            (instance.apply(register_tool("tool")), triple(&instance)),
            (
                Err(ErrorN::Kernel(KernelErrorN::ToolAlreadyRegistered)),
                before,
            )
        );
    }

    #[test]
    fn capacity_refusal_leaves_state_sequence_and_head_unchanged() {
        let instance = LiveInstance::new(background());
        let before = triple(&instance);

        assert_eq!(
            (
                instance.apply(register_tool(
                    &"x".repeat(limits::MAX_OPAQUE_UTF8_BYTES + 1)
                )),
                triple(&instance),
            ),
            (Err(ErrorN::CapacityExceeded), before)
        );
    }

    #[test]
    fn sequence_refusal_leaves_state_sequence_and_head_unchanged() {
        let instance = LiveInstance::new(background());
        instance.inner.try_lock().unwrap().sequence = limits::MAX_ACCEPTED_SEQUENCE;
        let before = triple(&instance);

        assert_eq!(
            (instance.apply(register_tool("tool")), triple(&instance)),
            (Err(ErrorN::SequenceExhausted), before)
        );
    }

    #[test]
    fn state_observation_is_read_only() {
        let instance = LiveInstance::new(background());
        let before = triple(&instance);

        assert_eq!(
            (instance.state(), triple(&instance)),
            (Ok(StateN::from_kernel(&before.kernel)), before)
        );
    }

    #[test]
    fn state_observation_rejects_capacity_excess_without_mutation() {
        let instance = LiveInstance::new(background());
        instance
            .inner
            .try_lock()
            .unwrap()
            .kernel
            .tool_registered
            .insert(ToolId("x".repeat(limits::MAX_OPAQUE_UTF8_BYTES + 1)));
        let before = triple(&instance);

        assert_eq!(
            (instance.state(), triple(&instance)),
            (Err(ErrorN::CapacityExceeded), before)
        );
    }

    #[test]
    fn contention_returns_busy_without_waiting() {
        let instance = LiveInstance::new(background());
        let _held = instance.inner.try_lock().unwrap();

        assert_eq!(
            (
                instance.apply(register_tool("tool")),
                instance.status(),
                instance.state(),
            ),
            (
                Err(ErrorN::InstanceBusy),
                Err(ErrorN::InstanceBusy),
                Err(ErrorN::InstanceBusy),
            )
        );
    }

    #[test]
    fn poisoned_resource_returns_typed_error() {
        let instance = Arc::new(LiveInstance::new(background()));
        let poisoner = Arc::clone(&instance);
        assert!(
            thread::spawn(move || {
                let _held = poisoner.inner.lock().unwrap();
                panic!("poison resource for test");
            })
            .join()
            .is_err()
        );

        assert_eq!(
            (
                instance.apply(register_tool("tool")),
                instance.status(),
                instance.state(),
            ),
            (
                Err(ErrorN::ResourcePoisoned),
                Err(ErrorN::ResourcePoisoned),
                Err(ErrorN::ResourcePoisoned),
            )
        );
    }

    #[test]
    fn empty_genesis_finalizes_into_a_live_instance() {
        let semantic = background();
        let expected = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = super::RecoveryInstance::new(semantic);

        assert_eq!(
            recovery
                .finalize(expected.clone())
                .and_then(|live| live.status()),
            Ok(expected)
        );
    }

    #[test]
    fn live_and_recovery_are_distinct_rustler_resource_types() {
        fn assert_resource<T: rustler::Resource>() {}

        assert_resource::<LiveInstance>();
        assert_resource::<super::RecoveryInstance>();
        assert_ne!(
            std::any::TypeId::of::<LiveInstance>(),
            std::any::TypeId::of::<super::RecoveryInstance>()
        );
    }

    #[test]
    fn successful_multi_link_replay_can_continue_live() {
        let live = LiveInstance::new(background());
        let first = live.apply(register_tool("tool")).unwrap();
        let second = live
            .apply(CommandN::Delegate(DelegateCommandN {
                grantor: "root".to_owned(),
                grantee: "agent".to_owned(),
            }))
            .unwrap();
        let expected = live.status().unwrap();
        let recovery = super::RecoveryInstance::new(background());

        assert_eq!(recovery.replay(first), Ok(()));
        assert_eq!(recovery.replay(second), Ok(()));
        let recovered = recovery.finalize(expected).unwrap();

        assert_eq!(
            recovered.apply(register_tool("next")),
            live.apply(register_tool("next"))
        );
        assert_eq!(triple(&recovered), triple(&live));
    }

    #[test]
    fn wrong_background_rejects_first_predecessor_without_mutation() {
        let live = LiveInstance::new(background());
        let envelope = live.apply(register_tool("tool")).unwrap();
        let mut different = background();
        different.mode = ModeN::Monitor;
        let recovery = super::RecoveryInstance::new(different);

        assert_replay_failure(&recovery, envelope, ErrorN::PreviousDigestMismatch);
    }

    #[test]
    fn wrong_envelope_version_does_not_commit() {
        let live = LiveInstance::new(background());
        let mut envelope = live.apply(register_tool("tool")).unwrap();
        envelope.version = VERSION + 1;
        let recovery = super::RecoveryInstance::new(background());

        assert_replay_failure(&recovery, envelope, ErrorN::InvalidVersion);
    }

    #[test]
    fn sequence_gap_does_not_commit() {
        let live = LiveInstance::new(background());
        let mut envelope = live.apply(register_tool("tool")).unwrap();
        envelope.sequence += 1;
        let recovery = super::RecoveryInstance::new(background());

        assert_replay_failure(&recovery, envelope, ErrorN::SequenceMismatch);
    }

    #[test]
    fn wrong_predecessor_does_not_commit() {
        let live = LiveInstance::new(background());
        let mut envelope = live.apply(register_tool("tool")).unwrap();
        envelope.previous_digest = crate::DigestN::new([7; 32]);
        let recovery = super::RecoveryInstance::new(background());

        assert_replay_failure(&recovery, envelope, ErrorN::PreviousDigestMismatch);
    }

    #[test]
    fn wrong_semantic_action_does_not_commit() {
        let live = LiveInstance::new(background());
        let mut envelope = live.apply(register_tool("tool")).unwrap();
        envelope.action = ActionN::RegisterTool(RegisterToolActionN {
            tool: "forged".to_owned(),
        });
        let recovery = super::RecoveryInstance::new(background());

        assert_replay_failure(&recovery, envelope, ErrorN::ActionMismatch);
    }

    #[test]
    fn wrong_digest_does_not_commit() {
        let live = LiveInstance::new(background());
        let mut envelope = live.apply(register_tool("tool")).unwrap();
        envelope.digest = crate::DigestN::new([9; 32]);
        let recovery = super::RecoveryInstance::new(background());

        assert_replay_failure(&recovery, envelope, ErrorN::DigestMismatch);
    }

    #[test]
    fn duplicate_link_is_rejected_by_prefix_sequence_without_mutation() {
        let live = LiveInstance::new(background());
        let envelope = live.apply(register_tool("tool")).unwrap();
        let recovery = super::RecoveryInstance::new(background());
        recovery.replay(envelope.clone()).unwrap();

        assert_replay_failure(&recovery, envelope, ErrorN::SequenceMismatch);
    }

    #[test]
    fn reordered_links_are_rejected_by_prefix_sequence_without_mutation() {
        let live = LiveInstance::new(background());
        let _first = live.apply(register_tool("first")).unwrap();
        let second = live.apply(register_tool("second")).unwrap();
        let recovery = super::RecoveryInstance::new(background());

        assert_replay_failure(&recovery, second, ErrorN::SequenceMismatch);
    }

    #[test]
    fn deleted_link_is_rejected_as_a_sequence_gap_without_mutation() {
        let live = LiveInstance::new(background());
        let first = live.apply(register_tool("first")).unwrap();
        let _second = live.apply(register_tool("second")).unwrap();
        let third = live.apply(register_tool("third")).unwrap();
        let recovery = super::RecoveryInstance::new(background());
        recovery.replay(first).unwrap();

        assert_replay_failure(&recovery, third, ErrorN::SequenceMismatch);
    }

    #[test]
    fn inserted_link_makes_the_recorded_prefix_fail_without_mutation() {
        let original = LiveInstance::new(background())
            .apply(register_tool("original"))
            .unwrap();
        let inserted = LiveInstance::new(background())
            .apply(register_tool("inserted"))
            .unwrap();
        let recovery = super::RecoveryInstance::new(background());
        recovery.replay(inserted).unwrap();

        assert_replay_failure(&recovery, original, ErrorN::SequenceMismatch);
    }

    #[test]
    fn replay_kernel_refusal_returns_closed_cause_without_mutation() {
        let first = LiveInstance::new(background())
            .apply(register_tool("tool"))
            .unwrap();
        let recovery = super::RecoveryInstance::new(background());
        recovery.replay(first).unwrap();
        let current = recovery_triple(&recovery).unwrap();
        let command = register_tool("tool");
        let action = ActionN::RegisterTool(RegisterToolActionN {
            tool: "tool".to_owned(),
        });
        let envelope = EnvelopeN {
            version: VERSION,
            sequence: current.sequence + 1,
            previous_digest: current.head,
            digest: link(current.head, current.sequence + 1, &command, &action),
            command,
            action,
        };

        assert_replay_failure(
            &recovery,
            envelope,
            ErrorN::ReplayRefused(KernelErrorN::ToolAlreadyRegistered),
        );
    }

    #[test]
    fn replay_state_capacity_refusal_does_not_commit() {
        let recovery = super::RecoveryInstance::new(background());
        recovery
            .inner
            .try_lock()
            .unwrap()
            .as_mut()
            .unwrap()
            .kernel
            .tool_registered
            .insert(ToolId("x".repeat(limits::MAX_OPAQUE_UTF8_BYTES + 1)));
        let envelope = LiveInstance::new(background())
            .apply(register_tool("tool"))
            .unwrap();

        assert_replay_failure(&recovery, envelope, ErrorN::CapacityExceeded);
    }

    #[test]
    fn replay_command_capacity_refusal_does_not_commit() {
        let recovery = super::RecoveryInstance::new(background());
        let current = recovery_triple(&recovery).unwrap();
        let command = register_tool(&"x".repeat(limits::MAX_OPAQUE_UTF8_BYTES + 1));
        let action = ActionN::RegisterTool(RegisterToolActionN {
            tool: "x".repeat(limits::MAX_OPAQUE_UTF8_BYTES + 1),
        });
        let envelope = EnvelopeN {
            version: VERSION,
            sequence: 1,
            previous_digest: current.head,
            digest: link(current.head, 1, &command, &action),
            command,
            action,
        };

        assert_replay_failure(&recovery, envelope, ErrorN::CapacityExceeded);
    }

    #[test]
    fn replay_sequence_limit_refusal_does_not_commit() {
        let recovery = super::RecoveryInstance::new(background());
        recovery
            .inner
            .try_lock()
            .unwrap()
            .as_mut()
            .unwrap()
            .sequence = limits::MAX_ACCEPTED_SEQUENCE;
        let envelope = LiveInstance::new(background())
            .apply(register_tool("tool"))
            .unwrap();

        assert_replay_failure(&recovery, envelope, ErrorN::SequenceExhausted);
    }

    #[test]
    fn final_version_mismatch_leaves_recovery_usable() {
        let semantic = background();
        let good = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = super::RecoveryInstance::new(semantic);
        let mut bad = good.clone();
        bad.version += 1;

        assert_eq!(recovery.finalize(bad).err(), Some(ErrorN::InvalidVersion));
        assert_eq!(
            recovery
                .finalize(good)
                .and_then(|live| live.status())
                .unwrap()
                .sequence,
            0
        );
    }

    #[test]
    fn final_sequence_mismatch_leaves_recovery_usable() {
        let semantic = background();
        let good = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = super::RecoveryInstance::new(semantic);
        let mut bad = good.clone();
        bad.sequence += 1;

        assert_eq!(
            recovery.finalize(bad).err(),
            Some(ErrorN::FinalAnchorMismatch)
        );
        assert_eq!(
            recovery
                .finalize(good)
                .and_then(|live| live.status())
                .unwrap()
                .sequence,
            0
        );
    }

    #[test]
    fn final_head_mismatch_leaves_recovery_usable() {
        let semantic = background();
        let good = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = super::RecoveryInstance::new(semantic);
        let mut bad = good.clone();
        bad.head = crate::DigestN::new([4; 32]);

        assert_eq!(
            recovery.finalize(bad).err(),
            Some(ErrorN::FinalAnchorMismatch)
        );
        assert_eq!(
            recovery
                .finalize(good)
                .and_then(|live| live.status())
                .unwrap()
                .sequence,
            0
        );
    }

    #[test]
    fn successful_finalization_consumes_recovery_exactly_once() {
        let semantic = background();
        let expected = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = super::RecoveryInstance::new(semantic);

        assert!(recovery.finalize(expected.clone()).is_ok());
        assert_eq!(
            recovery.finalize(expected).err(),
            Some(ErrorN::RecoveryConsumed)
        );
    }

    #[test]
    fn replay_after_finalization_returns_recovery_consumed() {
        let semantic = background();
        let expected = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = super::RecoveryInstance::new(semantic);
        recovery.finalize(expected).unwrap();
        let envelope = LiveInstance::new(background())
            .apply(register_tool("tool"))
            .unwrap();

        assert_replay_failure(&recovery, envelope, ErrorN::RecoveryConsumed);
    }

    #[test]
    fn recovery_operations_return_busy_without_waiting_or_mutating() {
        let semantic = background();
        let expected = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = super::RecoveryInstance::new(semantic);
        let envelope = LiveInstance::new(background())
            .apply(register_tool("tool"))
            .unwrap();
        let held = recovery.inner.try_lock().unwrap();
        let before = held.clone();

        assert_eq!(recovery.replay(envelope), Err(ErrorN::InstanceBusy));
        assert_eq!(
            recovery.finalize(expected).err(),
            Some(ErrorN::InstanceBusy)
        );
        assert_eq!(*held, before);
    }

    #[test]
    fn poisoned_recovery_operations_return_typed_error() {
        let semantic = background();
        let expected = ChainN {
            version: VERSION,
            sequence: 0,
            head: genesis(&semantic),
        };
        let recovery = Arc::new(super::RecoveryInstance::new(semantic));
        let poisoner = Arc::clone(&recovery);
        assert!(
            thread::spawn(move || {
                let _held = poisoner.inner.lock().unwrap();
                panic!("poison recovery resource for test");
            })
            .join()
            .is_err()
        );
        let envelope = LiveInstance::new(background())
            .apply(register_tool("tool"))
            .unwrap();

        assert_eq!(recovery.replay(envelope), Err(ErrorN::ResourcePoisoned));
        assert_eq!(
            recovery.finalize(expected).err(),
            Some(ErrorN::ResourcePoisoned)
        );
    }
}
