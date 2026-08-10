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

pub struct LiveInstance {
    background: BackgroundTheory,
    inner: Mutex<InstanceState>,
}

#[rustler::resource_impl]
impl Resource for LiveInstance {}

impl LiveInstance {
    fn new(background: BackgroundN) -> Self {
        let head = genesis(&background);
        Self {
            background: background.into_kernel(),
            inner: Mutex::new(InstanceState {
                kernel: KernelState::initial(),
                sequence: 0,
                head,
            }),
        }
    }

    fn status(&self) -> Result<ChainN, ErrorN> {
        let current = self.inner.try_lock().map_err(map_try_lock)?;
        Ok(ChainN {
            version: VERSION,
            sequence: current.sequence,
            head: current.head,
        })
    }

    fn state(&self) -> Result<StateN, ErrorN> {
        let current = self.inner.try_lock().map_err(map_try_lock)?;
        limits::check_state(&current.kernel)?;
        Ok(StateN::from_kernel(&current.kernel))
    }

    fn apply(&self, command: CommandN) -> Result<EnvelopeN, ErrorN> {
        let mut current = self.inner.try_lock().map_err(map_try_lock)?;
        limits::preflight(&current.kernel, current.sequence, &command)?;
        let sequence = current
            .sequence
            .checked_add(1)
            .ok_or(ErrorN::SequenceExhausted)?;
        let (kernel, action) = command
            .clone()
            .apply(current.kernel.clone(), &self.background)
            .map_err(ErrorN::kernel)?;
        let previous_digest = current.head;
        let digest = link(previous_digest, sequence, &command, &action);
        let envelope = EnvelopeN {
            version: VERSION,
            sequence,
            previous_digest,
            digest,
            command,
            action,
        };
        *current = InstanceState {
            kernel,
            sequence,
            head: digest,
        };
        Ok(envelope)
    }
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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::sync::Arc;
    use std::thread;

    use argus_kernel::{AgentId, ToolId};

    use crate::{
        ActionN, BackgroundN, ChainN, CommandN, EgressKindN, EnvelopeN, ErrorN, KernelErrorN,
        ModeN, RegisterToolActionN, RegisterToolCommandN, StateN, VERSION, genesis, limits, link,
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
}
