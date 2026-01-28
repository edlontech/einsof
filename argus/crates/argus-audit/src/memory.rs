use std::sync::{Mutex, MutexGuard, PoisonError};

use argus_kernel::{EventStore, KernelError, KernelEvent};

fn lock_poisoned<T>(_: PoisonError<T>) -> KernelError {
    KernelError::EventStoreError("lock poisoned".into())
}

pub struct InMemoryEventStore {
    events: Mutex<Vec<KernelEvent>>,
}

impl Default for InMemoryEventStore {
    fn default() -> Self {
        Self::new()
    }
}

impl InMemoryEventStore {
    pub fn new() -> Self {
        Self {
            events: Mutex::new(Vec::new()),
        }
    }

    fn lock(&self) -> Result<MutexGuard<'_, Vec<KernelEvent>>, KernelError> {
        self.events.lock().map_err(lock_poisoned)
    }

    pub fn snapshot(&self) -> Result<Vec<KernelEvent>, KernelError> {
        Ok(self.lock()?.clone())
    }
}

impl EventStore for InMemoryEventStore {
    fn append(&self, event: &KernelEvent) -> Result<(), KernelError> {
        self.lock()?.push(event.clone());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use argus_kernel::{KernelAction, ToolId};

    fn make_event(seq: u64, tool_name: &str) -> KernelEvent {
        KernelEvent::new(
            seq,
            KernelAction::RegisterTool {
                tool: ToolId::new(tool_name),
            },
        )
    }

    #[test]
    fn append_and_snapshot() {
        let store = InMemoryEventStore::new();
        store.append(&make_event(1, "tool-a")).unwrap();
        let snap = store.snapshot().unwrap();
        assert_eq!(snap.len(), 1);
        assert_eq!(snap[0].sequence, 1);
    }

    #[test]
    fn preserves_ordering() {
        let store = InMemoryEventStore::new();
        store.append(&make_event(1, "first")).unwrap();
        store.append(&make_event(2, "second")).unwrap();
        store.append(&make_event(3, "third")).unwrap();
        let snap = store.snapshot().unwrap();
        assert_eq!(snap.len(), 3);
        assert_eq!(snap[0].sequence, 1);
        assert_eq!(snap[2].sequence, 3);
    }

    #[test]
    fn snapshot_is_a_clone() {
        let store = InMemoryEventStore::new();
        store.append(&make_event(1, "a")).unwrap();
        let snap = store.snapshot().unwrap();
        store.append(&make_event(2, "b")).unwrap();
        assert_eq!(snap.len(), 1);
        assert_eq!(store.snapshot().unwrap().len(), 2);
    }

    #[test]
    fn concurrent_appends() {
        use std::sync::Arc;
        use std::thread;

        let store = Arc::new(InMemoryEventStore::new());
        let mut handles = vec![];
        for i in 0..10 {
            let s = Arc::clone(&store);
            handles.push(thread::spawn(move || {
                s.append(&make_event(i, &format!("tool-{i}"))).unwrap();
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        assert_eq!(store.snapshot().unwrap().len(), 10);
    }
}
