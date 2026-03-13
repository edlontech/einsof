use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use notify::{Config, Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use thiserror::Error;
use tokio::sync::mpsc;

use crate::hash::compute_hash;
use crate::trust_event::{TrustEvent, TrustEventStore, TrustEventType};
use crate::{QuarantineManager, QuarantineReason};
use argus_config::OperationalMode;

#[derive(Debug, Clone)]
pub enum WatchEvent {
    ItemAdded {
        path: PathBuf,
        authorized: bool,
    },
    ItemRemoved {
        path: PathBuf,
    },
    ItemModified {
        path: PathBuf,
    },
    Quarantined {
        name: String,
        reason: QuarantineReason,
    },
}

#[derive(Error, Debug)]
pub enum WatcherError {
    #[error("Failed to create watcher: {0}")]
    CreateWatcher(#[from] notify::Error),
    #[error("Channel send error")]
    ChannelSend,
    #[error("Quarantine error: {0}")]
    Quarantine(#[from] crate::QuarantineError),
}

pub struct FolderWatcher {
    mode: Arc<RwLock<OperationalMode>>,
    quarantine_manager: Arc<QuarantineManager>,
    event_tx: mpsc::Sender<WatchEvent>,
    authorized_paths: Arc<RwLock<HashSet<PathBuf>>>,
    binding_table: Option<Arc<RwLock<crate::BindingTable>>>,
    trust_event_store: Option<Arc<TrustEventStore>>,
}

impl FolderWatcher {
    pub fn new(
        mode: Arc<RwLock<OperationalMode>>,
        quarantine_manager: Arc<QuarantineManager>,
        event_tx: mpsc::Sender<WatchEvent>,
    ) -> Self {
        Self {
            mode,
            quarantine_manager,
            event_tx,
            authorized_paths: Arc::new(RwLock::new(HashSet::new())),
            binding_table: None,
            trust_event_store: None,
        }
    }

    pub fn mark_authorized(&self, path: PathBuf) {
        let mut authorized = self
            .authorized_paths
            .write()
            .unwrap_or_else(|e| e.into_inner());
        authorized.insert(path);
    }

    pub fn is_authorized(&self, path: &Path) -> bool {
        let authorized = self
            .authorized_paths
            .read()
            .unwrap_or_else(|e| e.into_inner());
        authorized.contains(path)
    }

    pub fn with_binding_table(mut self, bt: Arc<RwLock<crate::BindingTable>>) -> Self {
        self.binding_table = Some(bt);
        self
    }

    pub fn with_trust_event_store(mut self, store: Arc<TrustEventStore>) -> Self {
        self.trust_event_store = Some(store);
        self
    }

    pub fn clear_authorized(&self, path: &Path) {
        let mut authorized = self
            .authorized_paths
            .write()
            .unwrap_or_else(|e| e.into_inner());
        authorized.remove(path);
    }

    pub async fn handle_fs_event(&self, event: Event) -> Result<(), WatcherError> {
        match event.kind {
            EventKind::Create(_) => {
                for path in event.paths {
                    if path.is_dir() {
                        self.handle_item_added(path).await?;
                    }
                }
            }
            EventKind::Remove(_) => {
                for path in event.paths {
                    let _ = self.event_tx.send(WatchEvent::ItemRemoved { path }).await;
                }
            }
            EventKind::Modify(_) => {
                for path in event.paths {
                    self.handle_modified(path).await?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    async fn handle_item_added(&self, path: PathBuf) -> Result<(), WatcherError> {
        if self.is_authorized(&path) {
            self.clear_authorized(&path);
            let _ = self
                .event_tx
                .send(WatchEvent::ItemAdded {
                    path,
                    authorized: true,
                })
                .await;
            return Ok(());
        }

        let mode = self.mode.read().unwrap_or_else(|e| e.into_inner()).clone();
        match mode {
            OperationalMode::Development => {
                tracing::warn!(
                    path = %path.display(),
                    "Unauthorized item added in development mode - allowing with warning"
                );
                let _ = self
                    .event_tx
                    .send(WatchEvent::ItemAdded {
                        path,
                        authorized: false,
                    })
                    .await;
            }
            OperationalMode::Production { .. } => {
                tracing::warn!(
                    path = %path.display(),
                    "Unauthorized item added in production mode - quarantining"
                );
                let item = self
                    .quarantine_manager
                    .quarantine(&path, QuarantineReason::UnauthorizedAddition)?;
                self.record_quarantine_event(
                    &item.name,
                    None,
                    "unauthorized addition detected by file watcher",
                );
                let _ = self
                    .event_tx
                    .send(WatchEvent::Quarantined {
                        name: item.name,
                        reason: QuarantineReason::UnauthorizedAddition,
                    })
                    .await;
            }
        }
        Ok(())
    }

    async fn handle_modified(&self, path: PathBuf) -> Result<(), WatcherError> {
        let Some(bt) = &self.binding_table else {
            let _ = self.event_tx.send(WatchEvent::ItemModified { path }).await;
            return Ok(());
        };

        let binding_info = {
            let table = bt.read().unwrap_or_else(|e| e.into_inner());
            table
                .iter()
                .find(|b| path.starts_with(&b.source_path))
                .map(|b| {
                    (
                        b.name.clone(),
                        b.derivation_hash.clone(),
                        b.source_path.clone(),
                    )
                })
        };

        let Some((name, expected_hash, source_path)) = binding_info else {
            let _ = self.event_tx.send(WatchEvent::ItemModified { path }).await;
            return Ok(());
        };

        let current_hash = match compute_hash(&source_path) {
            Ok(h) => h,
            Err(_) => {
                tracing::error!(tool = %name, "Failed to recompute hash for modified tool");
                return Ok(());
            }
        };

        if current_hash == expected_hash {
            let _ = self.event_tx.send(WatchEvent::ItemModified { path }).await;
            return Ok(());
        }

        let mode = self.mode.read().unwrap_or_else(|e| e.into_inner()).clone();
        match mode {
            OperationalMode::Development => {
                tracing::warn!(tool = %name, "Hash mismatch in development mode -- binding is stale");
                let _ = self.event_tx.send(WatchEvent::ItemModified { path }).await;
            }
            OperationalMode::Production { .. } => {
                tracing::warn!(tool = %name, "Hash mismatch in production mode -- quarantining");
                let reason = QuarantineReason::HashMismatch {
                    expected: expected_hash,
                    actual: current_hash.clone(),
                };
                if source_path.exists() {
                    let _ = self
                        .quarantine_manager
                        .quarantine(&source_path, reason.clone());
                }
                self.record_quarantine_event(
                    &name,
                    Some(current_hash),
                    "hash mismatch detected by file watcher",
                );
                bt.write().unwrap_or_else(|e| e.into_inner()).remove(&name);
                let _ = self
                    .event_tx
                    .send(WatchEvent::Quarantined { name, reason })
                    .await;
            }
        }
        Ok(())
    }

    fn record_quarantine_event(
        &self,
        tool_name: &str,
        derivation_hash: Option<String>,
        rationale: &str,
    ) {
        if let Some(store) = &self.trust_event_store {
            let event = TrustEvent {
                id: TrustEvent::new_id(),
                timestamp: TrustEvent::now_rfc3339(),
                actor: "watcher".to_string(),
                tool_name: tool_name.to_string(),
                event_type: TrustEventType::Quarantined,
                derivation_hash,
                capabilities: None,
                source_path: None,
                mcp_name: None,
                analysis_summary: None,
                rationale: Some(rationale.to_string()),
            };
            if let Err(e) = store.write_event(&event) {
                tracing::error!(error = %e, "Failed to record quarantine trust event");
            }
        }
    }

    pub fn start_watching(
        self: Arc<Self>,
        paths: Vec<PathBuf>,
    ) -> Result<RecommendedWatcher, WatcherError> {
        let watcher_self = self.clone();

        let mut watcher = RecommendedWatcher::new(
            move |res: Result<Event, notify::Error>| {
                if let Ok(event) = res {
                    let watcher_clone = watcher_self.clone();
                    tokio::spawn(async move {
                        if let Err(e) = watcher_clone.handle_fs_event(event).await {
                            tracing::error!(error = %e, "Failed to handle fs event");
                        }
                    });
                }
            },
            Config::default(),
        )?;

        for path in paths {
            if path.exists() {
                watcher.watch(&path, RecursiveMode::NonRecursive)?;
                tracing::info!(path = %path.display(), "Watching directory for changes");
            }
        }

        Ok(watcher)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_config::OperationalMode;

    #[test]
    fn watch_event_item_added_can_be_created() {
        let event = WatchEvent::ItemAdded {
            path: PathBuf::from("/test/mcp"),
            authorized: true,
        };
        match event {
            WatchEvent::ItemAdded { authorized, .. } => assert!(authorized),
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn watch_event_quarantined_contains_reason() {
        let event = WatchEvent::Quarantined {
            name: "bad-mcp".to_string(),
            reason: QuarantineReason::UnauthorizedAddition,
        };
        match event {
            WatchEvent::Quarantined { name, reason } => {
                assert_eq!(name, "bad-mcp");
                assert!(matches!(reason, QuarantineReason::UnauthorizedAddition));
            }
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn folder_watcher_tracks_authorized_paths() {
        let mode = Arc::new(RwLock::new(OperationalMode::Development));
        let temp = tempfile::TempDir::new().unwrap();
        let qm = Arc::new(QuarantineManager::new(temp.path()).unwrap());
        let (tx, _rx) = mpsc::channel(10);

        let watcher = FolderWatcher::new(mode, qm, tx);

        let path = PathBuf::from("/test/mcp");
        assert!(!watcher.is_authorized(&path));

        watcher.mark_authorized(path.clone());
        assert!(watcher.is_authorized(&path));

        watcher.clear_authorized(&path);
        assert!(!watcher.is_authorized(&path));
    }

    #[tokio::test]
    async fn handle_item_added_development_mode_allows() {
        let mode = Arc::new(RwLock::new(OperationalMode::Development));
        let temp = tempfile::TempDir::new().unwrap();
        let qm = Arc::new(QuarantineManager::new(&temp.path().join("quarantine")).unwrap());
        let (tx, mut rx) = mpsc::channel(10);

        let watcher = FolderWatcher::new(mode, qm, tx);

        let item_path = temp.path().join("mcps").join("new-mcp");
        std::fs::create_dir_all(&item_path).unwrap();

        watcher.handle_item_added(item_path.clone()).await.unwrap();

        let event = rx.try_recv().unwrap();
        match event {
            WatchEvent::ItemAdded { path, authorized } => {
                assert_eq!(path, item_path);
                assert!(!authorized);
            }
            _ => panic!("Expected ItemAdded event"),
        }
    }

    #[tokio::test]
    async fn modify_event_with_hash_mismatch_quarantines_in_production() {
        let mode = Arc::new(RwLock::new(OperationalMode::Production { strict: false }));
        let temp = tempfile::TempDir::new().unwrap();
        let qm = Arc::new(QuarantineManager::new(&temp.path().join("quarantine")).unwrap());
        let (tx, mut rx) = mpsc::channel(10);

        let tool_dir = temp.path().join("mcps").join("my-tool");
        std::fs::create_dir_all(&tool_dir).unwrap();
        std::fs::write(tool_dir.join("main.js"), "original").unwrap();

        let hash = compute_hash(&tool_dir).unwrap();

        let bt = Arc::new(RwLock::new(crate::BindingTable::new()));
        {
            let mut table = bt.write().unwrap();
            table.register(crate::ToolBinding {
                name: "my-tool".to_string(),
                derivation_hash: hash,
                capabilities: std::collections::HashSet::new(),
                source_path: tool_dir.clone(),
                mcp_name: None,
            });
        }

        let watcher = FolderWatcher::new(mode, qm, tx).with_binding_table(bt.clone());

        std::fs::write(tool_dir.join("main.js"), "tampered").unwrap();

        watcher
            .handle_modified(tool_dir.join("main.js"))
            .await
            .unwrap();

        let event = rx.try_recv().unwrap();
        match event {
            WatchEvent::Quarantined { name, reason } => {
                assert_eq!(name, "my-tool");
                assert!(matches!(reason, QuarantineReason::HashMismatch { .. }));
            }
            other => panic!("Expected Quarantined, got {:?}", other),
        }

        let table = bt.read().unwrap();
        assert!(table.lookup("my-tool").is_none());
    }

    #[tokio::test]
    async fn modify_event_with_matching_hash_sends_item_modified() {
        let mode = Arc::new(RwLock::new(OperationalMode::Production { strict: false }));
        let temp = tempfile::TempDir::new().unwrap();
        let qm = Arc::new(QuarantineManager::new(&temp.path().join("quarantine")).unwrap());
        let (tx, mut rx) = mpsc::channel(10);

        let tool_dir = temp.path().join("mcps").join("good-tool");
        std::fs::create_dir_all(&tool_dir).unwrap();
        std::fs::write(tool_dir.join("main.js"), "unchanged").unwrap();

        let hash = compute_hash(&tool_dir).unwrap();

        let bt = Arc::new(RwLock::new(crate::BindingTable::new()));
        {
            let mut table = bt.write().unwrap();
            table.register(crate::ToolBinding {
                name: "good-tool".to_string(),
                derivation_hash: hash,
                capabilities: std::collections::HashSet::new(),
                source_path: tool_dir.clone(),
                mcp_name: None,
            });
        }

        let watcher = FolderWatcher::new(mode, qm, tx).with_binding_table(bt.clone());

        watcher
            .handle_modified(tool_dir.join("main.js"))
            .await
            .unwrap();

        let event = rx.try_recv().unwrap();
        assert!(matches!(event, WatchEvent::ItemModified { .. }));

        let table = bt.read().unwrap();
        assert!(table.lookup("good-tool").is_some());
    }

    #[tokio::test]
    async fn modify_event_dev_mode_warns_but_does_not_quarantine() {
        let mode = Arc::new(RwLock::new(OperationalMode::Development));
        let temp = tempfile::TempDir::new().unwrap();
        let qm = Arc::new(QuarantineManager::new(&temp.path().join("quarantine")).unwrap());
        let (tx, mut rx) = mpsc::channel(10);

        let tool_dir = temp.path().join("mcps").join("dev-tool");
        std::fs::create_dir_all(&tool_dir).unwrap();
        std::fs::write(tool_dir.join("main.js"), "original").unwrap();

        let hash = compute_hash(&tool_dir).unwrap();

        let bt = Arc::new(RwLock::new(crate::BindingTable::new()));
        {
            let mut table = bt.write().unwrap();
            table.register(crate::ToolBinding {
                name: "dev-tool".to_string(),
                derivation_hash: hash,
                capabilities: std::collections::HashSet::new(),
                source_path: tool_dir.clone(),
                mcp_name: None,
            });
        }

        let watcher = FolderWatcher::new(mode, qm, tx).with_binding_table(bt.clone());

        std::fs::write(tool_dir.join("main.js"), "tampered").unwrap();

        watcher
            .handle_modified(tool_dir.join("main.js"))
            .await
            .unwrap();

        let event = rx.try_recv().unwrap();
        assert!(matches!(event, WatchEvent::ItemModified { .. }));

        let table = bt.read().unwrap();
        assert!(table.lookup("dev-tool").is_some());
    }

    #[tokio::test]
    async fn quarantine_writes_trust_event() {
        let mode = Arc::new(RwLock::new(OperationalMode::Production { strict: false }));
        let temp = tempfile::TempDir::new().unwrap();
        let qm = Arc::new(QuarantineManager::new(&temp.path().join("quarantine")).unwrap());
        let (tx, _rx) = mpsc::channel(10);

        let trust_store = Arc::new(TrustEventStore::in_memory().unwrap());
        let watcher = FolderWatcher::new(mode, qm, tx).with_trust_event_store(trust_store.clone());

        let item_path = temp.path().join("mcps").join("suspect-mcp");
        std::fs::create_dir_all(&item_path).unwrap();

        watcher.handle_item_added(item_path).await.unwrap();

        let events = trust_store.events_for_tool("suspect-mcp").unwrap();
        assert_eq!(events.len(), 1);
        assert_eq!(events[0].event_type, TrustEventType::Quarantined);
        assert_eq!(events[0].actor, "watcher");
        assert!(
            events[0]
                .rationale
                .as_deref()
                .unwrap()
                .contains("unauthorized")
        );
    }

    #[tokio::test]
    async fn handle_item_added_production_mode_quarantines() {
        let mode = Arc::new(RwLock::new(OperationalMode::Production { strict: false }));
        let temp = tempfile::TempDir::new().unwrap();
        let qm = Arc::new(QuarantineManager::new(&temp.path().join("quarantine")).unwrap());
        let (tx, mut rx) = mpsc::channel(10);

        let watcher = FolderWatcher::new(mode, qm.clone(), tx);

        let item_path = temp.path().join("mcps").join("bad-mcp");
        std::fs::create_dir_all(&item_path).unwrap();

        watcher.handle_item_added(item_path.clone()).await.unwrap();

        assert!(!item_path.exists());

        let event = rx.try_recv().unwrap();
        match event {
            WatchEvent::Quarantined { name, reason } => {
                assert_eq!(name, "bad-mcp");
                assert!(matches!(reason, QuarantineReason::UnauthorizedAddition));
            }
            _ => panic!("Expected Quarantined event"),
        }
    }
}
