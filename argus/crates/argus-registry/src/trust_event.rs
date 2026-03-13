use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::Mutex;

use rusqlite::{Connection, params};
use uuid::Uuid;

use crate::binding::{BindingTable, ToolBinding};

#[derive(Debug, Clone, PartialEq)]
pub enum TrustEventType {
    Trusted,
    Updated,
    Revoked,
    Quarantined,
    Restored,
}

impl TrustEventType {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Trusted => "trusted",
            Self::Updated => "updated",
            Self::Revoked => "revoked",
            Self::Quarantined => "quarantined",
            Self::Restored => "restored",
        }
    }
}

impl FromStr for TrustEventType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "trusted" => Ok(Self::Trusted),
            "updated" => Ok(Self::Updated),
            "revoked" => Ok(Self::Revoked),
            "quarantined" => Ok(Self::Quarantined),
            "restored" => Ok(Self::Restored),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TrustEvent {
    pub id: String,
    pub timestamp: String,
    pub actor: String,
    pub tool_name: String,
    pub event_type: TrustEventType,
    pub derivation_hash: Option<String>,
    pub capabilities: Option<HashSet<String>>,
    pub source_path: Option<PathBuf>,
    pub mcp_name: Option<String>,
    pub analysis_summary: Option<String>,
    pub rationale: Option<String>,
}

impl TrustEvent {
    pub fn new_id() -> String {
        Uuid::now_v7().to_string()
    }

    pub fn now_rfc3339() -> String {
        chrono::Utc::now().to_rfc3339()
    }
}

const TRUST_EVENTS_SCHEMA: &str = r#"
CREATE TABLE IF NOT EXISTS trust_events (
    id              TEXT PRIMARY KEY,
    timestamp       TEXT NOT NULL,
    actor           TEXT NOT NULL,
    tool_name       TEXT NOT NULL,
    event_type      TEXT NOT NULL,
    derivation_hash TEXT,
    capabilities    TEXT,
    source_path     TEXT,
    mcp_name        TEXT,
    analysis_summary TEXT,
    rationale       TEXT
);

CREATE INDEX IF NOT EXISTS idx_trust_events_tool
    ON trust_events(tool_name, timestamp);
CREATE INDEX IF NOT EXISTS idx_trust_events_type
    ON trust_events(event_type, timestamp);

CREATE TABLE IF NOT EXISTS tool_bindings (
    name            TEXT PRIMARY KEY,
    derivation_hash TEXT NOT NULL,
    capabilities    TEXT NOT NULL,
    source_path     TEXT NOT NULL,
    mcp_name        TEXT
);
"#;

pub struct TrustEventStore {
    conn: Mutex<Connection>,
}

impl TrustEventStore {
    pub fn new(db_path: &Path) -> Result<Self, rusqlite::Error> {
        if let Some(parent) = db_path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        let conn = Connection::open(db_path)?;
        Self::from_connection(conn)
    }

    pub fn in_memory() -> Result<Self, rusqlite::Error> {
        let conn = Connection::open_in_memory()?;
        Self::from_connection(conn)
    }

    fn from_connection(conn: Connection) -> Result<Self, rusqlite::Error> {
        conn.execute_batch("PRAGMA journal_mode=WAL; PRAGMA busy_timeout=5000;")?;
        conn.execute_batch(TRUST_EVENTS_SCHEMA)?;
        Ok(Self {
            conn: Mutex::new(conn),
        })
    }

    pub fn write_event(&self, event: &TrustEvent) -> Result<(), rusqlite::Error> {
        let conn = self.conn.lock().unwrap();
        let capabilities_json = event
            .capabilities
            .as_ref()
            .map(|c| serde_json::to_string(c).expect("HashSet<String> always serializes"));
        let source_path_str = event.source_path.as_ref().map(|p| p.display().to_string());

        conn.execute(
            r#"
            INSERT INTO trust_events
                (id, timestamp, actor, tool_name, event_type,
                 derivation_hash, capabilities,
                 source_path, mcp_name, analysis_summary, rationale)
            VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)
            "#,
            params![
                event.id,
                event.timestamp,
                event.actor,
                event.tool_name,
                event.event_type.as_str(),
                event.derivation_hash,
                capabilities_json,
                source_path_str,
                event.mcp_name,
                event.analysis_summary,
                event.rationale,
            ],
        )?;
        Ok(())
    }

    pub fn events_for_tool(&self, tool_name: &str) -> Result<Vec<TrustEvent>, rusqlite::Error> {
        let conn = self.conn.lock().unwrap();
        let mut stmt =
            conn.prepare("SELECT * FROM trust_events WHERE tool_name = ?1 ORDER BY timestamp ASC")?;
        let rows = stmt.query_map(params![tool_name], Self::row_to_event)?;
        rows.collect()
    }

    pub fn recent_events(&self, limit: usize) -> Result<Vec<TrustEvent>, rusqlite::Error> {
        let conn = self.conn.lock().unwrap();
        let mut stmt =
            conn.prepare("SELECT * FROM trust_events ORDER BY timestamp DESC LIMIT ?1")?;
        let rows = stmt.query_map(params![limit as i64], Self::row_to_event)?;
        rows.collect()
    }

    pub fn rebuild_bindings(&self) -> Result<BindingTable, rusqlite::Error> {
        let mut conn = self.conn.lock().unwrap();
        let tx = conn.transaction()?;

        tx.execute("DELETE FROM tool_bindings", [])?;

        tx.execute_batch(
            r#"
            INSERT OR REPLACE INTO tool_bindings
                (name, derivation_hash, capabilities, source_path, mcp_name)
            SELECT e.tool_name, e.derivation_hash, e.capabilities,
                   e.source_path, e.mcp_name
            FROM trust_events e
            INNER JOIN (
                SELECT tool_name, MAX(rowid) as max_rowid
                FROM trust_events
                GROUP BY tool_name
            ) latest ON e.tool_name = latest.tool_name AND e.rowid = latest.max_rowid
            WHERE e.event_type != 'revoked'
            AND e.derivation_hash IS NOT NULL;
            "#,
        )?;

        let mut table = BindingTable::new();
        {
            let mut stmt = tx.prepare(
                "SELECT name, derivation_hash, capabilities, source_path, mcp_name
                 FROM tool_bindings",
            )?;
            let rows = stmt.query_map([], |row| {
                let name: String = row.get("name")?;
                let derivation_hash: String = row.get("derivation_hash")?;
                let capabilities_json: String = row.get("capabilities")?;
                let source_path_str: String = row.get("source_path")?;
                let mcp_name: Option<String> = row.get("mcp_name")?;

                let capabilities: HashSet<String> =
                    serde_json::from_str(&capabilities_json).unwrap_or_default();

                Ok(ToolBinding {
                    name,
                    derivation_hash,
                    capabilities,
                    source_path: PathBuf::from(source_path_str),
                    mcp_name,
                })
            })?;
            for binding in rows {
                table.register(binding?);
            }
        }

        tx.commit()?;
        Ok(table)
    }

    fn row_to_event(row: &rusqlite::Row) -> Result<TrustEvent, rusqlite::Error> {
        let event_type_str: String = row.get("event_type")?;
        let capabilities_json: Option<String> = row.get("capabilities")?;
        let source_path_str: Option<String> = row.get("source_path")?;

        Ok(TrustEvent {
            id: row.get("id")?,
            timestamp: row.get("timestamp")?,
            actor: row.get("actor")?,
            tool_name: row.get("tool_name")?,
            event_type: TrustEventType::from_str(&event_type_str)
                .unwrap_or(TrustEventType::Quarantined),
            derivation_hash: row.get("derivation_hash")?,
            capabilities: capabilities_json.map(|j| serde_json::from_str(&j).unwrap_or_default()),
            source_path: source_path_str.map(PathBuf::from),
            mcp_name: row.get("mcp_name")?,
            analysis_summary: row.get("analysis_summary")?,
            rationale: row.get("rationale")?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_trusted_event(tool_name: &str) -> TrustEvent {
        TrustEvent {
            id: TrustEvent::new_id(),
            timestamp: TrustEvent::now_rfc3339(),
            actor: "local".to_string(),
            tool_name: tool_name.to_string(),
            event_type: TrustEventType::Trusted,
            derivation_hash: Some(format!("sha256:{tool_name}")),
            capabilities: Some(["filesystem:read".to_string()].into_iter().collect()),
            source_path: Some(PathBuf::from(format!("/store/{tool_name}"))),
            mcp_name: None,
            analysis_summary: None,
            rationale: Some("initial trust".to_string()),
        }
    }

    #[test]
    fn write_and_read_trust_event() {
        let store = TrustEventStore::in_memory().unwrap();
        let event = sample_trusted_event("read_file");
        store.write_event(&event).unwrap();

        let events = store.events_for_tool("read_file").unwrap();
        assert_eq!(events.len(), 1);
        assert_eq!(events[0].tool_name, "read_file");
        assert_eq!(events[0].event_type, TrustEventType::Trusted);
        assert_eq!(events[0].actor, "local");
        assert_eq!(
            events[0].derivation_hash.as_deref(),
            Some("sha256:read_file")
        );
        assert_eq!(events[0].rationale.as_deref(), Some("initial trust"));
    }

    #[test]
    fn events_for_tool_returns_chronological_order() {
        let store = TrustEventStore::in_memory().unwrap();

        let mut e1 = sample_trusted_event("tool_a");
        e1.timestamp = "2026-01-01T00:00:00Z".to_string();
        store.write_event(&e1).unwrap();

        let mut e2 = sample_trusted_event("tool_a");
        e2.event_type = TrustEventType::Updated;
        e2.timestamp = "2026-01-02T00:00:00Z".to_string();
        e2.derivation_hash = Some("sha256:updated".to_string());
        store.write_event(&e2).unwrap();

        let events = store.events_for_tool("tool_a").unwrap();
        assert_eq!(events.len(), 2);
        assert_eq!(events[0].event_type, TrustEventType::Trusted);
        assert_eq!(events[1].event_type, TrustEventType::Updated);
    }

    #[test]
    fn rebuild_bindings_from_trusted_event() {
        let store = TrustEventStore::in_memory().unwrap();
        store
            .write_event(&sample_trusted_event("read_file"))
            .unwrap();

        let table = store.rebuild_bindings().unwrap();
        assert_eq!(table.len(), 1);
        let binding = table.lookup("read_file").unwrap();
        assert_eq!(binding.derivation_hash, "sha256:read_file");
        assert!(binding.capabilities.contains("filesystem:read"));
    }

    #[test]
    fn rebuild_bindings_excludes_revoked() {
        let store = TrustEventStore::in_memory().unwrap();
        store.write_event(&sample_trusted_event("tool_a")).unwrap();

        let revoke = TrustEvent {
            id: TrustEvent::new_id(),
            timestamp: TrustEvent::now_rfc3339(),
            actor: "local".to_string(),
            tool_name: "tool_a".to_string(),
            event_type: TrustEventType::Revoked,
            derivation_hash: None,
            capabilities: None,
            source_path: None,
            mcp_name: None,
            analysis_summary: None,
            rationale: Some("no longer needed".to_string()),
        };
        store.write_event(&revoke).unwrap();

        let table = store.rebuild_bindings().unwrap();
        assert!(table.is_empty());
    }

    #[test]
    fn rebuild_bindings_uses_latest_event() {
        let store = TrustEventStore::in_memory().unwrap();
        store.write_event(&sample_trusted_event("tool_a")).unwrap();

        let mut updated = sample_trusted_event("tool_a");
        updated.event_type = TrustEventType::Updated;
        updated.derivation_hash = Some("sha256:v2".to_string());
        store.write_event(&updated).unwrap();

        let table = store.rebuild_bindings().unwrap();
        assert_eq!(table.len(), 1);
        let binding = table.lookup("tool_a").unwrap();
        assert_eq!(binding.derivation_hash, "sha256:v2");
    }

    #[test]
    fn recent_events_respects_limit() {
        let store = TrustEventStore::in_memory().unwrap();
        for i in 0..5 {
            let mut event = sample_trusted_event(&format!("tool_{i}"));
            event.timestamp = format!("2026-01-0{i}T00:00:00Z");
            store.write_event(&event).unwrap();
        }

        let events = store.recent_events(3).unwrap();
        assert_eq!(events.len(), 3);
    }

    #[test]
    fn rebuild_bindings_multiple_tools() {
        let store = TrustEventStore::in_memory().unwrap();
        store.write_event(&sample_trusted_event("tool_a")).unwrap();
        store.write_event(&sample_trusted_event("tool_b")).unwrap();

        let table = store.rebuild_bindings().unwrap();
        assert_eq!(table.len(), 2);
        assert!(table.lookup("tool_a").is_some());
        assert!(table.lookup("tool_b").is_some());
    }

    #[test]
    fn event_type_roundtrip() {
        for event_type in [
            TrustEventType::Trusted,
            TrustEventType::Updated,
            TrustEventType::Revoked,
            TrustEventType::Quarantined,
            TrustEventType::Restored,
        ] {
            let s = event_type.as_str();
            let parsed = TrustEventType::from_str(s).unwrap();
            assert_eq!(parsed, event_type);
        }
    }

    #[test]
    fn rebuild_after_revoke_then_retrust() {
        let store = TrustEventStore::in_memory().unwrap();
        store.write_event(&sample_trusted_event("tool_a")).unwrap();

        let revoke = TrustEvent {
            id: TrustEvent::new_id(),
            timestamp: TrustEvent::now_rfc3339(),
            actor: "local".to_string(),
            tool_name: "tool_a".to_string(),
            event_type: TrustEventType::Revoked,
            derivation_hash: None,
            capabilities: None,
            source_path: None,
            mcp_name: None,
            analysis_summary: None,
            rationale: None,
        };
        store.write_event(&revoke).unwrap();

        let table = store.rebuild_bindings().unwrap();
        assert!(table.is_empty());

        let mut retrust = sample_trusted_event("tool_a");
        retrust.event_type = TrustEventType::Trusted;
        retrust.derivation_hash = Some("sha256:v3".to_string());
        store.write_event(&retrust).unwrap();

        let table = store.rebuild_bindings().unwrap();
        assert_eq!(table.len(), 1);
        assert_eq!(table.lookup("tool_a").unwrap().derivation_hash, "sha256:v3");
    }
}
