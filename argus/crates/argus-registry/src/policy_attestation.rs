use std::collections::HashMap;
use std::path::Path;
use std::str::FromStr;
use std::sync::Mutex;

use rusqlite::{params, Connection};

use sha2::{Digest, Sha256};

use crate::trust_event::TrustEvent;

#[derive(Debug, Clone, PartialEq)]
pub enum PolicyEventType {
    Loaded,
    Reloaded,
    Rejected,
}

impl PolicyEventType {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Loaded => "loaded",
            Self::Reloaded => "reloaded",
            Self::Rejected => "rejected",
        }
    }
}

impl FromStr for PolicyEventType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "loaded" => Ok(Self::Loaded),
            "reloaded" => Ok(Self::Reloaded),
            "rejected" => Ok(Self::Rejected),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PolicyAttestation {
    pub id: String,
    pub timestamp: String,
    pub policy_file: String,
    pub content_hash: String,
    pub signature: Option<String>,
    pub key_id: Option<String>,
    pub actor: String,
    pub event_type: PolicyEventType,
}

const POLICY_ATTESTATION_SCHEMA: &str = r#"
CREATE TABLE IF NOT EXISTS policy_attestations (
    id              TEXT PRIMARY KEY,
    timestamp       TEXT NOT NULL,
    policy_file     TEXT NOT NULL,
    content_hash    TEXT NOT NULL,
    signature       TEXT,
    key_id          TEXT,
    actor           TEXT NOT NULL,
    event_type      TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_policy_attestations_file
    ON policy_attestations(policy_file, timestamp);
"#;

pub struct PolicyAttestationStore {
    conn: Mutex<Connection>,
}

impl PolicyAttestationStore {
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
        conn.execute_batch(POLICY_ATTESTATION_SCHEMA)?;
        Ok(Self {
            conn: Mutex::new(conn),
        })
    }

    pub fn record(&self, attestation: &PolicyAttestation) -> Result<(), rusqlite::Error> {
        let conn = self.conn.lock().unwrap();
        conn.execute(
            r#"
            INSERT INTO policy_attestations
                (id, timestamp, policy_file, content_hash, signature,
                 key_id, actor, event_type)
            VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)
            "#,
            params![
                attestation.id,
                attestation.timestamp,
                attestation.policy_file,
                attestation.content_hash,
                attestation.signature,
                attestation.key_id,
                attestation.actor,
                attestation.event_type.as_str(),
            ],
        )?;
        Ok(())
    }

    pub fn latest_hashes(&self) -> Result<HashMap<String, String>, rusqlite::Error> {
        let conn = self.conn.lock().unwrap();
        let mut stmt = conn.prepare(
            r#"
            SELECT pa.policy_file, pa.content_hash
            FROM policy_attestations pa
            INNER JOIN (
                SELECT policy_file, MAX(rowid) as max_rowid
                FROM policy_attestations
                WHERE event_type != 'rejected'
                GROUP BY policy_file
            ) latest ON pa.policy_file = latest.policy_file AND pa.rowid = latest.max_rowid
            "#,
        )?;
        let rows = stmt.query_map([], |row| {
            let file: String = row.get(0)?;
            let hash: String = row.get(1)?;
            Ok((file, hash))
        })?;
        let mut map = HashMap::new();
        for row in rows {
            let (file, hash) = row?;
            map.insert(file, hash);
        }
        Ok(map)
    }

    pub fn history_for_file(
        &self,
        policy_file: &str,
    ) -> Result<Vec<PolicyAttestation>, rusqlite::Error> {
        let conn = self.conn.lock().unwrap();
        let mut stmt = conn.prepare(
            "SELECT * FROM policy_attestations WHERE policy_file = ?1 ORDER BY timestamp ASC",
        )?;
        let rows = stmt.query_map(params![policy_file], Self::row_to_attestation)?;
        rows.collect()
    }

    fn row_to_attestation(row: &rusqlite::Row) -> Result<PolicyAttestation, rusqlite::Error> {
        let event_type_str: String = row.get("event_type")?;
        Ok(PolicyAttestation {
            id: row.get("id")?,
            timestamp: row.get("timestamp")?,
            policy_file: row.get("policy_file")?,
            content_hash: row.get("content_hash")?,
            signature: row.get("signature")?,
            key_id: row.get("key_id")?,
            actor: row.get("actor")?,
            event_type: PolicyEventType::from_str(&event_type_str)
                .unwrap_or(PolicyEventType::Rejected),
        })
    }
}

pub fn compute_content_hash(content: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(content.as_bytes());
    format!("sha256:{}", hex::encode(hasher.finalize()))
}

impl PolicyAttestation {
    pub fn new_loaded(policy_file: &str, content_hash: &str, actor: &str) -> Self {
        Self {
            id: TrustEvent::new_id(),
            timestamp: TrustEvent::now_rfc3339(),
            policy_file: policy_file.to_string(),
            content_hash: content_hash.to_string(),
            signature: None,
            key_id: None,
            actor: actor.to_string(),
            event_type: PolicyEventType::Loaded,
        }
    }

    pub fn new_reloaded(policy_file: &str, content_hash: &str, actor: &str) -> Self {
        Self {
            id: TrustEvent::new_id(),
            timestamp: TrustEvent::now_rfc3339(),
            policy_file: policy_file.to_string(),
            content_hash: content_hash.to_string(),
            signature: None,
            key_id: None,
            actor: actor.to_string(),
            event_type: PolicyEventType::Reloaded,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn record_and_query_attestation() {
        let store = PolicyAttestationStore::in_memory().unwrap();
        let att = PolicyAttestation::new_loaded("default.cedar", "sha256:abc", "daemon");
        store.record(&att).unwrap();

        let history = store.history_for_file("default.cedar").unwrap();
        assert_eq!(history.len(), 1);
        assert_eq!(history[0].policy_file, "default.cedar");
        assert_eq!(history[0].content_hash, "sha256:abc");
        assert_eq!(history[0].event_type, PolicyEventType::Loaded);
    }

    #[test]
    fn latest_hashes_returns_most_recent() {
        let store = PolicyAttestationStore::in_memory().unwrap();

        store
            .record(&PolicyAttestation::new_loaded(
                "a.cedar",
                "sha256:v1",
                "daemon",
            ))
            .unwrap();
        store
            .record(&PolicyAttestation::new_reloaded(
                "a.cedar",
                "sha256:v2",
                "daemon",
            ))
            .unwrap();
        store
            .record(&PolicyAttestation::new_loaded(
                "b.cedar",
                "sha256:bbb",
                "daemon",
            ))
            .unwrap();

        let hashes = store.latest_hashes().unwrap();
        assert_eq!(hashes.len(), 2);
        assert_eq!(hashes["a.cedar"], "sha256:v2");
        assert_eq!(hashes["b.cedar"], "sha256:bbb");
    }

    #[test]
    fn history_for_file_chronological() {
        let store = PolicyAttestationStore::in_memory().unwrap();

        let mut a1 = PolicyAttestation::new_loaded("a.cedar", "sha256:v1", "daemon");
        a1.timestamp = "2026-01-01T00:00:00Z".to_string();
        store.record(&a1).unwrap();

        let mut a2 = PolicyAttestation::new_reloaded("a.cedar", "sha256:v2", "daemon");
        a2.timestamp = "2026-01-02T00:00:00Z".to_string();
        store.record(&a2).unwrap();

        let history = store.history_for_file("a.cedar").unwrap();
        assert_eq!(history.len(), 2);
        assert_eq!(history[0].event_type, PolicyEventType::Loaded);
        assert_eq!(history[1].event_type, PolicyEventType::Reloaded);
    }

    #[test]
    fn event_type_roundtrip() {
        for event_type in [
            PolicyEventType::Loaded,
            PolicyEventType::Reloaded,
            PolicyEventType::Rejected,
        ] {
            let s = event_type.as_str();
            let parsed = PolicyEventType::from_str(s).unwrap();
            assert_eq!(parsed, event_type);
        }
    }
}
