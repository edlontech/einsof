use std::path::Path;
use std::sync::Arc;

use crate::policy_attestation::PolicyAttestationStore;
use crate::trust_event::TrustEventStore;

pub struct ArgusDb {
    trust_events: Arc<TrustEventStore>,
    policy_attestations: Arc<PolicyAttestationStore>,
}

impl ArgusDb {
    pub fn new(db_path: &Path) -> Result<Self, rusqlite::Error> {
        let trust_events = Arc::new(TrustEventStore::new(db_path)?);
        let policy_attestations = Arc::new(PolicyAttestationStore::new(db_path)?);
        Ok(Self {
            trust_events,
            policy_attestations,
        })
    }

    pub fn trust_events(&self) -> &Arc<TrustEventStore> {
        &self.trust_events
    }

    pub fn policy_attestations(&self) -> &Arc<PolicyAttestationStore> {
        &self.policy_attestations
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn argus_db_creates_both_stores() {
        let temp = tempfile::TempDir::new().unwrap();
        let db = ArgusDb::new(&temp.path().join("argus.db")).unwrap();

        let trust = db.trust_events();
        assert!(trust.recent_events(10).unwrap().is_empty());

        let policy = db.policy_attestations();
        assert!(policy.latest_hashes().unwrap().is_empty());
    }
}
