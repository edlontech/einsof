use std::collections::BTreeSet;
use std::time::{Duration, Instant};

use crate::breaker::{BreakerState, CircuitBreaker, Evidence};
use crate::classifier::TaintSignal;

#[derive(Clone, Debug)]
pub struct UserIntent {
    pub goal: String,
    pub expected_tools: BTreeSet<String>,
    pub expected_scope: Vec<String>,
}

pub struct SessionAnalyzer {
    intent: Option<UserIntent>,
    breaker: CircuitBreaker,
    taint_escalations: Vec<TaintSignal>,
}

impl SessionAnalyzer {
    pub fn new(breaker_threshold: usize, breaker_window: Duration) -> Self {
        Self {
            intent: None,
            breaker: CircuitBreaker::new(breaker_threshold, breaker_window),
            taint_escalations: Vec::new(),
        }
    }

    pub fn update_intent(&mut self, intent: UserIntent) {
        self.intent = Some(intent);
    }

    pub fn intent(&self) -> Option<&UserIntent> {
        self.intent.as_ref()
    }

    pub fn record_taint_signal(&mut self, signal: TaintSignal) {
        let evidence = Evidence {
            tier: if signal.suspicion >= 0.8 { 1 } else { 2 },
            signal: signal.suspicion,
            confidence: signal.suspicion,
            timestamp: Instant::now(),
        };
        self.breaker.record_escalation(evidence);
        self.taint_escalations.push(signal);
    }

    pub fn breaker_state(&self) -> &BreakerState {
        self.breaker.state()
    }

    pub fn is_breaker_open(&self) -> bool {
        self.breaker.is_open()
    }

    pub fn acknowledge_breaker(&mut self) {
        self.breaker.acknowledge();
    }

    pub fn taint_escalations(&self) -> &[TaintSignal] {
        &self.taint_escalations
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn session_tracks_intent() {
        let mut session = SessionAnalyzer::new(3, Duration::from_secs(60));
        assert!(session.intent().is_none());

        let intent = UserIntent {
            goal: "refactor module".to_owned(),
            expected_tools: BTreeSet::from(["read_file".to_owned(), "write_file".to_owned()]),
            expected_scope: vec!["src/".to_owned()],
        };
        session.update_intent(intent);
        assert_eq!(session.intent().unwrap().goal, "refactor module");
    }

    #[test]
    fn session_feeds_breaker() {
        let mut session = SessionAnalyzer::new(2, Duration::from_secs(60));
        let signal = TaintSignal::from_suspicion(0.7, vec!["suspicious".to_owned()]);
        session.record_taint_signal(signal);
        assert!(!session.is_breaker_open());

        let signal = TaintSignal::from_suspicion(0.8, vec!["very_suspicious".to_owned()]);
        session.record_taint_signal(signal);
        assert!(session.is_breaker_open());
    }

    #[test]
    fn session_acknowledge_breaker() {
        let mut session = SessionAnalyzer::new(1, Duration::from_secs(60));
        let signal = TaintSignal::from_suspicion(0.9, vec!["alert".to_owned()]);
        session.record_taint_signal(signal);
        assert!(session.is_breaker_open());

        session.acknowledge_breaker();
        assert!(session.breaker_state().is_half_open());
    }
}
