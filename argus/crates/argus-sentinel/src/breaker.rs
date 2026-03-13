use std::collections::VecDeque;
use std::time::{Duration, Instant};

#[derive(Clone, Debug)]
pub struct Evidence {
    pub tier: u8,
    pub signal: f64,
    pub confidence: f64,
    pub timestamp: Instant,
}

#[derive(Clone, Debug)]
pub enum BreakerState {
    Closed,
    Open(Vec<Evidence>),
    HalfOpen,
}

impl BreakerState {
    pub fn is_open(&self) -> bool {
        matches!(self, Self::Open(_))
    }

    pub fn is_closed(&self) -> bool {
        matches!(self, Self::Closed)
    }

    pub fn is_half_open(&self) -> bool {
        matches!(self, Self::HalfOpen)
    }
}

pub struct CircuitBreaker {
    threshold: usize,
    window: Duration,
    events: VecDeque<Evidence>,
    state: BreakerState,
}

impl CircuitBreaker {
    pub fn new(threshold: usize, window: Duration) -> Self {
        Self {
            threshold,
            window,
            events: VecDeque::new(),
            state: BreakerState::Closed,
        }
    }

    pub fn record_escalation(&mut self, evidence: Evidence) {
        self.prune_expired();
        self.events.push_back(evidence);
        if self.events.len() >= self.threshold {
            let trail: Vec<Evidence> = self.events.iter().cloned().collect();
            self.state = BreakerState::Open(trail);
        }
    }

    pub fn state(&self) -> &BreakerState {
        &self.state
    }

    pub fn is_open(&self) -> bool {
        self.state.is_open()
    }

    pub fn acknowledge(&mut self) {
        if self.state.is_open() {
            self.state = BreakerState::HalfOpen;
        }
    }

    pub fn reset(&mut self) {
        self.state = BreakerState::Closed;
        self.events.clear();
    }

    fn prune_expired(&mut self) {
        let cutoff = Instant::now() - self.window;
        while let Some(front) = self.events.front() {
            if front.timestamp < cutoff {
                self.events.pop_front();
            } else {
                break;
            }
        }
    }

    pub fn evidence(&self) -> &VecDeque<Evidence> {
        &self.events
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_evidence(signal: f64) -> Evidence {
        Evidence {
            tier: 2,
            signal,
            confidence: 0.9,
            timestamp: Instant::now(),
        }
    }

    #[test]
    fn breaker_stays_closed_under_threshold() {
        let mut breaker = CircuitBreaker::new(3, Duration::from_secs(60));
        breaker.record_escalation(make_evidence(0.5));
        breaker.record_escalation(make_evidence(0.6));
        assert!(breaker.state().is_closed());
    }

    #[test]
    fn breaker_trips_at_threshold() {
        let mut breaker = CircuitBreaker::new(3, Duration::from_secs(60));
        breaker.record_escalation(make_evidence(0.5));
        breaker.record_escalation(make_evidence(0.6));
        breaker.record_escalation(make_evidence(0.7));
        assert!(breaker.is_open());
        if let BreakerState::Open(trail) = breaker.state() {
            assert_eq!(trail.len(), 3);
        } else {
            panic!("expected Open state with evidence");
        }
    }

    #[test]
    fn breaker_acknowledge_moves_to_half_open() {
        let mut breaker = CircuitBreaker::new(1, Duration::from_secs(60));
        breaker.record_escalation(make_evidence(0.9));
        assert!(breaker.is_open());
        breaker.acknowledge();
        assert!(breaker.state().is_half_open());
    }

    #[test]
    fn breaker_reset_clears() {
        let mut breaker = CircuitBreaker::new(1, Duration::from_secs(60));
        breaker.record_escalation(make_evidence(0.9));
        breaker.reset();
        assert!(breaker.state().is_closed());
        assert!(breaker.evidence().is_empty());
    }
}
