use std::collections::VecDeque;
use std::time::{Duration, Instant};

pub struct RestartTracker {
    timestamps: VecDeque<Instant>,
    max_restarts: u32,
    window: Duration,
}

impl RestartTracker {
    pub fn new(max_restarts: u32, window: Duration) -> Self {
        Self {
            timestamps: VecDeque::new(),
            max_restarts,
            window,
        }
    }

    pub fn default_policy() -> Self {
        Self::new(3, Duration::from_secs(60))
    }

    pub fn can_restart(&mut self) -> bool {
        self.expire_old();
        self.timestamps.len() < self.max_restarts as usize
    }

    pub fn try_restart(&mut self) -> bool {
        self.expire_old();
        if self.timestamps.len() < self.max_restarts as usize {
            self.timestamps.push_back(Instant::now());
            true
        } else {
            false
        }
    }

    pub fn record_restart(&mut self) {
        self.expire_old();
        self.timestamps.push_back(Instant::now());
    }

    fn expire_old(&mut self) {
        let cutoff = Instant::now() - self.window;
        while self.timestamps.front().is_some_and(|t| *t < cutoff) {
            self.timestamps.pop_front();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_tracker_allows_restart() {
        let mut tracker = RestartTracker::default_policy();
        assert!(tracker.can_restart());
    }

    #[test]
    fn exhausted_tracker_denies_restart() {
        let mut tracker = RestartTracker::new(2, Duration::from_secs(60));
        tracker.record_restart();
        tracker.record_restart();
        assert!(!tracker.can_restart());
    }

    #[test]
    fn restarts_within_budget_allowed() {
        let mut tracker = RestartTracker::new(3, Duration::from_secs(60));
        tracker.record_restart();
        tracker.record_restart();
        assert!(tracker.can_restart());
    }

    #[test]
    fn expired_restarts_free_budget() {
        let mut tracker = RestartTracker::new(1, Duration::from_millis(10));
        tracker.record_restart();
        assert!(!tracker.can_restart());
        std::thread::sleep(Duration::from_millis(20));
        assert!(tracker.can_restart());
    }

    #[test]
    fn zero_max_always_denies() {
        let mut tracker = RestartTracker::new(0, Duration::from_secs(60));
        assert!(!tracker.can_restart());
    }

    #[test]
    fn try_restart_atomically_checks_and_records() {
        let mut tracker = RestartTracker::new(2, Duration::from_secs(60));
        assert!(tracker.try_restart());
        assert!(tracker.try_restart());
        assert!(!tracker.try_restart());
    }
}
