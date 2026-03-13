use argus_kernel::ConfLevel;

#[derive(Clone, Debug)]
pub struct TaintSignal {
    pub suspicion: f64,
    pub taint_level: Option<ConfLevel>,
    pub markers: Vec<String>,
}

impl TaintSignal {
    pub fn from_suspicion(suspicion: f64, markers: Vec<String>) -> Self {
        let taint_level = if suspicion < 0.3 {
            None
        } else if suspicion < 0.6 {
            Some(ConfLevel::Internal)
        } else if suspicion < 0.8 {
            Some(ConfLevel::Sensitive)
        } else {
            Some(ConfLevel::Restricted)
        };
        Self {
            suspicion,
            taint_level,
            markers,
        }
    }
}

pub trait DivergenceClassifier: Send + Sync {
    fn classify(&self, reasoning_trace: &str) -> TaintSignal;
}

pub struct MockClassifier {
    fixed_score: f64,
}

impl MockClassifier {
    pub fn new(fixed_score: f64) -> Self {
        Self { fixed_score }
    }
}

impl DivergenceClassifier for MockClassifier {
    fn classify(&self, _reasoning_trace: &str) -> TaintSignal {
        TaintSignal::from_suspicion(self.fixed_score, vec!["mock".to_owned()])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_signal_no_taint() {
        let signal = TaintSignal::from_suspicion(0.1, vec![]);
        assert!(signal.taint_level.is_none());
    }

    #[test]
    fn moderate_suspicion_internal_taint() {
        let signal = TaintSignal::from_suspicion(0.4, vec![]);
        assert_eq!(signal.taint_level, Some(ConfLevel::Internal));
    }

    #[test]
    fn high_suspicion_sensitive_taint() {
        let signal = TaintSignal::from_suspicion(0.7, vec![]);
        assert_eq!(signal.taint_level, Some(ConfLevel::Sensitive));
    }

    #[test]
    fn extreme_suspicion_restricted_taint() {
        let signal = TaintSignal::from_suspicion(0.9, vec![]);
        assert_eq!(signal.taint_level, Some(ConfLevel::Restricted));
    }

    #[test]
    fn mock_classifier_returns_fixed_score() {
        let classifier = MockClassifier::new(0.5);
        let signal = classifier.classify("any trace");
        assert!((signal.suspicion - 0.5).abs() < f64::EPSILON);
        assert_eq!(signal.taint_level, Some(ConfLevel::Internal));
    }
}
