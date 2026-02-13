pub fn domain_matches(pattern: &str, hostname: &str) -> bool {
    if let Some(suffix) = pattern.strip_prefix("*.") {
        let suffix_dot = format!(".{suffix}");
        hostname.ends_with(&suffix_dot) && hostname.len() > suffix_dot.len()
    } else {
        pattern == hostname
    }
}

pub fn domain_matches_any(patterns: &[String], hostname: &str) -> bool {
    patterns.iter().any(|p| domain_matches(p, hostname))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_match() {
        assert!(domain_matches("api.github.com", "api.github.com"));
    }

    #[test]
    fn exact_no_match() {
        assert!(!domain_matches("api.github.com", "evil.github.com"));
    }

    #[test]
    fn wildcard_matches_subdomain() {
        assert!(domain_matches("*.github.com", "api.github.com"));
    }

    #[test]
    fn wildcard_matches_deep_subdomain() {
        assert!(domain_matches("*.github.com", "raw.api.github.com"));
    }

    #[test]
    fn wildcard_does_not_match_bare_domain() {
        assert!(!domain_matches("*.github.com", "github.com"));
    }

    #[test]
    fn wildcard_does_not_match_unrelated() {
        assert!(!domain_matches("*.github.com", "api.gitlab.com"));
    }

    #[test]
    fn case_sensitive() {
        assert!(!domain_matches("api.github.com", "API.GITHUB.COM"));
    }

    #[test]
    fn matches_any_with_list() {
        let patterns = vec!["api.github.com".into(), "*.openai.com".into()];
        assert!(domain_matches_any(&patterns, "api.github.com"));
        assert!(domain_matches_any(&patterns, "chat.openai.com"));
        assert!(!domain_matches_any(&patterns, "evil.com"));
    }

    #[test]
    fn empty_patterns_matches_nothing() {
        assert!(!domain_matches_any(&[], "anything.com"));
    }
}
