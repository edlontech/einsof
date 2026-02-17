use argus_sandbox::{NetPolicy, SandboxProfile};

pub fn enforce(profile: &SandboxProfile) -> Result<(), String> {
    let sbpl = generate_sbpl(profile);
    apply_sandbox(&sbpl)
}

fn generate_sbpl(profile: &SandboxProfile) -> String {
    let mut rules: Vec<String> = [
        "(version 1)",
        "(deny default)",
        "(allow process-exec)",
        "(allow process-fork)",
        "(allow sysctl-read)",
        "(allow mach-lookup)",
        "(allow signal (target self))",
        "(allow system-socket)",
        "(allow file-read-metadata)",
        "(allow file-read-data (literal \"/\"))",
    ]
    .iter()
    .map(|s| (*s).into())
    .collect();

    for path in &profile.allowed_read_paths {
        let p = path.display();
        if path.extension().is_some() && !path.is_dir() {
            rules.push(format!("(allow file-read* (literal \"{p}\"))"));
        } else {
            rules.push(format!("(allow file-read* (subpath \"{p}\"))"));
        }
    }

    for path in &profile.allowed_write_paths {
        let p = path.display();
        rules.push(format!("(allow file-write* (subpath \"{p}\"))"));
        rules.push(format!("(allow file-read* (subpath \"{p}\"))"));
    }

    const ALLOW_DNS: &str = "(allow network* (local udp \"*:53\"))";
    const DENY_INBOUND: &str = "(deny network-inbound)";

    match &profile.net_policy {
        NetPolicy::Blocked => {}
        NetPolicy::EgressOnly => {
            rules.push("(allow network-outbound)".into());
            rules.push(ALLOW_DNS.into());
            rules.push(DENY_INBOUND.into());
        }
        NetPolicy::EgressWithDomains(domains) => {
            if !domains.is_empty() {
                let combined: String = domains
                    .iter()
                    .map(|d| domain_to_seatbelt_regex(d))
                    .collect::<Vec<_>>()
                    .join(" ");
                rules.push(format!(
                    "(allow network-outbound (remote tcp (require-any {combined})))"
                ));
                rules.push(ALLOW_DNS.into());
            }
            rules.push(DENY_INBOUND.into());
        }
    }

    rules.join("\n")
}

fn domain_to_seatbelt_regex(domain: &str) -> String {
    if let Some(suffix) = domain.strip_prefix("*.") {
        let escaped = regex_escape(suffix);
        format!("(regex #\"^.+\\.{escaped}$\")")
    } else {
        let escaped = regex_escape(domain);
        format!("(regex #\"^{escaped}$\")")
    }
}

fn regex_escape(s: &str) -> String {
    s.replace('.', "\\.")
}

fn apply_sandbox(sbpl: &str) -> Result<(), String> {
    use std::ffi::CString;
    use std::ptr;

    let profile_cstr = CString::new(sbpl).map_err(|e| format!("invalid SBPL: {e}"))?;
    let mut errorbuf: *mut libc::c_char = ptr::null_mut();

    let result = unsafe {
        sandbox_init(profile_cstr.as_ptr(), 0, &mut errorbuf)
    };

    if result != 0 {
        let err = if !errorbuf.is_null() {
            let msg = unsafe { std::ffi::CStr::from_ptr(errorbuf) }
                .to_string_lossy()
                .into_owned();
            unsafe { sandbox_free_error(errorbuf) };
            msg
        } else {
            "unknown sandbox_init error".into()
        };
        return Err(format!("sandbox_init failed: {err}"));
    }

    Ok(())
}

unsafe extern "C" {
    fn sandbox_init(
        profile: *const libc::c_char,
        flags: u64,
        errorbuf: *mut *mut libc::c_char,
    ) -> libc::c_int;
    fn sandbox_free_error(errorbuf: *mut libc::c_char);
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn sbpl_starts_with_deny_default() {
        let profile = SandboxProfile::default();
        let sbpl = generate_sbpl(&profile);
        assert!(sbpl.contains("(deny default)"));
    }

    #[test]
    fn sbpl_includes_read_paths() {
        let profile = SandboxProfile {
            allowed_read_paths: vec![PathBuf::from("/usr/lib"), PathBuf::from("/tmp/data")],
            ..Default::default()
        };
        let sbpl = generate_sbpl(&profile);
        assert!(sbpl.contains("(allow file-read* (subpath \"/usr/lib\"))"));
        assert!(sbpl.contains("(allow file-read* (subpath \"/tmp/data\"))"));
    }

    #[test]
    fn sbpl_includes_write_paths_with_read() {
        let profile = SandboxProfile {
            allowed_write_paths: vec![PathBuf::from("/tmp/output")],
            ..Default::default()
        };
        let sbpl = generate_sbpl(&profile);
        assert!(sbpl.contains("(allow file-write* (subpath \"/tmp/output\"))"));
        assert!(sbpl.contains("(allow file-read* (subpath \"/tmp/output\"))"));
    }

    #[test]
    fn sbpl_blocked_network_has_no_allow() {
        let profile = SandboxProfile {
            net_policy: NetPolicy::Blocked,
            ..Default::default()
        };
        let sbpl = generate_sbpl(&profile);
        assert!(!sbpl.contains("network-outbound"));
    }

    #[test]
    fn sbpl_egress_only_allows_outbound() {
        let profile = SandboxProfile {
            net_policy: NetPolicy::EgressOnly,
            ..Default::default()
        };
        let sbpl = generate_sbpl(&profile);
        assert!(sbpl.contains("(allow network-outbound)"));
        assert!(sbpl.contains("(deny network-inbound)"));
    }

    #[test]
    fn sbpl_egress_with_domains_uses_regex() {
        let profile = SandboxProfile {
            net_policy: NetPolicy::EgressWithDomains(vec![
                "api.github.com".into(),
                "*.openai.com".into(),
            ]),
            ..Default::default()
        };
        let sbpl = generate_sbpl(&profile);
        assert!(sbpl.contains("(regex #\"^api\\.github\\.com$\")"));
        assert!(sbpl.contains("(regex #\"^.+\\.openai\\.com$\")"));
    }

    #[test]
    fn domain_to_regex_exact() {
        let r = domain_to_seatbelt_regex("api.github.com");
        assert_eq!(r, "(regex #\"^api\\.github\\.com$\")");
    }

    #[test]
    fn domain_to_regex_wildcard() {
        let r = domain_to_seatbelt_regex("*.openai.com");
        assert_eq!(r, "(regex #\"^.+\\.openai\\.com$\")");
    }
}
