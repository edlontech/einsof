use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use argus_sandbox::SandboxProfile;

const SYSTEM_BASELINE_VARS: &[&str] = &[
    "PATH", "HOME", "TMPDIR", "USER", "LANG", "LC_ALL", "LC_CTYPE", "LC_MESSAGES", "LC_COLLATE",
    "LC_MONETARY", "LC_NUMERIC", "LC_TIME", "TERM",
];

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();

    let (profile_path, cmd_args) = match parse_args(&args) {
        Ok(parsed) => parsed,
        Err(e) => {
            eprintln!("argus-sandbox-exec: {e}");
            return ExitCode::from(2);
        }
    };

    let profile = match read_and_delete_profile(&profile_path) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("argus-sandbox-exec: failed to read profile: {e}");
            return ExitCode::from(2);
        }
    };

    if let Err(e) = enforce_and_exec(&profile, &cmd_args) {
        eprintln!("argus-sandbox-exec: {e}");
        return ExitCode::from(1);
    }

    unreachable!("exec should have replaced this process")
}

fn parse_args(args: &[String]) -> Result<(PathBuf, Vec<String>), String> {
    let mut profile_path = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--profile" => {
                i += 1;
                profile_path = Some(PathBuf::from(
                    args.get(i).ok_or("--profile requires a path argument")?,
                ));
            }
            "--" => {
                i += 1;
                break;
            }
            other => return Err(format!("unknown argument: {other}")),
        }
        i += 1;
    }

    let profile = profile_path.ok_or("--profile is required")?;
    let cmd_args: Vec<String> = args[i..].to_vec();
    if cmd_args.is_empty() {
        return Err("no command specified after --".into());
    }
    Ok((profile, cmd_args))
}

fn read_and_delete_profile(path: &Path) -> Result<SandboxProfile, String> {
    let contents = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    std::fs::remove_file(path).ok();
    serde_json::from_str(&contents).map_err(|e| e.to_string())
}

fn enforce_and_exec(profile: &SandboxProfile, cmd_args: &[String]) -> Result<(), String> {
    scrub_and_inject_env(profile);

    #[cfg(target_os = "macos")]
    {
        seatbelt::enforce(profile)?;
    }

    #[cfg(target_os = "linux")]
    {
        linux::enforce(profile, cmd_args)?;
    }

    exec_command(cmd_args)
}

fn scrub_and_inject_env(profile: &SandboxProfile) {
    let baseline: HashMap<String, String> = SYSTEM_BASELINE_VARS
        .iter()
        .filter_map(|&var| std::env::var(var).ok().map(|v| (var.to_string(), v)))
        .collect();

    // SAFETY: argus-sandbox-exec is single-threaded (runs before execvp replaces the process).
    // No other threads exist to observe env mutations.
    unsafe {
        for (key, _) in std::env::vars() {
            std::env::remove_var(&key);
        }

        for (key, val) in &baseline {
            std::env::set_var(key, val);
        }

        if let Some(original_path) = baseline.get("PATH") {
            let restricted = restrict_path(original_path);
            std::env::set_var("PATH", restricted);
        }

        for (key, val) in &profile.resolved_env {
            std::env::set_var(key, val);
        }
    }
}

fn restrict_path(original: &str) -> String {
    let allowed_prefixes = ["/usr/bin", "/usr/local/bin", "/bin", "/usr/sbin"];
    original
        .split(':')
        .filter(|entry| allowed_prefixes.iter().any(|prefix| entry.starts_with(prefix)))
        .collect::<Vec<_>>()
        .join(":")
}

fn exec_command(cmd_args: &[String]) -> Result<(), String> {
    use std::ffi::CString;

    let program = CString::new(cmd_args[0].as_bytes()).map_err(|e| e.to_string())?;
    let c_args: Vec<CString> = cmd_args
        .iter()
        .map(|a| CString::new(a.as_bytes()).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;

    let c_arg_ptrs: Vec<*const libc::c_char> = c_args
        .iter()
        .map(|a| a.as_ptr())
        .chain(std::iter::once(std::ptr::null()))
        .collect();

    unsafe {
        libc::execvp(program.as_ptr(), c_arg_ptrs.as_ptr());
    }

    Err(format!(
        "execvp failed: {}",
        std::io::Error::last_os_error()
    ))
}

#[cfg(target_os = "macos")]
mod seatbelt;

#[cfg(target_os = "linux")]
mod linux;

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    #[test]
    fn system_baseline_vars_are_defined() {
        assert!(SYSTEM_BASELINE_VARS.contains(&"PATH"));
        assert!(SYSTEM_BASELINE_VARS.contains(&"HOME"));
        assert!(SYSTEM_BASELINE_VARS.contains(&"TMPDIR"));
        assert!(!SYSTEM_BASELINE_VARS.contains(&"ANTHROPIC_API_KEY"));
    }

    #[test]
    #[serial]
    fn scrub_env_removes_all_non_baseline() {
        let original: Vec<(String, String)> = std::env::vars().collect();

        // SAFETY: test is serialized via #[serial], no concurrent threads
        unsafe { std::env::set_var("TEST_LEAK_VAR", "should_not_survive") };

        let mut resolved = HashMap::new();
        resolved.insert("MY_VAR".to_string(), "my_value".to_string());

        let profile = SandboxProfile {
            resolved_env: resolved,
            ..Default::default()
        };

        scrub_and_inject_env(&profile);

        assert!(
            std::env::var("TEST_LEAK_VAR").is_err(),
            "leaked env var survived scrub"
        );
        assert_eq!(std::env::var("MY_VAR").unwrap(), "my_value");

        // Restore
        unsafe {
            for (key, _) in std::env::vars() {
                std::env::remove_var(&key);
            }
            for (k, v) in &original {
                std::env::set_var(k, v);
            }
        }
    }

    #[test]
    fn restrict_path_filters_non_standard() {
        let input = "/usr/bin:/usr/local/bin:/home/user/.cargo/bin:/bin:/opt/sketchy";
        let result = restrict_path(input);
        assert!(result.contains("/usr/bin"));
        assert!(result.contains("/usr/local/bin"));
        assert!(result.contains("/bin"));
        assert!(!result.contains(".cargo"));
        assert!(!result.contains("sketchy"));
    }
}
