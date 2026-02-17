use argus_sandbox::{NetPolicy, SandboxProfile};
use landlock::{
    Access, AccessFs, AccessNet, PathBeneath, PathFd, Ruleset, RulesetAttr, RulesetCreatedAttr,
    ABI,
};

mod proxy;

pub fn enforce(profile: &SandboxProfile, cmd_args: &[String]) -> Result<(), String> {
    match &profile.net_policy {
        NetPolicy::EgressWithDomains(domains) if !domains.is_empty() => {
            enforce_with_proxy(profile, cmd_args, domains)
        }
        _ => enforce_landlock_only(profile),
    }
}

fn enforce_landlock_only(profile: &SandboxProfile) -> Result<(), String> {
    let abi = ABI::V5;

    let mut ruleset = Ruleset::default()
        .handle_access(AccessFs::from_all(abi))
        .map_err(|e| format!("landlock fs setup: {e}"))?;

    ruleset = match &profile.net_policy {
        NetPolicy::Blocked => ruleset
            .handle_access(AccessNet::from_all(abi))
            .map_err(|e| format!("landlock net setup: {e}"))?,
        NetPolicy::EgressOnly => ruleset
            .handle_access(AccessNet::BindTcp)
            .map_err(|e| format!("landlock net setup: {e}"))?,
        NetPolicy::EgressWithDomains(_) => unreachable!(),
    };

    let mut created = ruleset
        .create()
        .map_err(|e| format!("landlock create: {e}"))?;

    let read_access = AccessFs::Execute | AccessFs::ReadFile | AccessFs::ReadDir;
    for path in &profile.allowed_read_paths {
        if let Ok(fd) = PathFd::new(path) {
            created = created
                .add_rule(PathBeneath::new(fd, read_access))
                .map_err(|e| format!("landlock read rule for {}: {e}", path.display()))?;
        }
    }

    let write_access = read_access
        | AccessFs::WriteFile
        | AccessFs::MakeDir
        | AccessFs::MakeReg
        | AccessFs::MakeSym
        | AccessFs::Refer
        | AccessFs::Truncate
        | AccessFs::RemoveFile
        | AccessFs::RemoveDir;
    for path in &profile.allowed_write_paths {
        if let Ok(fd) = PathFd::new(path) {
            created = created
                .add_rule(PathBeneath::new(fd, write_access))
                .map_err(|e| format!("landlock write rule for {}: {e}", path.display()))?;
        }
    }

    let status = created
        .restrict_self()
        .map_err(|e| format!("landlock restrict_self: {e}"))?;

    match status.ruleset {
        landlock::RulesetStatus::FullyEnforced => {}
        landlock::RulesetStatus::PartiallyEnforced => {
            return Err("landlock only partially enforced (kernel too old?)".into());
        }
        landlock::RulesetStatus::NotEnforced => {
            return Err("landlock not enforced (kernel does not support landlock)".into());
        }
    }

    let ret = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
    if ret != 0 {
        return Err(format!(
            "prctl(PR_SET_NO_NEW_PRIVS) failed: {}",
            std::io::Error::last_os_error()
        ));
    }

    Ok(())
}

fn enforce_with_proxy(
    profile: &SandboxProfile,
    cmd_args: &[String],
    domains: &[String],
) -> Result<(), String> {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("tokio runtime: {e}"))?;

    rt.block_on(async {
        let mut proxy_server = proxy::ProxyServer::new(domains.to_vec());
        proxy_server.start().await?;

        let http_sock = proxy_server.http_socket_path().display().to_string();
        let proxy_url = format!("http://unix:{http_sock}:");

        let mut bwrap_args = vec![
            "bwrap".to_string(),
            "--clearenv".to_string(),
            "--unshare-net".to_string(),
            "--bind".to_string(),
            "/".to_string(),
            "/".to_string(),
            "--ro-bind".to_string(),
            http_sock.clone(),
            http_sock,
        ];

        for var in ["HTTP_PROXY", "HTTPS_PROXY", "http_proxy", "https_proxy"] {
            bwrap_args.push("--setenv".to_string());
            bwrap_args.push(var.to_string());
            bwrap_args.push(proxy_url.clone());
        }

        for (key, value) in &profile.resolved_env {
            bwrap_args.push("--setenv".to_string());
            bwrap_args.push(key.clone());
            bwrap_args.push(value.clone());
        }

        bwrap_args.push("--".to_string());
        bwrap_args.extend_from_slice(cmd_args);

        let status = tokio::process::Command::new(&bwrap_args[0])
            .args(&bwrap_args[1..])
            .status()
            .await
            .map_err(|e| format!("failed to spawn bwrap: {e}"))?;

        proxy_server.shutdown();

        if status.success() {
            Ok(())
        } else {
            Err(format!(
                "sandboxed process exited with status: {}",
                status.code().unwrap_or(-1)
            ))
        }
    })
}
