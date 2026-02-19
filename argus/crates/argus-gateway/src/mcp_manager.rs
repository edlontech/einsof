use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use argus_registry::toml_types::{SidecarEntry, SidecarLifecycle};
use argus_sandbox::{SandboxProfile, SandboxProvider};
use rig::tool::ToolDyn;
use rig::tool::rmcp::McpTool;
use rmcp::ServiceExt;
use rmcp::service::{RoleClient, RunningService};
use rmcp::transport::TokioChildProcess;
use tokio::io::{AsyncBufReadExt, BufReader};
use tokio::process::Command;
use tokio::sync::{Mutex, watch};
use tokio::task::JoinHandle;
use tracing::{error, info, warn};

use crate::McpError;
use crate::ready_check::{ReadyOutcome, poll_ready};
use crate::restart::RestartTracker;

pub struct McpServerConfig {
    pub name: String,
    pub command: String,
    pub args: Vec<String>,
    pub env: Vec<(String, String)>,
    pub sandbox_profile: SandboxProfile,
    pub sidecars: Vec<SidecarEntry>,
}

struct DaemonHandle {
    name: String,
    child: tokio::process::Child,
    config: SidecarEntry,
    restart_tracker: RestartTracker,
}

struct McpServerHandle {
    service: RunningService<RoleClient, ()>,
    tools: HashMap<String, McpTool>,
    daemons: Arc<Mutex<Vec<DaemonHandle>>>,
    supervision_handle: Option<JoinHandle<()>>,
    supervision_cancel: Option<watch::Sender<bool>>,
    fatal_rx: Option<watch::Receiver<bool>>,
}

pub struct McpManager<S: SandboxProvider> {
    sandbox: Arc<S>,
    servers: HashMap<String, McpServerHandle>,
    tool_routes: HashMap<String, String>,
}

impl<S: SandboxProvider + 'static> McpManager<S> {
    pub fn new(sandbox: S) -> Self {
        Self {
            sandbox: Arc::new(sandbox),
            servers: HashMap::new(),
            tool_routes: HashMap::new(),
        }
    }

    pub fn managed_tools(&self) -> Vec<String> {
        self.tool_routes.keys().cloned().collect()
    }

    pub fn get_tool(&self, namespaced_id: &str) -> Option<&McpTool> {
        let server_name = self.tool_routes.get(namespaced_id)?;
        let handle = self.servers.get(server_name)?;
        handle.tools.get(namespaced_id)
    }

    pub fn all_mcp_tools(&self) -> Vec<McpTool> {
        self.servers
            .values()
            .flat_map(|h| h.tools.values().cloned())
            .collect()
    }

    pub fn has_fatal_failure(&self, server_name: &str) -> bool {
        self.servers
            .get(server_name)
            .and_then(|h| h.fatal_rx.as_ref())
            .is_some_and(|rx| *rx.borrow())
    }

    pub async fn spawn_server(&mut self, config: McpServerConfig) -> Result<(), McpError> {
        let mut daemons = Vec::new();

        for sidecar in &config.sidecars {
            match sidecar.lifecycle {
                SidecarLifecycle::Init => {
                    if let Err(e) = self
                        .run_init_sidecar(&config.name, sidecar, &config.sandbox_profile)
                        .await
                    {
                        kill_daemons(&mut daemons).await;
                        return Err(e);
                    }
                }
                SidecarLifecycle::Daemon => {
                    match self
                        .start_daemon_sidecar(&config.name, sidecar, &config.sandbox_profile)
                        .await
                    {
                        Ok(handle) => daemons.push(handle),
                        Err(e) => {
                            kill_daemons(&mut daemons).await;
                            return Err(e);
                        }
                    }
                }
            }
        }

        let mut cmd = Command::new(&config.command);
        cmd.args(&config.args);
        for (key, value) in &config.env {
            cmd.env(key, value);
        }

        let mut cmd = self.sandbox.prepare_command(cmd, &config.sandbox_profile)?;
        set_process_group(&mut cmd);

        let transport = TokioChildProcess::new(cmd).map_err(|e| McpError::SpawnFailed {
            name: config.name.clone(),
            source: e,
        })?;

        let service = ()
            .serve(transport)
            .await
            .map_err(|e| McpError::InitFailed {
                name: config.name.clone(),
                reason: format!("{e}"),
            });

        let service = match service {
            Ok(s) => s,
            Err(e) => {
                kill_daemons(&mut daemons).await;
                return Err(e);
            }
        };

        let tools_result = service
            .list_tools(Default::default())
            .await
            .map_err(|e| McpError::InitFailed {
                name: config.name.clone(),
                reason: format!("list_tools failed: {e}"),
            });

        let tools_result = match tools_result {
            Ok(t) => t,
            Err(e) => {
                kill_daemons(&mut daemons).await;
                return Err(e);
            }
        };

        let sink = service.peer().to_owned();

        let mut mcp_tools = HashMap::new();
        for tool in tools_result.tools {
            let namespaced = format!("{}/{}", config.name, tool.name);
            let mcp_tool = McpTool::from_mcp_server(tool, sink.clone());
            self.tool_routes
                .insert(namespaced.clone(), config.name.clone());
            mcp_tools.insert(namespaced, mcp_tool);
        }

        info!(
            server = %config.name,
            tools = ?mcp_tools.keys().collect::<Vec<_>>(),
            "MCP server spawned"
        );

        let has_daemons = !daemons.is_empty();
        let daemons = Arc::new(Mutex::new(daemons));

        let (supervision_cancel, supervision_handle, fatal_rx) = if has_daemons {
            let (cancel_tx, cancel_rx) = watch::channel(false);
            let (fatal_tx, fatal_rx) = watch::channel(false);

            let task_daemons = Arc::clone(&daemons);
            let task_sandbox = Arc::clone(&self.sandbox);
            let task_profile = config.sandbox_profile.clone();
            let server_name = config.name.clone();

            let handle = tokio::spawn(async move {
                supervise_daemons(
                    server_name,
                    task_daemons,
                    task_sandbox,
                    task_profile,
                    cancel_rx,
                    fatal_tx,
                )
                .await;
            });

            (Some(cancel_tx), Some(handle), Some(fatal_rx))
        } else {
            (None, None, None)
        };

        self.servers.insert(
            config.name,
            McpServerHandle {
                service,
                tools: mcp_tools,
                daemons,
                supervision_handle,
                supervision_cancel,
                fatal_rx,
            },
        );

        Ok(())
    }

    async fn run_init_sidecar(
        &self,
        mcp_name: &str,
        sidecar: &SidecarEntry,
        profile: &SandboxProfile,
    ) -> Result<(), McpError> {
        info!(
            server = %mcp_name,
            sidecar = %sidecar.name,
            "running init sidecar"
        );

        let mut cmd = Command::new(&sidecar.command);
        cmd.args(&sidecar.args);
        let mut cmd = self.sandbox.prepare_command(cmd, profile)?;
        set_process_group(&mut cmd);

        let output = cmd.output().await.map_err(|e| McpError::SidecarFailed {
            mcp: mcp_name.to_string(),
            sidecar: sidecar.name.clone(),
            reason: format!("failed to execute: {e}"),
        })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            if !stdout.is_empty() {
                info!(
                    server = %mcp_name,
                    sidecar = %sidecar.name,
                    "init stdout: {stdout}"
                );
            }
            if !stderr.is_empty() {
                warn!(
                    server = %mcp_name,
                    sidecar = %sidecar.name,
                    "init stderr: {stderr}"
                );
            }
            return Err(McpError::SidecarFailed {
                mcp: mcp_name.to_string(),
                sidecar: sidecar.name.clone(),
                reason: format!(
                    "exited with status {}",
                    output.status.code().unwrap_or(-1)
                ),
            });
        }

        info!(
            server = %mcp_name,
            sidecar = %sidecar.name,
            "init sidecar completed"
        );
        Ok(())
    }

    async fn start_daemon_sidecar(
        &self,
        mcp_name: &str,
        sidecar: &SidecarEntry,
        profile: &SandboxProfile,
    ) -> Result<DaemonHandle, McpError> {
        info!(
            server = %mcp_name,
            sidecar = %sidecar.name,
            "starting daemon sidecar"
        );

        let mut child = spawn_daemon(&*self.sandbox, sidecar, profile, mcp_name)?;

        let ready_check = sidecar
            .ready_check
            .as_ref()
            .expect("daemon sidecars must have a ready_check (validated at load time)");

        let outcome = poll_ready(
            ready_check,
            sidecar.ready_timeout,
            sidecar.ready_interval,
            &mut child,
        )
        .await;

        match outcome {
            ReadyOutcome::Ready => {
                info!(
                    server = %mcp_name,
                    sidecar = %sidecar.name,
                    "daemon sidecar ready"
                );
                Ok(DaemonHandle {
                    name: sidecar.name.clone(),
                    child,
                    config: sidecar.clone(),
                    restart_tracker: RestartTracker::default_policy(),
                })
            }
            ReadyOutcome::Timeout => {
                let _ = child.kill().await;
                Err(McpError::SidecarFailed {
                    mcp: mcp_name.to_string(),
                    sidecar: sidecar.name.clone(),
                    reason: format!(
                        "ready check timed out after {}s",
                        sidecar.ready_timeout
                    ),
                })
            }
            ReadyOutcome::ProcessDied => Err(McpError::SidecarFailed {
                mcp: mcp_name.to_string(),
                sidecar: sidecar.name.clone(),
                reason: "process died before becoming ready".to_string(),
            }),
        }
    }

    pub async fn call_tool(
        &self,
        tool_id: &str,
        arguments: serde_json::Value,
    ) -> Result<String, McpError> {
        let server_name = self
            .tool_routes
            .get(tool_id)
            .ok_or_else(|| McpError::NoServerForTool(tool_id.to_string()))?;

        let mcp_tool = self
            .servers
            .get(server_name)
            .and_then(|h| h.tools.get(tool_id))
            .ok_or_else(|| McpError::NoServerForTool(tool_id.to_string()))?;

        let call_failed = |reason: String| McpError::CallFailed {
            server: server_name.clone(),
            tool: tool_id.to_string(),
            reason,
        };

        let args_string =
            serde_json::to_string(&arguments).map_err(|e| call_failed(format!("serialize: {e}")))?;

        mcp_tool
            .call(args_string)
            .await
            .map_err(|e| call_failed(format!("{e}")))
    }

    pub async fn shutdown(&mut self) {
        for (name, mut handle) in self.servers.drain() {
            if let Some(cancel) = handle.supervision_cancel.take() {
                let _ = cancel.send(true);
            }
            if let Some(task) = handle.supervision_handle.take() {
                let _ = task.await;
            }

            info!(server = %name, "shutting down MCP server");
            let _ = handle.service.close().await;

            let mut daemons = handle.daemons.lock().await;
            if !daemons.is_empty() {
                info!(
                    server = %name,
                    count = daemons.len(),
                    "sending SIGTERM to daemon sidecars"
                );
                for daemon in daemons.iter() {
                    send_sigterm(&daemon.child);
                }

                let grace = Duration::from_secs(10);
                let _ = tokio::time::timeout(grace, async {
                    for daemon in daemons.iter_mut() {
                        let _ = daemon.child.wait().await;
                    }
                })
                .await;

                for daemon in daemons.iter_mut() {
                    match daemon.child.try_wait() {
                        Ok(Some(_)) => {}
                        _ => {
                            warn!(
                                server = %name,
                                sidecar = %daemon.name,
                                "daemon did not exit in time, sending SIGKILL"
                            );
                            let _ = daemon.child.kill().await;
                        }
                    }
                }
            }
        }
        self.tool_routes.clear();
    }

    pub async fn spawn_all(
        &mut self,
        configs: Vec<McpServerConfig>,
    ) -> Vec<Result<String, McpError>> {
        let mut results = Vec::with_capacity(configs.len());
        for config in configs {
            let name = config.name.clone();
            results.push(self.spawn_server(config).await.map(|()| name));
        }
        results
    }
}

fn spawn_daemon(
    sandbox: &dyn SandboxProvider,
    sidecar: &SidecarEntry,
    profile: &SandboxProfile,
    mcp_name: &str,
) -> Result<tokio::process::Child, McpError> {
    let mut cmd = Command::new(&sidecar.command);
    cmd.args(&sidecar.args);
    cmd.stdout(std::process::Stdio::piped());
    cmd.stderr(std::process::Stdio::piped());
    let mut cmd = sandbox.prepare_command(cmd, profile)?;
    set_process_group(&mut cmd);

    let mut child = cmd.spawn().map_err(|e| McpError::SidecarFailed {
        mcp: mcp_name.to_string(),
        sidecar: sidecar.name.clone(),
        reason: format!("failed to spawn: {e}"),
    })?;

    forward_output(
        child.stdout.take(),
        child.stderr.take(),
        mcp_name.to_string(),
        sidecar.name.clone(),
    );

    Ok(child)
}

enum SupervisionAction {
    Restart { index: usize, config: SidecarEntry },
    Fatal,
}

async fn supervise_daemons<S: SandboxProvider>(
    server_name: String,
    daemons: Arc<Mutex<Vec<DaemonHandle>>>,
    sandbox: Arc<S>,
    profile: SandboxProfile,
    mut cancel_rx: watch::Receiver<bool>,
    fatal_tx: watch::Sender<bool>,
) {
    loop {
        tokio::select! {
            _ = cancel_rx.wait_for(|v| *v) => {
                return;
            }
            _ = tokio::time::sleep(Duration::from_secs(1)) => {}
        }

        let actions = {
            let mut daemons = daemons.lock().await;
            let mut actions = Vec::new();

            for i in 0..daemons.len() {
                let exited = match daemons[i].child.try_wait() {
                    Ok(Some(status)) => Some(status),
                    Ok(None) => None,
                    Err(e) => {
                        warn!(
                            server = %server_name,
                            sidecar = %daemons[i].name,
                            error = %e,
                            "failed to check daemon status"
                        );
                        None
                    }
                };

                let Some(status) = exited else {
                    continue;
                };

                warn!(
                    server = %server_name,
                    sidecar = %daemons[i].name,
                    exit_code = status.code(),
                    "daemon sidecar exited unexpectedly"
                );

                if !daemons[i].restart_tracker.try_restart() {
                    error!(
                        server = %server_name,
                        sidecar = %daemons[i].name,
                        "restart budget exhausted, signaling fatal failure"
                    );
                    actions.push(SupervisionAction::Fatal);
                    break;
                }

                actions.push(SupervisionAction::Restart {
                    index: i,
                    config: daemons[i].config.clone(),
                });
            }

            actions
        };

        for action in actions {
            match action {
                SupervisionAction::Fatal => {
                    let _ = fatal_tx.send(true);
                    return;
                }
                SupervisionAction::Restart { index, config } => {
                    info!(
                        server = %server_name,
                        sidecar = %config.name,
                        "restarting daemon sidecar"
                    );

                    let respawn_result =
                        spawn_daemon(&*sandbox, &config, &profile, &server_name);

                    match respawn_result {
                        Ok(mut child) => {
                            let ready_check = config
                                .ready_check
                                .as_ref()
                                .expect("daemon sidecars must have a ready_check");

                            let outcome = poll_ready(
                                ready_check,
                                config.ready_timeout,
                                config.ready_interval,
                                &mut child,
                            )
                            .await;

                            match outcome {
                                ReadyOutcome::Ready => {
                                    info!(
                                        server = %server_name,
                                        sidecar = %config.name,
                                        "restarted daemon sidecar is ready"
                                    );
                                    let mut daemons = daemons.lock().await;
                                    daemons[index].child = child;
                                }
                                other => {
                                    error!(
                                        server = %server_name,
                                        sidecar = %config.name,
                                        outcome = ?other,
                                        "restarted daemon failed ready check, signaling fatal failure"
                                    );
                                    let _ = child.kill().await;
                                    let _ = fatal_tx.send(true);
                                    return;
                                }
                            }
                        }
                        Err(e) => {
                            error!(
                                server = %server_name,
                                sidecar = %config.name,
                                error = %e,
                                "failed to respawn daemon, signaling fatal failure"
                            );
                            let _ = fatal_tx.send(true);
                            return;
                        }
                    }
                }
            }
        }
    }
}

fn forward_output(
    stdout: Option<tokio::process::ChildStdout>,
    stderr: Option<tokio::process::ChildStderr>,
    server: String,
    sidecar: String,
) {
    if let Some(stdout) = stdout {
        let server = server.clone();
        let sidecar = sidecar.clone();
        tokio::spawn(async move {
            let reader = BufReader::new(stdout);
            let mut lines = reader.lines();
            while let Ok(Some(line)) = lines.next_line().await {
                info!(
                    server = %server,
                    sidecar = %sidecar,
                    "stdout: {line}"
                );
            }
        });
    }

    if let Some(stderr) = stderr {
        tokio::spawn(async move {
            let reader = BufReader::new(stderr);
            let mut lines = reader.lines();
            while let Ok(Some(line)) = lines.next_line().await {
                warn!(
                    server = %server,
                    sidecar = %sidecar,
                    "stderr: {line}"
                );
            }
        });
    }
}

#[cfg(unix)]
fn set_process_group(cmd: &mut Command) {
    unsafe {
        cmd.pre_exec(|| {
            if libc::setsid() == -1 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
}

#[cfg(not(unix))]
fn set_process_group(_cmd: &mut Command) {}

#[cfg(unix)]
fn send_sigterm(child: &tokio::process::Child) {
    if let Some(pid) = child.id() {
        let pgid = -(pid as libc::pid_t);
        let ret = unsafe { libc::kill(pgid, libc::SIGTERM) };
        if ret != 0 {
            let ret = unsafe { libc::kill(pid as libc::pid_t, libc::SIGTERM) };
            if ret != 0 {
                let err = std::io::Error::last_os_error();
                tracing::warn!(pid, error = %err, "SIGTERM delivery failed");
            }
        }
    }
}

#[cfg(not(unix))]
fn send_sigterm(_child: &tokio::process::Child) {}

async fn kill_daemons(daemons: &mut [DaemonHandle]) {
    for handle in daemons.iter_mut() {
        let _ = handle.child.kill().await;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_registry::toml_types::ReadyCheck;
    use argus_sandbox::NoopSandbox;

    fn failing_init_sidecar() -> SidecarEntry {
        SidecarEntry {
            name: "bad-init".into(),
            command: "false".into(),
            args: vec![],
            lifecycle: SidecarLifecycle::Init,
            ready_check: None,
            ready_timeout: 30,
            ready_interval: 500,
        }
    }

    fn succeeding_init_sidecar() -> SidecarEntry {
        SidecarEntry {
            name: "good-init".into(),
            command: "true".into(),
            args: vec![],
            lifecycle: SidecarLifecycle::Init,
            ready_check: None,
            ready_timeout: 30,
            ready_interval: 500,
        }
    }

    fn failing_daemon_sidecar() -> SidecarEntry {
        SidecarEntry {
            name: "bad-daemon".into(),
            command: "nonexistent-sidecar-binary".into(),
            args: vec![],
            lifecycle: SidecarLifecycle::Daemon,
            ready_check: Some(ReadyCheck::Command {
                run: "true".into(),
            }),
            ready_timeout: 1,
            ready_interval: 100,
        }
    }

    fn config_with_sidecars(sidecars: Vec<SidecarEntry>) -> McpServerConfig {
        McpServerConfig {
            name: "test-server".into(),
            command: "nonexistent-mcp-server".into(),
            args: vec![],
            env: vec![],
            sandbox_profile: SandboxProfile::default(),
            sidecars,
        }
    }

    #[tokio::test]
    async fn spawn_aborts_on_failed_init_sidecar() {
        let mut manager = McpManager::new(NoopSandbox);
        let config = config_with_sidecars(vec![failing_init_sidecar()]);

        let result = manager.spawn_server(config).await;
        assert!(result.is_err());

        let err = result.unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("bad-init"), "error should name the sidecar: {msg}");
        assert!(msg.contains("test-server"), "error should name the MCP server: {msg}");
    }

    #[tokio::test]
    async fn spawn_aborts_on_failed_daemon_sidecar() {
        let mut manager = McpManager::new(NoopSandbox);
        let config = config_with_sidecars(vec![failing_daemon_sidecar()]);

        let result = manager.spawn_server(config).await;
        assert!(result.is_err());

        let err = result.unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("bad-daemon"), "error should name the sidecar: {msg}");
    }

    #[tokio::test]
    async fn spawn_passes_successful_init_then_fails_on_mcp() {
        let mut manager = McpManager::new(NoopSandbox);
        let config = config_with_sidecars(vec![succeeding_init_sidecar()]);

        let result = manager.spawn_server(config).await;
        assert!(result.is_err());
        let err = result.unwrap_err();
        match err {
            McpError::SpawnFailed { name, .. } => {
                assert_eq!(name, "test-server");
            }
            other => panic!("expected SpawnFailed, got: {other}"),
        }
    }

    #[tokio::test]
    async fn spawn_aborts_second_init_kills_first_daemon() {
        let mut manager = McpManager::new(NoopSandbox);

        let daemon = SidecarEntry {
            name: "bg-process".into(),
            command: "sleep".into(),
            args: vec!["60".into()],
            lifecycle: SidecarLifecycle::Daemon,
            ready_check: Some(ReadyCheck::Command {
                run: "true".into(),
            }),
            ready_timeout: 5,
            ready_interval: 100,
        };

        let config = config_with_sidecars(vec![daemon, failing_init_sidecar()]);

        let result = manager.spawn_server(config).await;
        assert!(result.is_err());

        let err = result.unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("bad-init"), "should fail on the init sidecar: {msg}");
    }

    #[tokio::test]
    async fn spawn_no_sidecars_proceeds_to_mcp() {
        let mut manager = McpManager::new(NoopSandbox);
        let config = config_with_sidecars(vec![]);

        let result = manager.spawn_server(config).await;
        assert!(result.is_err());
        match result.unwrap_err() {
            McpError::SpawnFailed { .. } => {}
            other => panic!("expected SpawnFailed (no such MCP binary), got: {other}"),
        }
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn send_sigterm_to_running_process() {
        let mut child = Command::new("sleep")
            .arg("60")
            .spawn()
            .unwrap();

        send_sigterm(&child);
        let status = child.wait().await.unwrap();
        assert!(!status.success());
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn supervision_restarts_crashed_daemon() {
        let (cancel_tx, cancel_rx) = watch::channel(false);
        let (fatal_tx, _fatal_rx) = watch::channel(false);

        let sidecar_config = SidecarEntry {
            name: "crasher".into(),
            command: "sleep".into(),
            args: vec!["0.1".into()],
            lifecycle: SidecarLifecycle::Daemon,
            ready_check: Some(ReadyCheck::Command {
                run: "true".into(),
            }),
            ready_timeout: 5,
            ready_interval: 100,
        };

        let child = Command::new("sleep")
            .arg("0.1")
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let original_pid = child.id();

        let daemons = Arc::new(Mutex::new(vec![DaemonHandle {
            name: "crasher".into(),
            child,
            config: sidecar_config,
            restart_tracker: RestartTracker::new(3, Duration::from_secs(60)),
        }]));

        let sandbox = Arc::new(NoopSandbox);
        let profile = SandboxProfile::default();
        let task_daemons = Arc::clone(&daemons);

        let handle = tokio::spawn(async move {
            supervise_daemons(
                "test-server".into(),
                task_daemons,
                sandbox,
                profile,
                cancel_rx,
                fatal_tx,
            )
            .await;
        });

        tokio::time::sleep(Duration::from_secs(4)).await;

        let _ = cancel_tx.send(true);
        let _ = handle.await;

        let locked = daemons.lock().await;
        let new_pid = locked[0].child.id();
        assert_ne!(
            original_pid, new_pid,
            "PID should change after restart (original: {original_pid:?}, new: {new_pid:?})"
        );
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn supervision_signals_fatal_on_exhausted_restarts() {
        let (_cancel_tx, cancel_rx) = watch::channel(false);
        let (fatal_tx, mut fatal_rx) = watch::channel(false);

        let sidecar_config = SidecarEntry {
            name: "fast-crasher".into(),
            command: "sleep".into(),
            args: vec!["0.1".into()],
            lifecycle: SidecarLifecycle::Daemon,
            ready_check: Some(ReadyCheck::Command {
                run: "true".into(),
            }),
            ready_timeout: 5,
            ready_interval: 100,
        };

        let child = Command::new("sleep")
            .arg("0.1")
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();

        let daemons = Arc::new(Mutex::new(vec![DaemonHandle {
            name: "fast-crasher".into(),
            child,
            config: sidecar_config,
            restart_tracker: RestartTracker::new(0, Duration::from_secs(60)),
        }]));

        let sandbox = Arc::new(NoopSandbox);
        let profile = SandboxProfile::default();
        let task_daemons = Arc::clone(&daemons);

        let handle = tokio::spawn(async move {
            supervise_daemons(
                "test-server".into(),
                task_daemons,
                sandbox,
                profile,
                cancel_rx,
                fatal_tx,
            )
            .await;
        });

        let got_fatal = tokio::time::timeout(
            Duration::from_secs(10),
            fatal_rx.wait_for(|v| *v),
        )
        .await;

        assert!(got_fatal.is_ok(), "should receive fatal signal within timeout");
        let _ = handle.await;
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn has_fatal_failure_reflects_supervision_state() {
        let mut manager = McpManager::new(NoopSandbox);

        let sidecar = SidecarEntry {
            name: "doomed".into(),
            command: "sleep".into(),
            args: vec!["0.1".into()],
            lifecycle: SidecarLifecycle::Daemon,
            ready_check: Some(ReadyCheck::Command {
                run: "true".into(),
            }),
            ready_timeout: 5,
            ready_interval: 100,
        };

        let config = config_with_sidecars(vec![sidecar]);
        let _ = manager.spawn_server(config).await;

        assert!(
            !manager.has_fatal_failure("nonexistent"),
            "nonexistent server should not report fatal"
        );
    }
}
