use std::collections::{BTreeSet, HashMap};
use std::path::Path;
use std::sync::Arc;

use anyhow::Context;
use tokio::sync::RwLock;
use tracing::info;

use argus_audit::InMemoryEventStore;
use argus_gateway::{
    ArgusGrpcService, GatewayService, LlmFormat, LlmProxy, McpManager, McpServerConfig,
    ProxyConfig, UpstreamConfig,
};
use argus_kernel::{BackgroundTheoryBuilder, CapKind, ConfLevel, EgressKind, ToolId, ToolMetadata};
use argus_oracle::{CedarAuthorizer, FilePolicySource, MockContentGate};
use argus_registry::toml_loader::TomlRegistry;
use argus_registry::extract_env_defaults;
use argus_registry::toml_types::{InstallConfig, McpEntry, SandboxNetPolicy};
use argus_sandbox::{NetPolicy, NoopSandbox, OsSandbox, ProfileBuilder, SandboxProfile};

use crate::config::{DaemonConfig, ProxyCfg, UpstreamFormat, expand_tilde};

pub async fn run_serve(config_path: &str) -> anyhow::Result<()> {
    let config = DaemonConfig::load(Path::new(config_path))?;

    tracing_subscriber::fmt()
        .with_env_filter(&config.server.log_level)
        .init();

    info!("starting argus daemon");

    let registry_path = expand_tilde(&config.server.registry_path);
    let toml_registry = load_registry(&registry_path)?;
    let bg = build_background_theory(&toml_registry.mcps);

    let policy_path = expand_tilde(&config.server.policy_path);
    let policy_dir = Path::new(&policy_path);
    if !policy_dir.is_dir() {
        tracing::warn!(path = %policy_path, "policy directory not found, creating empty");
        std::fs::create_dir_all(policy_dir)
            .with_context(|| format!("failed to create policy dir: {policy_path}"))?;
    }
    let source = FilePolicySource::new(policy_dir);
    let authorizer =
        CedarAuthorizer::new(&source).context("failed to load Cedar policies")?;

    let content_gate = MockContentGate::default();
    let event_store = InMemoryEventStore::new();
    let gateway = Arc::new(GatewayService::new(bg, authorizer, content_gate, event_store));

    let sandbox: Box<dyn argus_sandbox::SandboxProvider> = match OsSandbox::new() {
        Ok(s) => {
            info!("sandbox enforcement enabled via argus-sandbox-exec");
            Box::new(s)
        }
        Err(e) => {
            tracing::warn!(error = %e, "sandbox wrapper not found, using NoopSandbox");
            Box::new(NoopSandbox)
        }
    };
    let mcp = Arc::new(RwLock::new(McpManager::new(sandbox)));
    let mcp_configs = build_mcp_configs(&toml_registry.mcps);
    if !mcp_configs.is_empty() {
        let mut mcp_lock = mcp.write().await;
        for result in mcp_lock.spawn_all(mcp_configs).await {
            match result {
                Ok(name) => info!(server = %name, "MCP server ready"),
                Err(e) => tracing::warn!(error = %e, "failed to spawn MCP server"),
            }
        }
    } else {
        tracing::warn!("no MCP servers configured in registry");
    }

    {
        let mcp_lock = mcp.read().await;
        for tool_name in mcp_lock.managed_tools() {
            if let Err(e) = gateway.register_tool(ToolId::new(&tool_name)).await {
                tracing::warn!(tool = %tool_name, error = %e, "failed to register discovered tool");
            }
        }
    }

    let (shutdown_tx, _) = tokio::sync::watch::channel(false);
    let mut handles = Vec::new();

    if let Some(ref grpc_cfg) = config.grpc
        && grpc_cfg.enabled
    {
        let addr = grpc_cfg
            .address
            .parse()
            .context("invalid gRPC address")?;
        let grpc_svc = ArgusGrpcService::new(gateway.clone());
        let mut shutdown_rx = shutdown_tx.subscribe();
        handles.push(tokio::spawn(async move {
            info!("gRPC server listening on {addr}");
            tonic::transport::Server::builder()
                .add_service(grpc_svc.into_server())
                .serve_with_shutdown(addr, async move {
                    let _ = shutdown_rx.changed().await;
                })
                .await
                .ok();
        }));
    }

    if let Some(ref proxy_cfg) = config.proxy
        && proxy_cfg.enabled
    {
        let proxy_config = build_proxy_config(proxy_cfg);
        let proxy = Arc::new(LlmProxy::new(gateway.clone(), mcp.clone(), proxy_config));
        let listener = tokio::net::TcpListener::bind(&proxy_cfg.address)
            .await
            .context("failed to bind proxy address")?;
        let mut shutdown_rx = shutdown_tx.subscribe();
        handles.push(tokio::spawn(async move {
            tokio::select! {
                _ = proxy.serve(listener) => {}
                _ = shutdown_rx.changed() => {
                    info!("LLM proxy shutting down");
                }
            }
        }));
    }

    info!("argus daemon ready");
    tokio::signal::ctrl_c().await.ok();
    info!("shutdown signal received");

    let _ = shutdown_tx.send(true);

    let timeout = std::time::Duration::from_secs(config.server.shutdown_timeout_secs);
    let _ = tokio::time::timeout(timeout, async {
        for h in handles {
            let _ = h.await;
        }
    })
    .await;

    mcp.write().await.shutdown().await;

    info!("argus daemon stopped");
    Ok(())
}

fn load_registry(path: &str) -> anyhow::Result<TomlRegistry> {
    let registry_dir = Path::new(path);
    if !registry_dir.is_dir() {
        tracing::warn!(path = %path, "registry directory not found, starting with empty registry");
        return Ok(TomlRegistry::empty());
    }
    TomlRegistry::load_from_dir(registry_dir).context("failed to load registry")
}

fn parse_cap_kind(s: &str) -> Option<CapKind> {
    let base = s.split('(').next().unwrap_or(s);
    match base {
        "filesystem:read" => Some(CapKind::FilesystemRead),
        "filesystem:write" => Some(CapKind::FilesystemWrite),
        "filesystem:delete" => Some(CapKind::FilesystemDelete),
        "network:egress" => Some(CapKind::NetworkEgress),
        "network:ingress" => Some(CapKind::NetworkIngress),
        "execution:shell" => Some(CapKind::ExecutionShell),
        "execution:code" => Some(CapKind::ExecutionCode),
        "credentials" => Some(CapKind::Credentials),
        "system:info" => Some(CapKind::SystemInfo),
        "system:modify" => Some(CapKind::SystemModify),
        "clipboard" => Some(CapKind::Clipboard),
        "browser:navigate" => Some(CapKind::BrowserNavigate),
        "database:read" => Some(CapKind::DatabaseRead),
        "database:write" => Some(CapKind::DatabaseWrite),
        "ipc" => Some(CapKind::Ipc),
        _ => None,
    }
}

fn cap_to_egress(cap: &CapKind) -> Option<EgressKind> {
    match cap {
        CapKind::NetworkEgress => Some(EgressKind::NetworkExternal),
        CapKind::NetworkIngress => Some(EgressKind::NetworkInternal),
        CapKind::FilesystemWrite | CapKind::FilesystemDelete => Some(EgressKind::FilesystemWrite),
        CapKind::Ipc => Some(EgressKind::Ipc),
        _ => None,
    }
}

fn build_background_theory(mcps: &HashMap<String, McpEntry>) -> argus_kernel::BackgroundTheory {
    let mut builder = BackgroundTheoryBuilder::new();
    for (name, entry) in mcps {
        let capabilities: BTreeSet<CapKind> = entry
            .metadata
            .capabilities
            .iter()
            .filter_map(|s| parse_cap_kind(s))
            .collect();

        let egress: BTreeSet<EgressKind> =
            capabilities.iter().filter_map(cap_to_egress).collect();

        let metadata = ToolMetadata {
            capabilities,
            egress,
            conf_floor: ConfLevel::Public,
            endorsed: matches!(entry.metadata.integrity.as_str(), "verified" | "proven"),
        };
        builder.register_tool(ToolId::new(name), metadata);
    }
    builder.build()
}

fn build_mcp_configs(mcps: &HashMap<String, McpEntry>) -> Vec<McpServerConfig> {
    let mut configs = Vec::new();
    for (name, entry) in mcps {
        let (command, args) = match &entry.install {
            InstallConfig::Npm { package, version } => {
                let mut args = vec!["-y".to_string(), format!("{package}@{version}")];
                args.extend(entry.args.default.clone());
                ("npx".to_string(), args)
            }
            _ => {
                tracing::warn!(server = %name, "unsupported install type for auto-spawn, skipping");
                continue;
            }
        };

        let mut daemon_env = HashMap::new();
        let missing: Vec<_> = entry
            .env
            .iter()
            .filter_map(|(k, v)| {
                match std::env::var(k) {
                    Ok(val) => { daemon_env.insert(k.clone(), val); None }
                    Err(_) if v.required => Some(k.as_str()),
                    Err(_) => None,
                }
            })
            .collect();
        if !missing.is_empty() {
            tracing::warn!(server = %name, missing = ?missing, "skipping due to missing required env vars");
            continue;
        }

        let env: Vec<(String, String)> = daemon_env
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        let sandbox_profile = build_sandbox_profile(name, entry, &daemon_env);

        configs.push(McpServerConfig {
            name: name.clone(),
            command,
            args,
            env,
            sandbox_profile,
            sidecars: entry.sidecars.clone(),
        });
    }
    configs
}

fn build_sandbox_profile(
    name: &str,
    entry: &McpEntry,
    daemon_env: &HashMap<String, String>,
) -> SandboxProfile {
    let mut builder = ProfileBuilder::new();

    let mut resolved = extract_env_defaults(&entry.env);
    resolved.extend(daemon_env.iter().map(|(k, v)| (k.clone(), v.clone())));
    if !resolved.is_empty() {
        builder = builder.resolved_env(resolved);
    }

    if let Some(cfg) = &entry.sandbox {
        builder = builder
            .extra_read(cfg.extra_read.clone())
            .extra_write(cfg.extra_write.clone());

        let policy = cfg.net_policy.as_ref().map(|net| match net {
            SandboxNetPolicy::Blocked => NetPolicy::Blocked,
            SandboxNetPolicy::Egress => NetPolicy::EgressOnly,
            SandboxNetPolicy::EgressDomains(domains) => {
                NetPolicy::EgressWithDomains(domains.clone())
            }
        });
        if let Some(policy) = policy {
            builder = builder.net_policy(policy);
        }
    }

    builder.build().unwrap_or_else(|e| {
        tracing::error!(server = %name, error = %e, "sandbox profile construction failed, using default");
        SandboxProfile::default()
    })
}

fn build_proxy_config(proxy_cfg: &ProxyCfg) -> ProxyConfig {
    let upstreams = proxy_cfg
        .upstreams
        .iter()
        .map(|(name, entry)| UpstreamConfig {
            name: name.clone(),
            url: entry.url.clone(),
            format: match entry.format {
                UpstreamFormat::Openai => LlmFormat::OpenAi,
                UpstreamFormat::Anthropic => LlmFormat::Anthropic,
            },
        })
        .collect();

    ProxyConfig {
        max_tool_rounds: proxy_cfg.max_tool_rounds,
        upstreams,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_registry::toml_types::{McpArgs, McpMetadata};

    fn test_mcp_entry(
        name: &str,
        integrity: &str,
        caps: &[&str],
        install: InstallConfig,
    ) -> McpEntry {
        McpEntry {
            metadata: McpMetadata {
                name: name.into(),
                description: String::new(),
                repository: None,
                source: "community".into(),
                integrity: integrity.into(),
                capabilities: caps.iter().map(|s| (*s).into()).collect(),
                schema_hash: None,
                pinned_ref: None,
                track: None,
            },
            install,
            env: HashMap::new(),
            args: McpArgs::default(),
            sandbox: None,
            sidecars: vec![],
        }
    }

    fn npm_install(package: &str, version: &str) -> InstallConfig {
        InstallConfig::Npm {
            package: package.into(),
            version: version.into(),
        }
    }

    #[test]
    fn parse_cap_kind_basic() {
        assert_eq!(parse_cap_kind("filesystem:read"), Some(CapKind::FilesystemRead));
        assert_eq!(parse_cap_kind("network:egress"), Some(CapKind::NetworkEgress));
        assert_eq!(parse_cap_kind("credentials"), Some(CapKind::Credentials));
        assert_eq!(parse_cap_kind("ipc"), Some(CapKind::Ipc));
    }

    #[test]
    fn parse_cap_kind_with_scope() {
        assert_eq!(
            parse_cap_kind("filesystem:read(/tmp/**)"),
            Some(CapKind::FilesystemRead)
        );
        assert_eq!(
            parse_cap_kind("network:egress(api.github.com)"),
            Some(CapKind::NetworkEgress)
        );
        assert_eq!(
            parse_cap_kind("execution:shell(git, ls)"),
            Some(CapKind::ExecutionShell)
        );
    }

    #[test]
    fn parse_cap_kind_unknown() {
        assert_eq!(parse_cap_kind("unknown:capability"), None);
        assert_eq!(parse_cap_kind(""), None);
    }

    #[test]
    fn parse_cap_kind_all_15_variants() {
        let mappings = [
            ("filesystem:read", CapKind::FilesystemRead),
            ("filesystem:write", CapKind::FilesystemWrite),
            ("filesystem:delete", CapKind::FilesystemDelete),
            ("network:egress", CapKind::NetworkEgress),
            ("network:ingress", CapKind::NetworkIngress),
            ("execution:shell", CapKind::ExecutionShell),
            ("execution:code", CapKind::ExecutionCode),
            ("credentials", CapKind::Credentials),
            ("system:info", CapKind::SystemInfo),
            ("system:modify", CapKind::SystemModify),
            ("clipboard", CapKind::Clipboard),
            ("browser:navigate", CapKind::BrowserNavigate),
            ("database:read", CapKind::DatabaseRead),
            ("database:write", CapKind::DatabaseWrite),
            ("ipc", CapKind::Ipc),
        ];
        for (s, expected) in mappings {
            assert_eq!(parse_cap_kind(s), Some(expected), "failed for {s}");
        }
    }

    #[test]
    fn build_background_theory_from_registry() {
        let mut mcps = HashMap::new();
        mcps.insert(
            "fs-server".to_string(),
            test_mcp_entry(
                "fs-server",
                "observed",
                &["filesystem:read", "filesystem:write"],
                npm_install("@mcp/fs", "1.0.0"),
            ),
        );
        mcps.insert(
            "net-server".to_string(),
            test_mcp_entry(
                "net-server",
                "verified",
                &["network:egress"],
                npm_install("@mcp/net", "2.0.0"),
            ),
        );

        let bg = build_background_theory(&mcps);

        let fs_meta = bg.tool_metadata(&ToolId::new("fs-server")).unwrap();
        assert!(fs_meta.capabilities.contains(&CapKind::FilesystemRead));
        assert!(fs_meta.capabilities.contains(&CapKind::FilesystemWrite));
        assert!(fs_meta.egress.contains(&EgressKind::FilesystemWrite));
        assert!(!fs_meta.endorsed);

        let net_meta = bg.tool_metadata(&ToolId::new("net-server")).unwrap();
        assert!(net_meta.capabilities.contains(&CapKind::NetworkEgress));
        assert!(net_meta.egress.contains(&EgressKind::NetworkExternal));
        assert!(net_meta.endorsed);
    }

    #[test]
    fn build_background_theory_empty_registry() {
        let mcps = HashMap::new();
        let bg = build_background_theory(&mcps);
        assert!(bg.tool_metadata(&ToolId::new("anything")).is_none());
    }

    #[test]
    fn build_mcp_configs_npm_only() {
        let mut mcps = HashMap::new();
        mcps.insert(
            "npm-server".to_string(),
            test_mcp_entry("npm-server", "observed", &[], npm_install("@mcp/test", "1.0.0")),
        );
        mcps.insert(
            "binary-server".to_string(),
            test_mcp_entry(
                "binary-server",
                "observed",
                &[],
                InstallConfig::Binary {
                    url: "https://example.com/bin".into(),
                    checksum: "sha256:abc".into(),
                },
            ),
        );

        let configs = build_mcp_configs(&mcps);
        assert_eq!(configs.len(), 1);
        assert_eq!(configs[0].name, "npm-server");
        assert_eq!(configs[0].command, "npx");
        assert_eq!(configs[0].args[0], "-y");
        assert_eq!(configs[0].args[1], "@mcp/test@1.0.0");
    }

    #[test]
    fn build_mcp_configs_includes_default_args() {
        let mut mcps = HashMap::new();
        let mut entry =
            test_mcp_entry("with-args", "observed", &[], npm_install("@mcp/test", "1.0.0"));
        entry.args = McpArgs {
            default: vec!["/home/user/docs".into()],
        };
        mcps.insert("with-args".to_string(), entry);

        let configs = build_mcp_configs(&mcps);
        assert_eq!(configs[0].args.len(), 3);
        assert_eq!(configs[0].args[2], "/home/user/docs");
    }

    #[test]
    fn build_proxy_config_maps_upstreams() {
        let proxy_cfg = ProxyCfg {
            enabled: true,
            address: "127.0.0.1:8080".into(),
            max_tool_rounds: 20,
            upstreams: HashMap::from([
                (
                    "openai".into(),
                    crate::config::UpstreamEntry {
                        url: "https://api.openai.com".into(),
                        format: UpstreamFormat::Openai,
                        api_key_env: None,
                    },
                ),
                (
                    "anthropic".into(),
                    crate::config::UpstreamEntry {
                        url: "https://api.anthropic.com".into(),
                        format: UpstreamFormat::Anthropic,
                        api_key_env: None,
                    },
                ),
            ]),
        };

        let config = build_proxy_config(&proxy_cfg);
        assert_eq!(config.max_tool_rounds, 20);
        assert_eq!(config.upstreams.len(), 2);
        let openai = config.upstreams.iter().find(|u| u.name == "openai").unwrap();
        assert_eq!(openai.format, LlmFormat::OpenAi);
        let anthropic = config
            .upstreams
            .iter()
            .find(|u| u.name == "anthropic")
            .unwrap();
        assert_eq!(anthropic.format, LlmFormat::Anthropic);
    }
}
