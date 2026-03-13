use std::path::PathBuf;

use anyhow::{Context, Result};
use argus_analysis::{
    InstallDetection, ManifestKind, OrchestratorConfig, RegistryAnalysisReport, RegistryAnalyzer,
    ToolContext, audit_dependencies, detect_install,
};
use argus_config::ExtractionProviderConfig;
use argus_registry::toml_types::InstallConfig;
use argus_registry::{
    AssemblyInput, assemble_mcp_entry, generate_sandbox_config, write_registry_entry,
};
use tracing::{info, warn};

use crate::git;

pub struct RegistryAddOptions {
    pub url: String,
    pub git_ref: Option<String>,
    pub track: bool,
    pub dry_run: bool,
    pub report_only: bool,
    pub argus_home: PathBuf,
    pub provider: ExtractionProviderConfig,
    pub max_turns: usize,
    pub max_tokens: u64,
}

pub async fn run_registry_add(opts: RegistryAddOptions) -> Result<()> {
    let clone_dir = tempfile::tempdir().context("Failed to create temp directory")?;
    let clone_path = clone_dir.path().to_path_buf();

    let url = opts.url.clone();
    let git_ref = opts.git_ref.clone();
    let path = clone_path.clone();
    let pinned_ref = tokio::task::spawn_blocking(move || -> Result<String> {
        info!(url = %url, "Cloning repository");
        git::clone_repo(&url, git_ref.as_deref(), &path)?;
        let commit = git::head_commit(&path)?;
        info!(pinned_ref = %commit, "Pinned to commit");
        Ok(commit)
    })
    .await
    .context("Clone task panicked")??;

    let tool_ctx = ToolContext::new(&clone_path)?;
    let manifest_kind = tool_ctx.detect_manifest().context(
        "No recognized manifest found (package.json, Cargo.toml, pyproject.toml, go.mod)",
    )?;
    let manifest_content = tool_ctx.read_file(manifest_filename(&manifest_kind), None, None)?;

    info!("Analyzing dependencies");
    let dep_report = audit_dependencies(&manifest_kind, &manifest_content).await;
    info!(
        total = dep_report.total,
        vulnerabilities = dep_report.vulnerabilities.len(),
        flagged = dep_report.flagged.len(),
        "Dependency audit complete"
    );

    let install_detection = detect_install(&manifest_kind, &manifest_content);
    info!(
        method = %install_detection.method,
        package = %install_detection.package,
        "Detected install method"
    );

    info!("Running LLM capability inference");
    let analyzer = RegistryAnalyzer::from_config(&opts.provider)
        .context("Failed to initialize LLM provider")?
        .with_orchestrator_config(OrchestratorConfig {
            max_turns: opts.max_turns,
            max_tokens: opts.max_tokens,
        });
    let capabilities = analyzer
        .infer_capabilities(&clone_path)
        .await
        .context("Capability inference failed")?;
    info!(count = capabilities.len(), "Capabilities inferred");

    for cap in &capabilities {
        info!(
            capability = %cap.capability,
            evidence_count = cap.evidence.len(),
            "Found capability"
        );
    }

    let cap_strings: Vec<String> = capabilities.iter().map(|c| c.capability.clone()).collect();
    let sandbox_config = generate_sandbox_config(&cap_strings);
    let name = derive_tool_name(&opts.url);

    let report = RegistryAnalysisReport {
        tool: name.clone(),
        analyzed_at: chrono::Utc::now().to_rfc3339(),
        pinned_ref: pinned_ref.clone(),
        capabilities: capabilities.clone(),
        dependencies: dep_report,
        install_detection: install_detection.clone(),
    };

    let report_json = serde_json::to_string_pretty(&report)?;

    if opts.report_only {
        println!("{report_json}");
        return Ok(());
    }

    let install_config = to_install_config(&install_detection);
    let entry = assemble_mcp_entry(AssemblyInput {
        name: name.clone(),
        description: format!("Auto-analyzed from {}", opts.url),
        repository: opts.url.clone(),
        pinned_ref,
        track: opts.track,
        capabilities: cap_strings,
        install: install_config,
        sandbox: sandbox_config,
    });

    if opts.dry_run {
        let toml_str = toml::to_string_pretty(&entry)?;
        println!("{report_json}");
        println!("{toml_str}");
        return Ok(());
    }

    let registry_dir = opts.argus_home.join("local-registry");
    write_registry_entry(&registry_dir, &name, &entry, &report_json)?;
    info!(
        toml_path = %registry_dir.join("mcps").join(format!("{name}.toml")).display(),
        report_path = %registry_dir.join("reports").join(format!("{name}.json")).display(),
        "Registry entry written"
    );

    Ok(())
}

fn manifest_filename(kind: &ManifestKind) -> &'static str {
    match kind {
        ManifestKind::PackageJson => "package.json",
        ManifestKind::CargoToml => "Cargo.toml",
        ManifestKind::PyprojectToml => "pyproject.toml",
        ManifestKind::GoMod => "go.mod",
    }
}

fn derive_tool_name(url: &str) -> String {
    url.trim_end_matches('/')
        .rsplit('/')
        .next()
        .unwrap_or("unknown")
        .trim_end_matches(".git")
        .to_string()
}

fn to_install_config(detection: &InstallDetection) -> InstallConfig {
    match detection.method.as_str() {
        "npm" => InstallConfig::Npm {
            package: detection.package.clone(),
            version: detection.version.clone(),
        },
        "cargo" => InstallConfig::Cargo {
            crate_name: detection.package.clone(),
            version: detection.version.clone(),
        },
        "pip" => InstallConfig::Pip {
            package: detection.package.clone(),
            version: detection.version.clone(),
            python_version: None,
        },
        other => {
            warn!(
                method = other,
                "No native install config for this method, using binary placeholder"
            );
            InstallConfig::Binary {
                url: format!("TODO: fill in binary URL for {} package", other),
                checksum: "TODO: fill in checksum".to_string(),
            }
        }
    }
}
