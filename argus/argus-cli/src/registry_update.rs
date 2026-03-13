use std::path::PathBuf;

use anyhow::{Context, Result};
use argus_config::ExtractionProviderConfig;
use argus_registry::toml_loader::TomlRegistry;
use tracing::info;

pub struct RegistryUpdateOptions {
    pub name: String,
    pub argus_home: PathBuf,
    pub provider: ExtractionProviderConfig,
    pub max_turns: usize,
    pub max_tokens: u64,
}

pub async fn run_registry_update(opts: RegistryUpdateOptions) -> Result<()> {
    let registry_dir = opts.argus_home.join("local-registry");
    let toml_path = registry_dir
        .join("mcps")
        .join(format!("{}.toml", opts.name));

    if !toml_path.exists() {
        anyhow::bail!(
            "No registry entry found for '{}' at {}",
            opts.name,
            toml_path.display()
        );
    }

    let entry = TomlRegistry::load_mcp(&toml_path)
        .context(format!("Failed to parse TOML for '{}'", opts.name))?;

    let repo_url = entry
        .metadata
        .repository
        .context("Entry has no repository URL, cannot update")?;

    info!(
        tool = %opts.name,
        url = %repo_url,
        "Re-analyzing tool from latest HEAD"
    );

    crate::registry_add::run_registry_add(crate::registry_add::RegistryAddOptions {
        url: repo_url,
        git_ref: None,
        track: entry.metadata.track.unwrap_or(false),
        dry_run: false,
        report_only: false,
        argus_home: opts.argus_home,
        provider: opts.provider,
        max_turns: opts.max_turns,
        max_tokens: opts.max_tokens,
    })
    .await
}
