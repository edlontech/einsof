use std::path::PathBuf;

use anyhow::{Context, Result};
use argus_registry::toml_loader::TomlRegistry;
use tracing::{error, info, warn};

use crate::git;

pub async fn run_registry_check(argus_home: PathBuf) -> Result<()> {
    let registry_dir = argus_home.join("local-registry");
    let mcps_dir = registry_dir.join("mcps");

    if !mcps_dir.exists() {
        warn!(path = %mcps_dir.display(), "No registry entries found");
        return Ok(());
    }

    let registry =
        TomlRegistry::load_from_dir(&registry_dir).context("Failed to load registry")?;

    let tracked: Vec<_> = registry
        .mcps
        .iter()
        .filter(|(_, entry)| entry.metadata.track.unwrap_or(false))
        .collect();

    if tracked.is_empty() {
        info!("No tracked tools found, use --track when adding to enable drift detection");
        return Ok(());
    }

    info!(count = tracked.len(), "Checking tracked tools for drift");

    for (name, entry) in &tracked {
        let repo_url = match &entry.metadata.repository {
            Some(url) => url,
            None => {
                warn!(tool = %name, "Skipping tool with no repository URL");
                continue;
            }
        };

        let pinned = entry
            .metadata
            .pinned_ref
            .as_deref()
            .unwrap_or("unknown");

        let clone_dir = tempfile::tempdir()?;
        let name_owned = name.to_string();
        let url_owned = repo_url.clone();
        let dest = clone_dir.path().to_path_buf();

        let head = match tokio::task::spawn_blocking(move || -> Result<String> {
            git::clone_repo(&url_owned, None, &dest)?;
            git::head_commit(&dest)
        })
        .await
        .context("Clone task panicked")?
        {
            Ok(h) => h,
            Err(e) => {
                error!(tool = %name_owned, error = %e, "Failed to check tool");
                continue;
            }
        };

        let short_pinned: String = pinned.chars().take(8).collect();
        let short_head: String = head.chars().take(8).collect();

        if head == pinned {
            info!(tool = %name, commit = %short_pinned, "Up to date");
        } else {
            warn!(
                tool = %name,
                pinned = %short_pinned,
                current = %short_head,
                "Drift detected, run: argus registry update {name}"
            );
        }
    }

    Ok(())
}
