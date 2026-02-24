use std::num::NonZeroU32;
use std::path::Path;

use anyhow::{Context, Result};
use gix::remote::fetch::Shallow;

pub fn clone_repo(url: &str, git_ref: Option<&str>, dest: &Path) -> Result<()> {
    let mut prepare = gix::prepare_clone(url, dest)
        .context("Failed to prepare clone")?
        .with_shallow(Shallow::DepthAtRemote(
            NonZeroU32::new(1).expect("1 is non-zero"),
        ));

    if let Some(r) = git_ref {
        prepare = prepare.with_ref_name(Some(r))?;
    }

    let (mut checkout, _outcome) = prepare
        .fetch_then_checkout(gix::progress::Discard, &gix::interrupt::IS_INTERRUPTED)
        .context("Failed to fetch repository")?;

    checkout
        .main_worktree(gix::progress::Discard, &gix::interrupt::IS_INTERRUPTED)
        .context("Failed to checkout worktree")?;

    Ok(())
}

pub fn head_commit(repo_path: &Path) -> Result<String> {
    let repo = gix::open(repo_path).context("Failed to open repository")?;
    let id = repo.head_id().context("Failed to resolve HEAD")?;
    Ok(id.to_string())
}

pub fn resolve_argus_home() -> std::path::PathBuf {
    if let Ok(home) = std::env::var("ARGUS_HOME") {
        return std::path::PathBuf::from(home);
    }
    if let Ok(home) = std::env::var("HOME") {
        return std::path::PathBuf::from(home).join(".argus");
    }
    std::path::PathBuf::from(".argus")
}
