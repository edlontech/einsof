mod config;
mod git;
mod registry_add;
mod registry_check;
mod registry_update;
mod serve;

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "argus", about = "Tool Authorization Gateway for LLM APIs")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Serve {
        #[arg(long, default_value = "argus.toml")]
        config: String,
    },
    Analyze {
        path: String,
    },
    #[command(subcommand)]
    Registry(RegistryCommands),
    #[command(subcommand)]
    Audit(AuditCommands),
}

#[derive(Subcommand)]
enum RegistryCommands {
    List,
    /// Analyze a tool repository and add it to the local registry
    Add {
        /// Repository URL to analyze
        url: String,
        /// Pin to a specific git ref (tag, branch, commit)
        #[arg(long)]
        git_ref: Option<String>,
        /// Enable drift tracking for this tool
        #[arg(long)]
        track: bool,
        /// Run analysis without writing files
        #[arg(long)]
        dry_run: bool,
        /// Only produce the analysis report, no TOML entry
        #[arg(long)]
        report_only: bool,
        /// LLM provider (openrouter, ollama, openai, anthropic, gemini)
        #[arg(long, default_value = "openrouter")]
        provider: String,
        /// Model name for the LLM provider
        #[arg(long, default_value = "anthropic/claude-sonnet-4")]
        model: String,
        /// Maximum LLM agent turns
        #[arg(long, default_value = "15")]
        max_turns: usize,
        /// Maximum tokens per LLM response
        #[arg(long, default_value = "16384")]
        max_tokens: u64,
    },
    /// Re-analyze a registered tool and update its registry entry (fetches latest HEAD)
    Update {
        /// Name of the registered tool to update
        name: String,
        /// LLM provider (openrouter, ollama, openai, anthropic, gemini)
        #[arg(long, default_value = "openrouter")]
        provider: String,
        /// Model name for the LLM provider
        #[arg(long, default_value = "anthropic/claude-sonnet-4")]
        model: String,
        /// Maximum LLM agent turns
        #[arg(long, default_value = "15")]
        max_turns: usize,
        /// Maximum tokens per LLM response
        #[arg(long, default_value = "16384")]
        max_tokens: u64,
    },
    /// Check tracked tools for upstream drift (compares HEAD vs pinned ref)
    Check,
    Sync,
}

#[derive(Subcommand)]
enum AuditCommands {
    Query {
        #[arg(long)]
        agent: Option<String>,
        #[arg(long)]
        action: Option<String>,
        #[arg(long)]
        since: Option<String>,
    },
    Replay {
        #[arg(long)]
        from: Option<u64>,
    },
}

fn build_provider_config(provider: &str, model: &str) -> anyhow::Result<argus_config::ExtractionProviderConfig> {
    use argus_config::ExtractionProviderConfig;
    match provider {
        "openrouter" => Ok(ExtractionProviderConfig::OpenRouter {
            model: model.to_string(),
            api_key_env: "OPENROUTER_API_KEY".to_string(),
            timeout_ms: 30000,
        }),
        "ollama" => Ok(ExtractionProviderConfig::Ollama {
            model: model.to_string(),
            base_url: std::env::var("OLLAMA_BASE_URL")
                .unwrap_or_else(|_| "http://localhost:11434".to_string()),
            timeout_ms: 30000,
        }),
        "openai" => Ok(ExtractionProviderConfig::OpenAI {
            model: model.to_string(),
            api_key_env: "OPENAI_API_KEY".to_string(),
            timeout_ms: 30000,
        }),
        "anthropic" => Ok(ExtractionProviderConfig::Anthropic {
            model: model.to_string(),
            api_key_env: "ANTHROPIC_API_KEY".to_string(),
            timeout_ms: 30000,
        }),
        "gemini" => Ok(ExtractionProviderConfig::Gemini {
            model: model.to_string(),
            api_key_env: "GEMINI_API_KEY".to_string(),
            timeout_ms: 30000,
        }),
        other => anyhow::bail!("Unknown provider: {other}. Use: openrouter, ollama, openai, anthropic, gemini"),
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Serve { config } => return serve::run_serve(&config).await,
        Commands::Analyze { .. } => println!("argus analyze: not yet implemented"),
        Commands::Registry(RegistryCommands::List) => {
            println!("argus registry list: not yet implemented")
        }
        Commands::Registry(RegistryCommands::Add {
            url,
            git_ref,
            track,
            dry_run,
            report_only,
            provider,
            model,
            max_turns,
            max_tokens,
        }) => {
            let _ = tracing_subscriber::fmt::try_init();
            let provider_config = build_provider_config(&provider, &model)?;
            registry_add::run_registry_add(registry_add::RegistryAddOptions {
                url,
                git_ref,
                track,
                dry_run,
                report_only,
                argus_home: git::resolve_argus_home(),
                provider: provider_config,
                max_turns,
                max_tokens,
            })
            .await?;
        }
        Commands::Registry(RegistryCommands::Update {
            name,
            provider,
            model,
            max_turns,
            max_tokens,
        }) => {
            let _ = tracing_subscriber::fmt::try_init();
            let provider_config = build_provider_config(&provider, &model)?;
            registry_update::run_registry_update(registry_update::RegistryUpdateOptions {
                name,
                argus_home: git::resolve_argus_home(),
                provider: provider_config,
                max_turns,
                max_tokens,
            })
            .await?;
        }
        Commands::Registry(RegistryCommands::Check) => {
            let _ = tracing_subscriber::fmt::try_init();
            registry_check::run_registry_check(git::resolve_argus_home()).await?;
        }
        Commands::Registry(RegistryCommands::Sync) => {
            println!("argus registry sync: not yet implemented")
        }
        Commands::Audit(AuditCommands::Query { .. }) => {
            println!("argus audit query: not yet implemented")
        }
        Commands::Audit(AuditCommands::Replay { .. }) => {
            println!("argus audit replay: not yet implemented")
        }
    }
    Ok(())
}
