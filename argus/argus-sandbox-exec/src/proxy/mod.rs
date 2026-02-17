mod http_connect;

use std::path::PathBuf;
use std::sync::Arc;

use tokio::net::UnixListener;

pub struct ProxyServer {
    domains: Arc<Vec<String>>,
    http_socket_path: PathBuf,
    shutdown_tx: Option<tokio::sync::watch::Sender<bool>>,
}

impl ProxyServer {
    pub fn new(domains: Vec<String>) -> Self {
        let pid = std::process::id();
        Self {
            domains: Arc::new(domains),
            http_socket_path: PathBuf::from(format!("/tmp/argus-proxy-{pid}-http.sock")),
            shutdown_tx: None,
        }
    }

    pub fn http_socket_path(&self) -> &PathBuf {
        &self.http_socket_path
    }

    pub async fn start(&mut self) -> Result<(), String> {
        let _ = std::fs::remove_file(&self.http_socket_path);

        let http_listener = UnixListener::bind(&self.http_socket_path)
            .map_err(|e| format!("bind HTTP proxy socket: {e}"))?;

        let (shutdown_tx, shutdown_rx) = tokio::sync::watch::channel(false);
        self.shutdown_tx = Some(shutdown_tx);

        let domains = self.domains.clone();
        tokio::spawn(async move {
            http_connect::serve(http_listener, domains, shutdown_rx).await;
        });

        Ok(())
    }

    pub fn shutdown(&mut self) {
        if let Some(tx) = self.shutdown_tx.take() {
            let _ = tx.send(true);
        }
        let _ = std::fs::remove_file(&self.http_socket_path);
    }
}

impl Drop for ProxyServer {
    fn drop(&mut self) {
        self.shutdown();
    }
}
