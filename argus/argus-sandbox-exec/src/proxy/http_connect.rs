use std::sync::Arc;

use hyper::body::Incoming;
use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper::{Method, Request, Response};
use hyper_util::rt::TokioIo;
use tokio::io;
use tokio::net::{TcpStream, UnixListener};

use argus_sandbox::domain_matches_any;

pub async fn serve(
    listener: UnixListener,
    domains: Arc<Vec<String>>,
    mut shutdown_rx: tokio::sync::watch::Receiver<bool>,
) {
    loop {
        tokio::select! {
            accept = listener.accept() => {
                match accept {
                    Ok((stream, _)) => {
                        let domains = domains.clone();
                        tokio::spawn(async move {
                            let io = TokioIo::new(stream);
                            let svc = service_fn(move |req| {
                                let domains = domains.clone();
                                async move { handle_request(req, &domains).await }
                            });
                            if let Err(e) = http1::Builder::new()
                                .preserve_header_case(true)
                                .serve_connection(io, svc)
                                .with_upgrades()
                                .await
                            {
                                eprintln!("argus-proxy: connection error: {e}");
                            }
                        });
                    }
                    Err(e) => {
                        eprintln!("argus-proxy: accept error: {e}");
                    }
                }
            }
            _ = shutdown_rx.changed() => {
                if *shutdown_rx.borrow() {
                    break;
                }
            }
        }
    }
}

async fn handle_request(
    req: Request<Incoming>,
    domains: &[String],
) -> Result<Response<http_body_util::Empty<hyper::body::Bytes>>, hyper::Error> {
    if req.method() == Method::CONNECT {
        let authority = req.uri().authority().map(|a| a.to_string());
        if let Some(ref authority) = authority {
            let (host, port) = parse_authority(authority);
            if domain_matches_any(domains, &host) {
                tokio::spawn(async move {
                    match hyper::upgrade::on(req).await {
                        Ok(upgraded) => {
                            let target = format!("{host}:{port}");
                            if let Err(e) = tunnel(upgraded, &target).await {
                                eprintln!("argus-proxy: tunnel to {target} failed: {e}");
                            }
                        }
                        Err(e) => {
                            eprintln!("argus-proxy: upgrade failed: {e}");
                        }
                    }
                });

                Ok(Response::new(http_body_util::Empty::new()))
            } else {
                eprintln!("argus-proxy: blocked connection to {authority}");
                let mut resp = Response::new(http_body_util::Empty::new());
                *resp.status_mut() = hyper::StatusCode::FORBIDDEN;
                Ok(resp)
            }
        } else {
            let mut resp = Response::new(http_body_util::Empty::new());
            *resp.status_mut() = hyper::StatusCode::BAD_REQUEST;
            Ok(resp)
        }
    } else {
        let mut resp = Response::new(http_body_util::Empty::new());
        *resp.status_mut() = hyper::StatusCode::METHOD_NOT_ALLOWED;
        Ok(resp)
    }
}

fn parse_authority(authority: &str) -> (String, u16) {
    if let Some(colon_pos) = authority.rfind(':') {
        let host = &authority[..colon_pos];
        let port = authority[colon_pos + 1..]
            .parse()
            .unwrap_or(443);
        (host.to_string(), port)
    } else {
        (authority.to_string(), 443)
    }
}

async fn tunnel(
    upgraded: hyper::upgrade::Upgraded,
    target: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut upstream = TcpStream::connect(target).await?;
    let mut client = TokioIo::new(upgraded);

    let (_, _) = io::copy_bidirectional(&mut client, &mut upstream).await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_authority_with_port() {
        let (host, port) = parse_authority("api.github.com:443");
        assert_eq!(host, "api.github.com");
        assert_eq!(port, 443);
    }

    #[test]
    fn parse_authority_without_port() {
        let (host, port) = parse_authority("api.github.com");
        assert_eq!(host, "api.github.com");
        assert_eq!(port, 443);
    }

    #[test]
    fn parse_authority_with_custom_port() {
        let (host, port) = parse_authority("example.com:8080");
        assert_eq!(host, "example.com");
        assert_eq!(port, 8080);
    }
}
