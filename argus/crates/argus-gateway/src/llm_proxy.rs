use std::convert::Infallible;
use std::sync::Arc;

use bytes::Bytes;
use futures::future::join_all;
use http_body_util::{BodyExt, Full, StreamBody};
use hyper::body::Frame;
use hyper::header::{HeaderMap, HeaderValue};
use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper::{Request, Response, StatusCode};
use hyper_util::rt::TokioIo;
use serde_json::{json, Value};
use tokio::net::TcpListener;
use tokio::sync::mpsc;
use tokio_stream::wrappers::ReceiverStream;
use uuid::Uuid;

use argus_kernel::{AgentId, AuthorizerOracle, ContentGateOracle, EventStore, InvocationId, ToolId};
use argus_sandbox::SandboxProvider;

use crate::error::ProxyError;
use crate::llm_codec::{codec_for_path, LlmCodec};
use crate::llm_types::{LlmFormat, ProxyConfig, SseProgressEvent, ToolResult, UpstreamConfig};
use crate::mcp_manager::McpManager;
use crate::service::GatewayService;

type BoxBody = http_body_util::combinators::BoxBody<Bytes, Infallible>;

pub struct LlmProxy<A, C, E, S>
where
    A: AuthorizerOracle,
    C: ContentGateOracle,
    E: EventStore,
    S: SandboxProvider,
{
    gateway: Arc<GatewayService<A, C, E>>,
    mcp: Arc<tokio::sync::RwLock<McpManager<S>>>,
    config: ProxyConfig,
    http_client: reqwest::Client,
}

impl<A, C, E, S> LlmProxy<A, C, E, S>
where
    A: AuthorizerOracle + Send + Sync + 'static,
    C: ContentGateOracle + Send + Sync + 'static,
    E: EventStore + Send + Sync + 'static,
    S: SandboxProvider + Send + Sync + 'static,
{
    pub fn new(
        gateway: Arc<GatewayService<A, C, E>>,
        mcp: Arc<tokio::sync::RwLock<McpManager<S>>>,
        config: ProxyConfig,
    ) -> Self {
        Self {
            gateway,
            mcp,
            config,
            http_client: reqwest::Client::new(),
        }
    }

    pub async fn serve(self: Arc<Self>, listener: TcpListener) {
        let addr = listener.local_addr().unwrap();
        tracing::info!("LLM proxy listening on {addr}");
        loop {
            let Ok((stream, _)) = listener.accept().await else {
                continue;
            };
            let io = TokioIo::new(stream);
            let proxy = self.clone();
            tokio::spawn(async move {
                let service = service_fn(move |req| {
                    let proxy = proxy.clone();
                    async move { Ok::<_, Infallible>(proxy.handle_request(req).await) }
                });
                if let Err(e) = http1::Builder::new()
                    .serve_connection(io, service)
                    .await
                {
                    tracing::error!("HTTP connection error: {e}");
                }
            });
        }
    }

    async fn handle_request(
        self: Arc<Self>,
        req: Request<hyper::body::Incoming>,
    ) -> Response<BoxBody> {
        let path = req.uri().path().to_owned();
        let headers = req.headers().clone();

        let body_bytes = match req.into_body().collect().await {
            Ok(collected) => collected.to_bytes(),
            Err(e) => {
                return error_response(StatusCode::BAD_REQUEST, &format!("failed to read body: {e}"))
            }
        };
        let body: Value = match serde_json::from_slice(&body_bytes) {
            Ok(v) => v,
            Err(e) => {
                return error_response(StatusCode::BAD_REQUEST, &format!("invalid JSON: {e}"))
            }
        };

        match self.handle_proxy_request(&path, &headers, body).await {
            Ok(resp) => resp,
            Err(e) => proxy_error_to_response(&e),
        }
    }

    async fn handle_proxy_request(
        self: &Arc<Self>,
        path: &str,
        headers: &HeaderMap<HeaderValue>,
        body: Value,
    ) -> Result<Response<BoxBody>, ProxyError> {
        let (codec, format) =
            codec_for_path(path).ok_or_else(|| ProxyError::UnsupportedPath(path.to_owned()))?;

        let agent_str = headers
            .get("x-argus-agent")
            .and_then(|v| v.to_str().ok())
            .ok_or(ProxyError::MissingAgentHeader)?;
        let agent = AgentId::new(agent_str);

        let state = self.gateway.state_snapshot().await;
        if !state.agent_active.contains(&agent) {
            return Err(ProxyError::AgentNotFound(agent_str.to_owned()));
        }

        let upstream = self
            .resolve_upstream(headers, format)
            .ok_or(ProxyError::NoUpstream)?;

        let mut forward_headers = HeaderMap::new();
        for (name, value) in headers.iter() {
            let n = name.as_str();
            if !n.starts_with("x-argus-") && n != "host" && n != "content-length" {
                forward_headers.insert(name.clone(), value.clone());
            }
        }

        if codec.is_streaming_request(&body) {
            return self.handle_streaming(agent, codec, &upstream, forward_headers, body, path);
        }

        let result = self
            .run_tool_loop(&agent, &*codec, &upstream, &forward_headers, body, path, None)
            .await?;
        Ok(json_response(StatusCode::OK, &result))
    }

    fn handle_streaming(
        self: &Arc<Self>,
        agent: AgentId,
        codec: Box<dyn LlmCodec>,
        upstream: &UpstreamConfig,
        forward_headers: HeaderMap<HeaderValue>,
        body: Value,
        path: &str,
    ) -> Result<Response<BoxBody>, ProxyError> {
        let (tx, rx) = mpsc::channel::<Result<Frame<Bytes>, Infallible>>(32);
        let stream = ReceiverStream::new(rx);
        let body_stream = StreamBody::new(stream);
        let response = Response::builder()
            .status(200)
            .header("content-type", "text/event-stream")
            .header("cache-control", "no-cache")
            .body(body_stream.boxed())
            .unwrap();

        let proxy = self.clone();
        let upstream = upstream.clone();
        let path = path.to_owned();
        tokio::spawn(async move {
            let result = proxy
                .run_tool_loop(
                    &agent,
                    &*codec,
                    &upstream,
                    &forward_headers,
                    body,
                    &path,
                    Some(&tx),
                )
                .await;
            match result {
                Ok(final_response) => {
                    for chunk in codec.response_to_sse(&final_response) {
                        let _ = tx.send(Ok(Frame::data(Bytes::from(chunk)))).await;
                    }
                }
                Err(e) => {
                    let event = SseProgressEvent::Error {
                        message: e.to_string(),
                    };
                    let _ = tx
                        .send(Ok(Frame::data(Bytes::from(event.to_sse_string()))))
                        .await;
                }
            }
        });

        Ok(response)
    }

    #[allow(clippy::too_many_arguments)]
    async fn run_tool_loop(
        &self,
        agent: &AgentId,
        codec: &dyn LlmCodec,
        upstream: &UpstreamConfig,
        forward_headers: &HeaderMap<HeaderValue>,
        mut request_body: Value,
        path: &str,
        sse_tx: Option<&mpsc::Sender<Result<Frame<Bytes>, Infallible>>>,
    ) -> Result<Value, ProxyError> {
        for round in 1..=self.config.max_tool_rounds {
            request_body["stream"] = Value::Bool(false);

            let url = format!("{}{}", upstream.url.trim_end_matches('/'), path);
            let resp = self
                .http_client
                .post(&url)
                .headers(forward_headers.clone())
                .json(&request_body)
                .send()
                .await?;

            let status = resp.status();
            if !status.is_success() {
                let body = resp.text().await.unwrap_or_default();
                return Err(ProxyError::UpstreamStatus {
                    status: status.as_u16(),
                    body,
                });
            }

            let response_body: Value = resp.json().await?;
            let tool_calls = codec.extract_tool_calls(&response_body);

            if tool_calls.is_empty() {
                return Ok(response_body);
            }

            let tool_results = self
                .execute_tool_calls(agent, &tool_calls, round, sse_tx)
                .await;

            let denied = tool_results.iter().filter(|r| r.is_error).count();
            emit_sse(
                sse_tx,
                &SseProgressEvent::RoundComplete {
                    round,
                    tool_calls: tool_calls.len(),
                    denied,
                    next: "llm_call".into(),
                },
            )
            .await;

            request_body =
                codec.build_tool_results_request(&request_body, &response_body, &tool_results);
        }

        Err(ProxyError::MaxRoundsExceeded(self.config.max_tool_rounds))
    }

    async fn execute_tool_calls(
        &self,
        agent: &AgentId,
        tool_calls: &[crate::llm_types::ToolCall],
        round: usize,
        sse_tx: Option<&mpsc::Sender<Result<Frame<Bytes>, Infallible>>>,
    ) -> Vec<ToolResult> {
        let futures: Vec<_> = tool_calls
            .iter()
            .map(|tc| self.execute_single_tool(agent, tc, round, sse_tx))
            .collect();
        join_all(futures).await
    }

    async fn execute_single_tool(
        &self,
        agent: &AgentId,
        tc: &crate::llm_types::ToolCall,
        round: usize,
        sse_tx: Option<&mpsc::Sender<Result<Frame<Bytes>, Infallible>>>,
    ) -> ToolResult {
        let inv_id = Uuid::new_v4().to_string();
        let inv = InvocationId::new(&inv_id);
        let tool_id = ToolId::new(&tc.name);

        emit_sse(
            sse_tx,
            &SseProgressEvent::ToolStart {
                tool: tc.name.clone(),
                invocation: inv_id.clone(),
                round,
            },
        )
        .await;

        if let Err(e) = self
            .gateway
            .invoke_start(agent.clone(), tool_id, inv.clone())
            .await
        {
            emit_sse(
                sse_tx,
                &SseProgressEvent::ToolDenied {
                    tool: tc.name.clone(),
                    invocation: inv_id,
                    reason: e.to_string(),
                    round,
                },
            )
            .await;
            return ToolResult {
                tool_call_id: tc.id.clone(),
                content: format!("Authorization denied: {e}"),
                is_error: true,
            };
        }

        let args: Value = serde_json::from_str(&tc.arguments).unwrap_or(json!({}));
        let mcp_result = {
            let mcp = self.mcp.read().await;
            mcp.call_tool(&tc.name, args).await
        };

        if let Err(e) = self.gateway.invoke_complete(agent.clone(), inv).await {
            tracing::warn!(tool = %tc.name, error = %e, "invoke_complete failed");
        }

        let (content, is_error, status) = match mcp_result {
            Ok(result) => (result, false, "ok"),
            Err(e) => (format!("Tool execution failed: {e}"), true, "error"),
        };

        emit_sse(
            sse_tx,
            &SseProgressEvent::ToolResult {
                tool: tc.name.clone(),
                invocation: inv_id,
                status: status.into(),
                round,
            },
        )
        .await;

        ToolResult {
            tool_call_id: tc.id.clone(),
            content,
            is_error,
        }
    }

    fn resolve_upstream(
        &self,
        headers: &HeaderMap<HeaderValue>,
        format: LlmFormat,
    ) -> Option<UpstreamConfig> {
        if let Some(name) = headers.get("x-argus-upstream").and_then(|v| v.to_str().ok()) {
            return self.config.upstreams.iter().find(|u| u.name == name).cloned();
        }
        self.config
            .upstreams
            .iter()
            .find(|u| u.format == format)
            .cloned()
    }
}

async fn emit_sse(
    tx: Option<&mpsc::Sender<Result<Frame<Bytes>, Infallible>>>,
    event: &SseProgressEvent,
) {
    if let Some(tx) = tx {
        let _ = tx
            .send(Ok(Frame::data(Bytes::from(event.to_sse_string()))))
            .await;
    }
}

fn json_response(status: StatusCode, body: &Value) -> Response<BoxBody> {
    let bytes = serde_json::to_vec(body).unwrap_or_default();
    Response::builder()
        .status(status)
        .header("content-type", "application/json")
        .body(Full::new(Bytes::from(bytes)).boxed())
        .unwrap()
}

fn error_response(status: StatusCode, message: &str) -> Response<BoxBody> {
    json_response(status, &json!({"error": {"message": message}}))
}

pub fn proxy_error_to_response(err: &ProxyError) -> Response<BoxBody> {
    let status = match err {
        ProxyError::MissingAgentHeader | ProxyError::AgentNotFound(_) => StatusCode::UNAUTHORIZED,
        ProxyError::UnsupportedPath(_) => StatusCode::NOT_FOUND,
        ProxyError::NoUpstream | ProxyError::InvalidBody(_) | ProxyError::Json(_) => {
            StatusCode::BAD_REQUEST
        }
        ProxyError::UpstreamRequest(_) | ProxyError::UpstreamStatus { .. } => {
            StatusCode::BAD_GATEWAY
        }
        ProxyError::Gateway(_) => StatusCode::FORBIDDEN,
        ProxyError::MaxRoundsExceeded(_) => StatusCode::INTERNAL_SERVER_ERROR,
    };
    error_response(status, &err.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proxy_error_missing_agent_is_401() {
        let resp = proxy_error_to_response(&ProxyError::MissingAgentHeader);
        assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    }

    #[test]
    fn proxy_error_unsupported_path_is_404() {
        let resp = proxy_error_to_response(&ProxyError::UnsupportedPath("/v2/foo".into()));
        assert_eq!(resp.status(), StatusCode::NOT_FOUND);
    }

    #[test]
    fn proxy_error_upstream_status_is_502() {
        let resp = proxy_error_to_response(&ProxyError::UpstreamStatus {
            status: 500,
            body: "internal".into(),
        });
        assert_eq!(resp.status(), StatusCode::BAD_GATEWAY);
    }

    #[test]
    fn proxy_error_max_rounds_is_500() {
        let resp = proxy_error_to_response(&ProxyError::MaxRoundsExceeded(15));
        assert_eq!(resp.status(), StatusCode::INTERNAL_SERVER_ERROR);
    }
}
