use std::collections::{BTreeSet, VecDeque};
use std::convert::Infallible;
use std::net::SocketAddr;
use std::sync::Arc;

use bytes::Bytes;
use http_body_util::{BodyExt, Full};
use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper::{Request, Response, StatusCode};
use hyper_util::rt::TokioIo;
use serde_json::{json, Value};
use tokio::net::TcpListener;
use tokio::sync::Mutex;

use argus_audit::InMemoryEventStore;
use argus_gateway::{
    GatewayService, LlmFormat, LlmProxy, McpManager, ProxyConfig, UpstreamConfig,
};
use argus_kernel::{AgentId, BackgroundTheoryBuilder, CapKind, ConfLevel, ToolId, ToolMetadata};
use argus_oracle::{MockAuthorizer, MockContentGate};
use argus_sandbox::NoopSandbox;

struct MockLlm {
    responses: Arc<Mutex<VecDeque<(StatusCode, Value)>>>,
    requests: Arc<Mutex<Vec<Value>>>,
}

impl MockLlm {
    fn new(responses: Vec<Value>) -> Self {
        Self {
            responses: Arc::new(Mutex::new(
                responses
                    .into_iter()
                    .map(|v| (StatusCode::OK, v))
                    .collect(),
            )),
            requests: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn with_status(responses: Vec<(StatusCode, Value)>) -> Self {
        Self {
            responses: Arc::new(Mutex::new(VecDeque::from(responses))),
            requests: Arc::new(Mutex::new(Vec::new())),
        }
    }

    async fn start(self) -> (SocketAddr, Arc<Mutex<Vec<Value>>>) {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let responses = self.responses.clone();
        let requests = self.requests.clone();

        tokio::spawn(async move {
            loop {
                let Ok((stream, _)) = listener.accept().await else {
                    break;
                };
                let io = TokioIo::new(stream);
                let responses = responses.clone();
                let requests = requests.clone();
                tokio::spawn(async move {
                    let responses = responses.clone();
                    let requests = requests.clone();
                    let svc = service_fn(move |req: Request<hyper::body::Incoming>| {
                        let responses = responses.clone();
                        let requests = requests.clone();
                        async move {
                            let body = req.into_body().collect().await.unwrap().to_bytes();
                            let body_json: Value =
                                serde_json::from_slice(&body).unwrap_or(json!({}));
                            requests.lock().await.push(body_json);

                            let (status, response) = responses
                                .lock()
                                .await
                                .pop_front()
                                .unwrap_or((StatusCode::OK, json!({"error": "no more responses"})));
                            let bytes = serde_json::to_vec(&response).unwrap();
                            Ok::<_, Infallible>(
                                Response::builder()
                                    .status(status)
                                    .header("content-type", "application/json")
                                    .body(Full::new(Bytes::from(bytes)).boxed())
                                    .unwrap(),
                            )
                        }
                    });
                    let _ = http1::Builder::new().serve_connection(io, svc).await;
                });
            }
        });

        (addr, self.requests)
    }
}

fn openai_text_response(text: &str) -> Value {
    json!({
        "id": "chatcmpl-test",
        "object": "chat.completion",
        "model": "gpt-4",
        "choices": [{
            "index": 0,
            "message": {"role": "assistant", "content": text},
            "finish_reason": "stop"
        }]
    })
}

fn openai_tool_call_response(calls: Vec<(&str, &str, &str)>) -> Value {
    let tool_calls: Vec<Value> = calls
        .iter()
        .map(|(id, name, args)| {
            json!({
                "id": id,
                "type": "function",
                "function": {"name": name, "arguments": args}
            })
        })
        .collect();
    json!({
        "id": "chatcmpl-test",
        "object": "chat.completion",
        "model": "gpt-4",
        "choices": [{
            "index": 0,
            "message": {"role": "assistant", "content": null, "tool_calls": tool_calls},
            "finish_reason": "tool_calls"
        }]
    })
}

fn test_background() -> BackgroundTheoryBuilder {
    let mut b = BackgroundTheoryBuilder::new();
    b.register_tool(
        ToolId::new("read_file"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemRead]),
            egress: BTreeSet::new(),
            conf_floor: ConfLevel::Internal,
            endorsed: false,
        },
    );
    b.register_tool(
        ToolId::new("write_file"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemWrite]),
            egress: BTreeSet::new(),
            conf_floor: ConfLevel::Sensitive,
            endorsed: false,
        },
    );
    b
}

fn allow_gateway() -> GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore> {
    GatewayService::new(
        test_background().build(),
        MockAuthorizer::allow_all(),
        MockContentGate::pass_all(),
        InMemoryEventStore::new(),
    )
}

fn deny_gateway() -> GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore> {
    GatewayService::new(
        test_background().build(),
        MockAuthorizer::new(),
        MockContentGate::pass_all(),
        InMemoryEventStore::new(),
    )
}

async fn setup_agent(
    gateway: &GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore>,
) {
    gateway
        .register_tool(ToolId::new("read_file"))
        .await
        .unwrap();
    gateway
        .register_tool(ToolId::new("write_file"))
        .await
        .unwrap();
    gateway
        .delegate(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();
    gateway
        .grant_capability(AgentId::root(), AgentId::new("worker"), CapKind::FilesystemRead)
        .await
        .unwrap();
    gateway
        .grant_capability(
            AgentId::root(),
            AgentId::new("worker"),
            CapKind::FilesystemWrite,
        )
        .await
        .unwrap();
}

async fn start_proxy_with_format(
    gateway: GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore>,
    mock_addr: SocketAddr,
    format: LlmFormat,
) -> SocketAddr {
    let gateway = Arc::new(gateway);
    let mcp = Arc::new(tokio::sync::RwLock::new(McpManager::new(NoopSandbox)));
    let config = ProxyConfig {
        max_tool_rounds: 3,
        upstreams: vec![UpstreamConfig {
            name: "mock".into(),
            url: format!("http://{mock_addr}"),
            format,
        }],
    };
    let proxy = Arc::new(LlmProxy::new(gateway, mcp, config));
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move { proxy.serve(listener).await });
    addr
}

async fn start_proxy(
    gateway: GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore>,
    mock_addr: SocketAddr,
) -> SocketAddr {
    start_proxy_with_format(gateway, mock_addr, LlmFormat::OpenAi).await
}

fn proxy_client() -> reqwest::Client {
    reqwest::Client::new()
}

#[tokio::test]
async fn happy_path_no_tool_calls() {
    let mock = MockLlm::new(vec![openai_text_response("Hello from the LLM")]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .header("x-argus-agent", "worker")
        .json(&json!({"model": "gpt-4", "messages": [{"role": "user", "content": "Hi"}]}))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 200);
    let body: Value = resp.json().await.unwrap();
    assert_eq!(
        body["choices"][0]["message"]["content"],
        "Hello from the LLM"
    );
}

#[tokio::test]
async fn missing_agent_header_returns_401() {
    let mock = MockLlm::new(vec![openai_text_response("Hi")]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .json(&json!({"model": "gpt-4", "messages": []}))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 401);
}

#[tokio::test]
async fn unknown_agent_returns_401() {
    let mock = MockLlm::new(vec![openai_text_response("Hi")]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .header("x-argus-agent", "ghost")
        .json(&json!({"model": "gpt-4", "messages": []}))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 401);
}

#[tokio::test]
async fn unsupported_path_returns_404() {
    let mock = MockLlm::new(vec![]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v2/unknown"))
        .header("x-argus-agent", "worker")
        .json(&json!({"model": "gpt-4"}))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 404);
}

#[tokio::test]
async fn upstream_error_returns_502() {
    let mock = MockLlm::with_status(vec![(
        StatusCode::INTERNAL_SERVER_ERROR,
        json!({"error": "boom"}),
    )]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .header("x-argus-agent", "worker")
        .json(&json!({"model": "gpt-4", "messages": [{"role": "user", "content": "Hi"}]}))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 502);
}

#[tokio::test]
async fn tool_call_authorized_mcp_fails_then_text() {
    let mock = MockLlm::new(vec![
        openai_tool_call_response(vec![("call_1", "read_file", "{\"path\":\"/tmp\"}")]),
        openai_text_response("I could not read the file"),
    ]);
    let (mock_addr, requests) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .header("x-argus-agent", "worker")
        .json(&json!({
            "model": "gpt-4",
            "messages": [{"role": "user", "content": "Read /tmp"}]
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 200);
    let body: Value = resp.json().await.unwrap();
    assert_eq!(
        body["choices"][0]["message"]["content"],
        "I could not read the file"
    );

    let reqs = requests.lock().await;
    assert_eq!(reqs.len(), 2);
    let second_messages = reqs[1]["messages"].as_array().unwrap();
    assert!(second_messages.iter().any(|m| m["role"] == "tool"));
}

#[tokio::test]
async fn tool_call_denied() {
    let mock = MockLlm::new(vec![
        openai_tool_call_response(vec![("call_1", "read_file", "{}")]),
        openai_text_response("I was denied access"),
    ]);
    let (mock_addr, requests) = mock.start().await;

    let gw = deny_gateway();
    gw.register_tool(ToolId::new("read_file")).await.unwrap();
    gw.register_tool(ToolId::new("write_file")).await.unwrap();
    gw.delegate(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();
    gw.grant_capability(AgentId::root(), AgentId::new("worker"), CapKind::FilesystemRead)
        .await
        .unwrap();

    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .header("x-argus-agent", "worker")
        .json(&json!({
            "model": "gpt-4",
            "messages": [{"role": "user", "content": "Read file"}]
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 200);
    let body: Value = resp.json().await.unwrap();
    assert_eq!(
        body["choices"][0]["message"]["content"],
        "I was denied access"
    );

    let reqs = requests.lock().await;
    assert_eq!(reqs.len(), 2);
    let tool_msg = reqs[1]["messages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["role"] == "tool")
        .unwrap();
    assert!(
        tool_msg["content"]
            .as_str()
            .unwrap()
            .contains("Authorization denied")
    );
}

#[tokio::test]
async fn streaming_returns_sse_content_type() {
    let mock = MockLlm::new(vec![openai_text_response("Streamed response")]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .header("x-argus-agent", "worker")
        .json(&json!({
            "model": "gpt-4",
            "stream": true,
            "messages": [{"role": "user", "content": "Hi"}]
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 200);
    let ct = resp.headers().get("content-type").unwrap().to_str().unwrap();
    assert_eq!(ct, "text/event-stream");

    let body = resp.text().await.unwrap();
    assert!(body.contains("data:"));
    assert!(body.contains("[DONE]"));
}

fn anthropic_text_response(text: &str) -> Value {
    json!({
        "id": "msg_test",
        "type": "message",
        "role": "assistant",
        "model": "claude-sonnet-4-20250514",
        "content": [{"type": "text", "text": text}],
        "stop_reason": "end_turn",
        "usage": {"input_tokens": 10, "output_tokens": 5}
    })
}

fn anthropic_tool_call_response(calls: Vec<(&str, &str, Value)>) -> Value {
    let content: Vec<Value> = calls
        .into_iter()
        .map(|(id, name, input)| {
            json!({
                "type": "tool_use",
                "id": id,
                "name": name,
                "input": input,
            })
        })
        .collect();
    json!({
        "id": "msg_test",
        "type": "message",
        "role": "assistant",
        "model": "claude-sonnet-4-20250514",
        "content": content,
        "stop_reason": "tool_use",
        "usage": {"input_tokens": 10, "output_tokens": 20}
    })
}

async fn start_proxy_anthropic(
    gateway: GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore>,
    mock_addr: SocketAddr,
) -> SocketAddr {
    start_proxy_with_format(gateway, mock_addr, LlmFormat::Anthropic).await
}

#[tokio::test]
async fn anthropic_happy_path_no_tool_calls() {
    let mock = MockLlm::new(vec![anthropic_text_response("Hello from Claude")]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy_anthropic(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/messages"))
        .header("x-argus-agent", "worker")
        .json(&json!({
            "model": "claude-sonnet-4-20250514",
            "max_tokens": 1024,
            "messages": [{"role": "user", "content": "Hi"}]
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 200);
    let body: Value = resp.json().await.unwrap();
    assert_eq!(body["content"][0]["text"], "Hello from Claude");
}

#[tokio::test]
async fn anthropic_tool_call_then_text() {
    let mock = MockLlm::new(vec![
        anthropic_tool_call_response(vec![("toolu_1", "read_file", json!({"path": "/tmp"}))]),
        anthropic_text_response("I could not read the file"),
    ]);
    let (mock_addr, requests) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy_anthropic(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/messages"))
        .header("x-argus-agent", "worker")
        .json(&json!({
            "model": "claude-sonnet-4-20250514",
            "max_tokens": 1024,
            "messages": [{"role": "user", "content": "Read /tmp"}]
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 200);
    let body: Value = resp.json().await.unwrap();
    assert_eq!(body["content"][0]["text"], "I could not read the file");

    let reqs = requests.lock().await;
    assert_eq!(reqs.len(), 2);
    let second_messages = reqs[1]["messages"].as_array().unwrap();
    assert!(second_messages.iter().any(|m| {
        m["role"] == "user"
            && m["content"]
                .as_array()
                .map(|c| c.iter().any(|b| b["type"] == "tool_result"))
                .unwrap_or(false)
    }));
}

#[tokio::test]
async fn max_rounds_exceeded() {
    let mock = MockLlm::new(vec![
        openai_tool_call_response(vec![("call_1", "read_file", "{}")]),
        openai_tool_call_response(vec![("call_2", "read_file", "{}")]),
        openai_tool_call_response(vec![("call_3", "read_file", "{}")]),
        openai_tool_call_response(vec![("call_4", "read_file", "{}")]),
    ]);
    let (mock_addr, _) = mock.start().await;

    let gw = allow_gateway();
    setup_agent(&gw).await;
    let proxy_addr = start_proxy(gw, mock_addr).await;

    let resp = proxy_client()
        .post(format!("http://{proxy_addr}/v1/chat/completions"))
        .header("x-argus-agent", "worker")
        .json(&json!({
            "model": "gpt-4",
            "messages": [{"role": "user", "content": "loop forever"}]
        }))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 500);
    let body: Value = resp.json().await.unwrap();
    let msg = body["error"]["message"].as_str().unwrap();
    assert!(msg.contains("max tool rounds"));
}
