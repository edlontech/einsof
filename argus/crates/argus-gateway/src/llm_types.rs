use serde::Serialize;

#[derive(Debug, Clone)]
pub struct ToolCall {
    pub id: String,
    pub name: String,
    pub arguments: String,
}

#[derive(Debug, Clone)]
pub struct ToolResult {
    pub tool_call_id: String,
    pub content: String,
    pub is_error: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LlmFormat {
    OpenAi,
    Anthropic,
}

#[derive(Debug, Clone)]
pub struct UpstreamConfig {
    pub name: String,
    pub url: String,
    pub format: LlmFormat,
}

#[derive(Debug, Clone)]
pub struct ProxyConfig {
    pub max_tool_rounds: usize,
    pub upstreams: Vec<UpstreamConfig>,
}

impl Default for ProxyConfig {
    fn default() -> Self {
        Self {
            max_tool_rounds: 15,
            upstreams: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum SseProgressEvent {
    ToolStart {
        tool: String,
        invocation: String,
        round: usize,
    },
    ToolDenied {
        tool: String,
        invocation: String,
        reason: String,
        round: usize,
    },
    ToolResult {
        tool: String,
        invocation: String,
        status: String,
        round: usize,
    },
    RoundComplete {
        round: usize,
        tool_calls: usize,
        denied: usize,
        next: String,
    },
    Error {
        message: String,
    },
}

impl SseProgressEvent {
    pub fn event_name(&self) -> &'static str {
        match self {
            Self::ToolStart { .. } => "argus.tool_start",
            Self::ToolDenied { .. } => "argus.tool_denied",
            Self::ToolResult { .. } => "argus.tool_result",
            Self::RoundComplete { .. } => "argus.round_complete",
            Self::Error { .. } => "argus.error",
        }
    }

    pub fn to_sse_string(&self) -> String {
        let data = serde_json::to_string(self).unwrap_or_default();
        format!("event: {}\ndata: {data}\n\n", self.event_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sse_tool_start_format() {
        let event = SseProgressEvent::ToolStart {
            tool: "read_file".into(),
            invocation: "inv_1".into(),
            round: 1,
        };
        let sse = event.to_sse_string();
        assert!(sse.starts_with("event: argus.tool_start\n"));
        assert!(sse.contains("\"tool\":\"read_file\""));
        assert!(sse.ends_with("\n\n"));
    }

    #[test]
    fn sse_error_format() {
        let event = SseProgressEvent::Error {
            message: "connection lost".into(),
        };
        let sse = event.to_sse_string();
        assert!(sse.starts_with("event: argus.error\n"));
        assert!(sse.contains("\"message\":\"connection lost\""));
    }

    #[test]
    fn proxy_config_defaults() {
        let config = ProxyConfig::default();
        assert_eq!(config.max_tool_rounds, 15);
        assert!(config.upstreams.is_empty());
    }
}
