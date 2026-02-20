use crate::llm_types::{LlmFormat, ToolCall, ToolResult};

pub trait LlmCodec: Send + Sync {
    fn extract_tool_calls(&self, response: &serde_json::Value) -> Vec<ToolCall>;

    fn build_tool_results_request(
        &self,
        current_request: &serde_json::Value,
        assistant_response: &serde_json::Value,
        tool_results: &[ToolResult],
    ) -> serde_json::Value;

    fn response_to_sse(&self, response: &serde_json::Value) -> Vec<String>;

    fn is_streaming_request(&self, request: &serde_json::Value) -> bool;
}

pub fn codec_for_path(path: &str) -> Option<(Box<dyn LlmCodec>, LlmFormat)> {
    use crate::llm_anthropic::AnthropicCodec;
    use crate::llm_openai::OpenAiCodec;

    if path.starts_with("/v1/chat/completions") {
        Some((Box::new(OpenAiCodec), LlmFormat::OpenAi))
    } else if path.starts_with("/v1/messages") {
        Some((Box::new(AnthropicCodec), LlmFormat::Anthropic))
    } else {
        None
    }
}
