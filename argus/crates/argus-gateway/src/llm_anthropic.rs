use crate::llm_codec::LlmCodec;
use crate::llm_types::{ToolCall, ToolResult};
use serde_json::{json, Value};

pub struct AnthropicCodec;

impl LlmCodec for AnthropicCodec {
    fn extract_tool_calls(&self, response: &Value) -> Vec<ToolCall> {
        let Some(content) = response.get("content").and_then(|c| c.as_array()) else {
            return Vec::new();
        };
        content
            .iter()
            .filter_map(|block| {
                if block.get("type")?.as_str()? != "tool_use" {
                    return None;
                }
                let id = block.get("id")?.as_str()?.to_owned();
                let name = block.get("name")?.as_str()?.to_owned();
                let input = block.get("input").cloned().unwrap_or(json!({}));
                let arguments = serde_json::to_string(&input).unwrap_or_default();
                Some(ToolCall { id, name, arguments })
            })
            .collect()
    }

    fn build_tool_results_request(
        &self,
        current_request: &Value,
        assistant_response: &Value,
        tool_results: &[ToolResult],
    ) -> Value {
        let mut request = current_request.clone();
        let messages = request
            .get_mut("messages")
            .and_then(|m| m.as_array_mut())
            .expect("request must have messages array");

        let assistant_content = assistant_response
            .get("content")
            .cloned()
            .unwrap_or(json!([]));
        messages.push(json!({
            "role": "assistant",
            "content": assistant_content,
        }));

        let tool_result_blocks: Vec<Value> = tool_results
            .iter()
            .map(|r| {
                let mut block = json!({
                    "type": "tool_result",
                    "tool_use_id": r.tool_call_id,
                    "content": r.content,
                });
                if r.is_error {
                    block["is_error"] = Value::Bool(true);
                }
                block
            })
            .collect();
        messages.push(json!({
            "role": "user",
            "content": tool_result_blocks,
        }));

        request["stream"] = Value::Bool(false);
        request
    }

    fn response_to_sse(&self, response: &Value) -> Vec<String> {
        let mut events = Vec::new();

        let mut msg_start = response.clone();
        msg_start["content"] = json!([]);
        if let Some(obj) = msg_start.as_object_mut() {
            obj.remove("stop_reason");
        }
        events.push(format!(
            "event: message_start\ndata: {}\n\n",
            json!({"type": "message_start", "message": msg_start})
        ));

        if let Some(content) = response.get("content").and_then(|c| c.as_array()) {
            for (i, block) in content.iter().enumerate() {
                let block_type = block.get("type").and_then(|t| t.as_str()).unwrap_or("text");
                if block_type == "text" {
                    let text = block.get("text").and_then(|t| t.as_str()).unwrap_or("");
                    events.push(format!(
                        "event: content_block_start\ndata: {}\n\n",
                        json!({"type": "content_block_start", "index": i, "content_block": {"type": "text", "text": ""}})
                    ));
                    events.push(format!(
                        "event: content_block_delta\ndata: {}\n\n",
                        json!({"type": "content_block_delta", "index": i, "delta": {"type": "text_delta", "text": text}})
                    ));
                    events.push(format!(
                        "event: content_block_stop\ndata: {}\n\n",
                        json!({"type": "content_block_stop", "index": i})
                    ));
                }
            }
        }

        let stop_reason = response
            .get("stop_reason")
            .and_then(|s| s.as_str())
            .unwrap_or("end_turn");
        events.push(format!(
            "event: message_delta\ndata: {}\n\n",
            json!({"type": "message_delta", "delta": {"stop_reason": stop_reason}})
        ));
        events.push("event: message_stop\ndata: {\"type\":\"message_stop\"}\n\n".to_owned());

        events
    }

    fn is_streaming_request(&self, request: &Value) -> bool {
        request
            .get("stream")
            .and_then(|s| s.as_bool())
            .unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn extract_tool_calls_single() {
        let codec = AnthropicCodec;
        let response = json!({
            "id": "msg_abc",
            "type": "message",
            "role": "assistant",
            "content": [
                {"type": "text", "text": "Let me read that file."},
                {"type": "tool_use", "id": "toolu_abc", "name": "read_file", "input": {"path": "/etc/hosts"}}
            ],
            "stop_reason": "tool_use"
        });
        let calls = codec.extract_tool_calls(&response);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].id, "toolu_abc");
        assert_eq!(calls[0].name, "read_file");
        assert!(calls[0].arguments.contains("/etc/hosts"));
    }

    #[test]
    fn extract_tool_calls_multiple() {
        let codec = AnthropicCodec;
        let response = json!({
            "content": [
                {"type": "tool_use", "id": "toolu_1", "name": "read_file", "input": {}},
                {"type": "tool_use", "id": "toolu_2", "name": "write_file", "input": {}}
            ],
            "stop_reason": "tool_use"
        });
        let calls = codec.extract_tool_calls(&response);
        assert_eq!(calls.len(), 2);
    }

    #[test]
    fn extract_tool_calls_text_only() {
        let codec = AnthropicCodec;
        let response = json!({
            "content": [
                {"type": "text", "text": "Hello world"}
            ],
            "stop_reason": "end_turn"
        });
        let calls = codec.extract_tool_calls(&response);
        assert!(calls.is_empty());
    }

    #[test]
    fn build_tool_results_appends_messages() {
        let codec = AnthropicCodec;
        let original = json!({
            "model": "claude-sonnet-4-20250514",
            "messages": [
                {"role": "user", "content": "Read the file"}
            ],
            "max_tokens": 1024
        });
        let assistant = json!({
            "role": "assistant",
            "content": [
                {"type": "text", "text": "I'll read it."},
                {"type": "tool_use", "id": "toolu_abc", "name": "read_file", "input": {"path": "/"}}
            ]
        });
        let results = vec![ToolResult {
            tool_call_id: "toolu_abc".into(),
            content: "file contents".into(),
            is_error: false,
        }];
        let new_req = codec.build_tool_results_request(&original, &assistant, &results);
        let messages = new_req["messages"].as_array().unwrap();
        assert_eq!(messages.len(), 3);
        assert_eq!(messages[1]["role"], "assistant");
        assert_eq!(messages[2]["role"], "user");
        let tool_result = &messages[2]["content"][0];
        assert_eq!(tool_result["type"], "tool_result");
        assert_eq!(tool_result["tool_use_id"], "toolu_abc");
    }

    #[test]
    fn response_to_sse_valid_events() {
        let codec = AnthropicCodec;
        let response = json!({
            "id": "msg_abc",
            "type": "message",
            "role": "assistant",
            "model": "claude-sonnet-4-20250514",
            "content": [{"type": "text", "text": "Hello world"}],
            "stop_reason": "end_turn",
            "usage": {"input_tokens": 10, "output_tokens": 5}
        });
        let chunks = codec.response_to_sse(&response);
        assert!(chunks.len() >= 3);
        assert!(chunks[0].contains("event: message_start"));
        assert!(chunks.last().unwrap().contains("event: message_stop"));
        let has_content = chunks.iter().any(|c| c.contains("Hello world"));
        assert!(has_content);
    }

    #[test]
    fn is_streaming_request_checks_stream_field() {
        let codec = AnthropicCodec;
        assert!(codec.is_streaming_request(&json!({"stream": true})));
        assert!(!codec.is_streaming_request(&json!({"model": "claude-sonnet-4-20250514"})));
    }
}
