use crate::llm_codec::LlmCodec;
use crate::llm_types::{ToolCall, ToolResult};
use serde_json::{Value, json};

pub struct OpenAiCodec;

impl LlmCodec for OpenAiCodec {
    fn extract_tool_calls(&self, response: &Value) -> Vec<ToolCall> {
        let Some(choices) = response.get("choices").and_then(|c| c.as_array()) else {
            return Vec::new();
        };
        let Some(message) = choices.first().and_then(|c| c.get("message")) else {
            return Vec::new();
        };
        let Some(tool_calls) = message.get("tool_calls").and_then(|t| t.as_array()) else {
            return Vec::new();
        };
        tool_calls
            .iter()
            .filter_map(|tc| {
                let id = tc.get("id")?.as_str()?.to_owned();
                let function = tc.get("function")?;
                let name = function.get("name")?.as_str()?.to_owned();
                let arguments = function
                    .get("arguments")
                    .and_then(|a| a.as_str())
                    .unwrap_or("{}")
                    .to_owned();
                Some(ToolCall {
                    id,
                    name,
                    arguments,
                })
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

        if let Some(assistant_msg) = assistant_response
            .get("choices")
            .and_then(|c| c.as_array())
            .and_then(|c| c.first())
            .and_then(|c| c.get("message"))
        {
            messages.push(assistant_msg.clone());
        }

        for result in tool_results {
            messages.push(json!({
                "role": "tool",
                "tool_call_id": result.tool_call_id,
                "content": result.content,
            }));
        }

        request["stream"] = Value::Bool(false);
        request
    }

    fn response_to_sse(&self, response: &Value) -> Vec<String> {
        let content = response
            .get("choices")
            .and_then(|c| c.as_array())
            .and_then(|c| c.first())
            .and_then(|c| c.get("message"))
            .and_then(|m| m.get("content"))
            .and_then(|c| c.as_str())
            .unwrap_or("");

        let id = response
            .get("id")
            .cloned()
            .unwrap_or_else(|| json!("chatcmpl-proxy"));
        let model = response
            .get("model")
            .cloned()
            .unwrap_or_else(|| json!("unknown"));

        let chunk = json!({
            "id": id,
            "object": "chat.completion.chunk",
            "model": model,
            "choices": [{
                "index": 0,
                "delta": {
                    "role": "assistant",
                    "content": content,
                },
                "finish_reason": "stop"
            }]
        });

        vec![
            format!("data: {}\n\n", serde_json::to_string(&chunk).unwrap()),
            "data: [DONE]\n\n".to_owned(),
        ]
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
    use crate::llm_codec::LlmCodec;
    use serde_json::json;

    #[test]
    fn extract_tool_calls_single() {
        let codec = OpenAiCodec;
        let response = json!({
            "id": "chatcmpl-abc",
            "object": "chat.completion",
            "choices": [{
                "index": 0,
                "message": {
                    "role": "assistant",
                    "content": null,
                    "tool_calls": [{
                        "id": "call_abc",
                        "type": "function",
                        "function": {
                            "name": "read_file",
                            "arguments": "{\"path\":\"/etc/hosts\"}"
                        }
                    }]
                },
                "finish_reason": "tool_calls"
            }]
        });
        let calls = codec.extract_tool_calls(&response);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].id, "call_abc");
        assert_eq!(calls[0].name, "read_file");
        assert!(calls[0].arguments.contains("/etc/hosts"));
    }

    #[test]
    fn extract_tool_calls_multiple() {
        let codec = OpenAiCodec;
        let response = json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "tool_calls": [
                        {"id": "call_1", "type": "function", "function": {"name": "read_file", "arguments": "{}"}},
                        {"id": "call_2", "type": "function", "function": {"name": "write_file", "arguments": "{}"}}
                    ]
                },
                "finish_reason": "tool_calls"
            }]
        });
        let calls = codec.extract_tool_calls(&response);
        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0].name, "read_file");
        assert_eq!(calls[1].name, "write_file");
    }

    #[test]
    fn extract_tool_calls_none() {
        let codec = OpenAiCodec;
        let response = json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": "Hello world"
                },
                "finish_reason": "stop"
            }]
        });
        let calls = codec.extract_tool_calls(&response);
        assert!(calls.is_empty());
    }

    #[test]
    fn build_tool_results_appends_messages() {
        let codec = OpenAiCodec;
        let original = json!({
            "model": "gpt-4",
            "messages": [
                {"role": "user", "content": "Read the file"}
            ]
        });
        let assistant = json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": null,
                    "tool_calls": [{
                        "id": "call_abc",
                        "type": "function",
                        "function": {"name": "read_file", "arguments": "{}"}
                    }]
                }
            }]
        });
        let results = vec![ToolResult {
            tool_call_id: "call_abc".into(),
            content: "file contents".into(),
            is_error: false,
        }];
        let new_req = codec.build_tool_results_request(&original, &assistant, &results);
        let messages = new_req["messages"].as_array().unwrap();
        assert_eq!(messages.len(), 3);
        assert_eq!(messages[1]["role"], "assistant");
        assert_eq!(messages[2]["role"], "tool");
        assert_eq!(messages[2]["tool_call_id"], "call_abc");
        assert_eq!(messages[2]["content"], "file contents");
        assert_eq!(new_req["model"], "gpt-4");
        assert_eq!(new_req["stream"], false);
    }

    #[test]
    fn response_to_sse_produces_valid_chunks() {
        let codec = OpenAiCodec;
        let response = json!({
            "id": "chatcmpl-abc",
            "object": "chat.completion",
            "model": "gpt-4",
            "choices": [{
                "index": 0,
                "message": {
                    "role": "assistant",
                    "content": "Hello world"
                },
                "finish_reason": "stop"
            }]
        });
        let chunks = codec.response_to_sse(&response);
        assert_eq!(chunks.len(), 2);
        assert!(chunks[0].starts_with("data: "));
        assert!(chunks[0].contains("chat.completion.chunk"));
        assert!(chunks[0].contains("Hello world"));
        assert_eq!(chunks[1].trim(), "data: [DONE]");
    }

    #[test]
    fn is_streaming_request_checks_stream_field() {
        let codec = OpenAiCodec;
        assert!(codec.is_streaming_request(&json!({"stream": true})));
        assert!(!codec.is_streaming_request(&json!({"stream": false})));
        assert!(!codec.is_streaming_request(&json!({"model": "gpt-4"})));
    }
}
