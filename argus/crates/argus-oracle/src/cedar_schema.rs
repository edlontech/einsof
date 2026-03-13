use std::collections::{BTreeMap, HashMap, HashSet};
use std::str::FromStr;

use argus_kernel::{AgentId, BackgroundTheory, KernelState, ToolId};
use cedar_policy::{
    Context, Entities, Entity, EntityId, EntityTypeName, EntityUid, Request, RestrictedExpression,
    Schema,
};

use crate::error::CedarError;
use crate::policy_source::ToolScope;

const BUILT_IN_SCHEMA: &str = include_str!("../cedar/schema.cedarschema");

pub fn load_built_in_schema() -> Result<Schema, CedarError> {
    Schema::from_cedarschema_str(BUILT_IN_SCHEMA)
        .map(|(schema, _warnings)| schema)
        .map_err(|e| CedarError::SchemaValidation(e.to_string()))
}

fn agent_type_name() -> EntityTypeName {
    EntityTypeName::from_str("Argus::Agent").expect("valid type name")
}

fn tool_type_name() -> EntityTypeName {
    EntityTypeName::from_str("Argus::Tool").expect("valid type name")
}

fn action_type_name() -> EntityTypeName {
    EntityTypeName::from_str("Argus::Action").expect("valid type name")
}

fn agent_uid(agent: &AgentId) -> EntityUid {
    EntityUid::from_type_name_and_id(agent_type_name(), EntityId::new(&agent.0))
}

fn tool_uid(tool: &ToolId) -> EntityUid {
    EntityUid::from_type_name_and_id(tool_type_name(), EntityId::new(&tool.0))
}

fn action_invoke_uid() -> EntityUid {
    EntityUid::from_type_name_and_id(action_type_name(), EntityId::new("invoke"))
}

fn string_set(items: impl IntoIterator<Item = impl AsRef<str>>) -> RestrictedExpression {
    RestrictedExpression::new_set(
        items
            .into_iter()
            .map(|s| RestrictedExpression::new_string(s.as_ref().to_string())),
    )
}

pub fn build_agent_entity(
    agent: &AgentId,
    state: &KernelState,
) -> Result<Option<Entity>, CedarError> {
    if !state.agent_active.contains(agent) {
        return Ok(None);
    }

    let uid = agent_uid(agent);

    let caps: Vec<String> = state
        .agent_cap
        .get(agent)
        .map(|s| s.iter().map(|c| c.to_string()).collect())
        .unwrap_or_default();

    let taints: Vec<String> = state
        .taint_levels
        .get(agent)
        .map(|s| s.iter().map(|c| c.to_string()).collect())
        .unwrap_or_default();

    let attrs = HashMap::from([
        ("capabilities".to_string(), string_set(&caps)),
        ("taint_levels".to_string(), string_set(&taints)),
    ]);

    let parents: HashSet<EntityUid> = state
        .agent_parent
        .get(agent)
        .map(agent_uid)
        .into_iter()
        .collect();

    Entity::new(uid, attrs, parents)
        .map(Some)
        .map_err(|e| CedarError::SchemaValidation(format!("agent entity: {e}")))
}

pub fn build_tool_entity(
    tool: &ToolId,
    bg: &BackgroundTheory,
    scopes: &BTreeMap<ToolId, ToolScope>,
) -> Result<Option<Entity>, CedarError> {
    let meta = match bg.tool_metadata(tool) {
        Some(m) => m,
        None => return Ok(None),
    };
    let uid = tool_uid(tool);

    let caps: Vec<String> = meta.capabilities.iter().map(|c| c.to_string()).collect();
    let egress: Vec<String> = meta.egress.iter().map(|e| e.to_string()).collect();

    let mut attrs = HashMap::from([
        (
            "endorsed".to_string(),
            RestrictedExpression::new_bool(meta.endorsed),
        ),
        (
            "conf_floor".to_string(),
            RestrictedExpression::new_string(meta.conf_floor.to_string()),
        ),
        ("capabilities".to_string(), string_set(&caps)),
        ("egress".to_string(), string_set(&egress)),
    ]);

    if let Some(scope) = scopes.get(tool) {
        let scope_fields: Vec<(String, RestrictedExpression)> = [
            ("paths", &scope.paths),
            ("domains", &scope.domains),
            ("commands", &scope.commands),
        ]
        .into_iter()
        .filter(|(_, v)| !v.is_empty())
        .map(|(name, v)| (name.to_string(), string_set(v)))
        .collect();

        if !scope_fields.is_empty() {
            let record = RestrictedExpression::new_record(scope_fields)
                .map_err(|e| CedarError::SchemaValidation(format!("tool scope: {e}")))?;
            attrs.insert("scope".to_string(), record);
        }
    }

    Entity::new(uid, attrs, HashSet::new())
        .map(Some)
        .map_err(|e| CedarError::SchemaValidation(format!("tool entity: {e}")))
}

pub fn build_entities_for_request(
    agent: &AgentId,
    tool: &ToolId,
    state: &KernelState,
    bg: &BackgroundTheory,
    scopes: &BTreeMap<ToolId, ToolScope>,
) -> Result<Entities, CedarError> {
    let mut entities = vec![];

    let mut current = Some(agent.clone());
    let mut visited = HashSet::new();
    while let Some(ref a) = current {
        if !visited.insert(a.clone()) {
            break;
        }
        if let Some(entity) = build_agent_entity(a, state)? {
            entities.push(entity);
        }
        current = state.agent_parent.get(a).cloned();
    }

    if let Some(entity) = build_tool_entity(tool, bg, scopes)? {
        entities.push(entity);
    }

    Entities::from_entities(entities, None).map_err(|e| CedarError::SchemaValidation(e.to_string()))
}

pub fn build_request(
    agent: &AgentId,
    tool: &ToolId,
    schema: Option<&Schema>,
) -> Result<Request, CedarError> {
    Request::new(
        agent_uid(agent),
        action_invoke_uid(),
        tool_uid(tool),
        Context::empty(),
        schema,
    )
    .map_err(|e| CedarError::SchemaValidation(e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    use argus_kernel::{BackgroundTheoryBuilder, CapKind, ConfLevel, EgressKind, ToolMetadata};
    use cedar_policy::{Authorizer, Decision, PolicySet};

    fn test_background() -> BackgroundTheory {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_tool(
            ToolId::new("fs-reader"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::from([EgressKind::FilesystemWrite]),
                conf_floor: ConfLevel::Internal,
                endorsed: true,
            },
        );
        builder.register_tool(
            ToolId::new("web-fetch"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Sensitive,
                endorsed: false,
            },
        );
        builder.build()
    }

    fn test_state() -> KernelState {
        let mut state = KernelState::initial();
        state.agent_active.insert(AgentId::new("child"));
        state
            .agent_parent
            .insert(AgentId::new("child"), AgentId::root());
        state.agent_cap.insert(
            AgentId::new("child"),
            BTreeSet::from([CapKind::FilesystemRead, CapKind::NetworkEgress]),
        );
        state
            .taint_levels
            .insert(AgentId::new("child"), BTreeSet::from([ConfLevel::Internal]));
        state
    }

    #[test]
    fn built_in_schema_parses() {
        let schema = load_built_in_schema();
        assert!(schema.is_ok(), "Schema failed to parse: {:?}", schema.err());
    }

    #[test]
    fn build_agent_entity_with_attributes() {
        let state = test_state();
        let entity = build_agent_entity(&AgentId::new("child"), &state).unwrap();
        assert!(entity.is_some());
    }

    #[test]
    fn build_agent_entity_returns_none_for_unknown() {
        let state = KernelState::initial();
        let entity = build_agent_entity(&AgentId::new("nonexistent"), &state).unwrap();
        assert!(entity.is_none());
    }

    #[test]
    fn build_tool_entity_with_scope() {
        let bg = test_background();
        let scopes = BTreeMap::from([(
            ToolId::new("fs-reader"),
            ToolScope {
                paths: vec!["/home/**".to_string()],
                ..Default::default()
            },
        )]);
        let entity = build_tool_entity(&ToolId::new("fs-reader"), &bg, &scopes).unwrap();
        assert!(entity.is_some());
    }

    #[test]
    fn build_tool_entity_returns_none_for_unknown() {
        let bg = test_background();
        let entity = build_tool_entity(&ToolId::new("unknown"), &bg, &BTreeMap::new()).unwrap();
        assert!(entity.is_none());
    }

    #[test]
    fn build_entities_for_request_includes_agent_chain_and_tool() {
        let state = test_state();
        let bg = test_background();
        let scopes = BTreeMap::new();
        let entities = build_entities_for_request(
            &AgentId::new("child"),
            &ToolId::new("fs-reader"),
            &state,
            &bg,
            &scopes,
        );
        assert!(entities.is_ok());
    }

    #[test]
    fn end_to_end_policy_evaluation() {
        let _schema = load_built_in_schema().unwrap();
        let state = test_state();
        let bg = test_background();
        let scopes = BTreeMap::new();

        let policy: PolicySet = r#"permit(principal, action == Argus::Action::"invoke", resource) when { resource.endorsed == true };"#
            .parse()
            .unwrap();

        let entities = build_entities_for_request(
            &AgentId::new("child"),
            &ToolId::new("fs-reader"),
            &state,
            &bg,
            &scopes,
        )
        .unwrap();

        let request =
            build_request(&AgentId::new("child"), &ToolId::new("fs-reader"), None).unwrap();
        let authorizer = Authorizer::new();
        let response = authorizer.is_authorized(&request, &policy, &entities);
        assert_eq!(response.decision(), Decision::Allow);
    }
}
