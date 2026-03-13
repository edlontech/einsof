use std::collections::BTreeMap;

use argus_kernel::{AgentId, AuthorizerOracle, BackgroundTheory, KernelState, ToolId};
use cedar_policy::{Authorizer, Decision, PolicySet, Schema};

use crate::cedar_schema::{build_entities_for_request, build_request, load_built_in_schema};
use crate::error::CedarError;
use crate::policy_source::{PolicySource, ToolScope};

pub struct CedarAuthorizer {
    authorizer: Authorizer,
    policy_set: PolicySet,
    schema: Schema,
    tool_scopes: BTreeMap<ToolId, ToolScope>,
}

impl CedarAuthorizer {
    pub fn new(source: &dyn PolicySource) -> Result<Self, CedarError> {
        let schema = load_built_in_schema()?;
        let policy_set = source.load_policies()?;
        let tool_scopes = source.load_tool_scopes()?;

        Ok(Self {
            authorizer: Authorizer::new(),
            policy_set,
            schema,
            tool_scopes,
        })
    }
}

impl AuthorizerOracle for CedarAuthorizer {
    fn allows(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool {
        let Ok(entities) = build_entities_for_request(agent, tool, state, bg, &self.tool_scopes)
        else {
            return false;
        };

        let Ok(request) = build_request(agent, tool, Some(&self.schema)) else {
            return false;
        };

        self.authorizer
            .is_authorized(&request, &self.policy_set, &entities)
            .decision()
            == Decision::Allow
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    use argus_kernel::{BackgroundTheoryBuilder, CapKind, ConfLevel, EgressKind, ToolMetadata};

    fn test_background() -> BackgroundTheory {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_tool(
            ToolId::new("endorsed-tool"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::from([EgressKind::FilesystemWrite]),
                conf_floor: ConfLevel::Internal,
                endorsed: true,
            },
        );
        builder.register_tool(
            ToolId::new("unendorsed-tool"),
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
        state.agent_active.insert(AgentId::new("worker"));
        state
            .agent_parent
            .insert(AgentId::new("worker"), AgentId::root());
        state.agent_cap.insert(
            AgentId::new("worker"),
            BTreeSet::from([CapKind::FilesystemRead, CapKind::NetworkEgress]),
        );
        state
    }

    struct InlinePolicySource {
        policy_text: String,
        scopes: BTreeMap<ToolId, ToolScope>,
    }

    impl PolicySource for InlinePolicySource {
        fn load_policies(&self) -> Result<PolicySet, CedarError> {
            if self.policy_text.is_empty() {
                return Ok(PolicySet::new());
            }
            self.policy_text
                .parse::<PolicySet>()
                .map_err(|e| CedarError::PolicyParse(e.to_string()))
        }
        fn load_tool_scopes(&self) -> Result<BTreeMap<ToolId, ToolScope>, CedarError> {
            Ok(self.scopes.clone())
        }
    }

    fn source_with_policy(policy: &str) -> InlinePolicySource {
        InlinePolicySource {
            policy_text: policy.to_string(),
            scopes: BTreeMap::new(),
        }
    }

    #[test]
    fn allows_endorsed_tool_with_default_policy() {
        let policy = r#"permit(principal, action == Argus::Action::"invoke", resource) when { resource.endorsed == true };"#;
        let source = source_with_policy(policy);
        let auth = CedarAuthorizer::new(&source).unwrap();
        assert!(auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("endorsed-tool"),
            &test_state(),
            &test_background()
        ));
    }

    #[test]
    fn denies_unendorsed_tool_with_endorsed_only_policy() {
        let policy = r#"permit(principal, action == Argus::Action::"invoke", resource) when { resource.endorsed == true };"#;
        let source = source_with_policy(policy);
        let auth = CedarAuthorizer::new(&source).unwrap();
        assert!(!auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("unendorsed-tool"),
            &test_state(),
            &test_background()
        ));
    }

    #[test]
    fn denies_when_no_policies() {
        let source = source_with_policy("");
        let auth = CedarAuthorizer::new(&source).unwrap();
        assert!(!auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("endorsed-tool"),
            &test_state(),
            &test_background()
        ));
    }

    #[test]
    fn forbid_overrides_permit() {
        let policy = r#"
            permit(principal, action == Argus::Action::"invoke", resource);
            forbid(principal, action == Argus::Action::"invoke", resource)
                when { resource.endorsed == false };
        "#;
        let source = source_with_policy(policy);
        let bg = test_background();
        let auth = CedarAuthorizer::new(&source).unwrap();
        assert!(auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("endorsed-tool"),
            &test_state(),
            &bg
        ));
        assert!(!auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("unendorsed-tool"),
            &test_state(),
            &bg
        ));
    }

    #[test]
    fn tainted_state_changes_decision() {
        let policy = r#"
            permit(principal, action == Argus::Action::"invoke", resource);
            forbid(principal, action == Argus::Action::"invoke", resource)
                when { principal.taint_levels.contains("restricted") };
        "#;
        let source = source_with_policy(policy);
        let bg = test_background();
        let auth = CedarAuthorizer::new(&source).unwrap();

        assert!(auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("endorsed-tool"),
            &test_state(),
            &bg
        ));

        let mut tainted_state = test_state();
        tainted_state.taint_levels.insert(
            AgentId::new("worker"),
            BTreeSet::from([ConfLevel::Restricted]),
        );

        assert!(!auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("endorsed-tool"),
            &tainted_state,
            &bg
        ));
    }

    #[test]
    fn unknown_agent_denied_by_attribute_policy() {
        let policy = r#"permit(principal, action == Argus::Action::"invoke", resource) when { resource.endorsed == true };"#;
        let source = source_with_policy(policy);
        let auth = CedarAuthorizer::new(&source).unwrap();
        let _ = auth.allows(
            &AgentId::new("ghost"),
            &ToolId::new("endorsed-tool"),
            &test_state(),
            &test_background(),
        );
    }

    #[test]
    fn unknown_tool_denied_by_attribute_policy() {
        let policy = r#"permit(principal, action == Argus::Action::"invoke", resource) when { resource.endorsed == true };"#;
        let source = source_with_policy(policy);
        let auth = CedarAuthorizer::new(&source).unwrap();
        assert!(!auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("nonexistent"),
            &test_state(),
            &test_background()
        ));
    }

    #[test]
    fn scope_based_policy() {
        let policy = r#"
            permit(principal, action == Argus::Action::"invoke", resource)
                when { resource has scope && resource.scope has paths };
        "#;
        let source = InlinePolicySource {
            policy_text: policy.to_string(),
            scopes: BTreeMap::from([(
                ToolId::new("endorsed-tool"),
                ToolScope {
                    paths: vec!["/home/**".to_string()],
                    ..Default::default()
                },
            )]),
        };
        let bg = test_background();
        let auth = CedarAuthorizer::new(&source).unwrap();
        assert!(auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("endorsed-tool"),
            &test_state(),
            &bg
        ));
        assert!(!auth.allows(
            &AgentId::new("worker"),
            &ToolId::new("unendorsed-tool"),
            &test_state(),
            &bg
        ));
    }
}
