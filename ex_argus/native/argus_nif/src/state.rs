use std::collections::HashMap;

use argus_kernel::{
    AgentId, BackgroundTheory, BackgroundTheoryBuilder, CapKind, ConfLevel, InstructionId,
    InvocationId, IssuerId, KernelState, OverrideKey, ToolId, ToolMetadata, VecMap, VecSet,
};
use rustler::{NifMap, NifStruct};

use crate::enums::{BudgetLevelN, CapKindN, ConfLevelN, EgressKindN};

#[derive(Debug, Clone, NifMap)]
pub struct ToolMetadataN {
    pub capabilities: Vec<CapKindN>,
    pub egress: Vec<EgressKindN>,
    pub conf_floor: ConfLevelN,
    pub output_bounded: bool,
    pub issuer: String,
}

impl ToolMetadataN {
    pub fn into_kernel(self) -> ToolMetadata {
        ToolMetadata {
            capabilities: self.capabilities.into_iter().map(CapKindN::into_kernel).collect(),
            egress: self.egress.into_iter().map(EgressKindN::into_kernel).collect(),
            conf_floor: self.conf_floor.into_kernel(),
            output_bounded: self.output_bounded,
            issuer: IssuerId(self.issuer),
        }
    }
}

#[derive(Debug, Clone, NifStruct)]
#[module = "ExArgus.Kernel.Background"]
pub struct BackgroundN {
    pub tools: HashMap<String, ToolMetadataN>,
    pub allow_ceiling: HashMap<EgressKindN, ConfLevelN>,
    pub inspect_ceiling: HashMap<EgressKindN, ConfLevelN>,
    pub trusted_issuers: Vec<String>,
    pub instruction_issuer: HashMap<String, String>,
}

impl BackgroundN {
    pub fn into_kernel(self) -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        for issuer in self.trusted_issuers {
            b.trust_issuer(IssuerId(issuer));
        }
        for (tool, meta) in self.tools {
            b.register_tool(ToolId(tool), meta.into_kernel());
        }
        // Merge both ceiling maps per egress: collect all egress keys, then call
        // set_egress_ceilings once per egress with both values.
        let mut egress_keys: Vec<EgressKindN> = Vec::new();
        for k in self.allow_ceiling.keys() {
            if !egress_keys.contains(k) {
                egress_keys.push(*k);
            }
        }
        for k in self.inspect_ceiling.keys() {
            if !egress_keys.contains(k) {
                egress_keys.push(*k);
            }
        }
        for egress in egress_keys {
            let allow = self.allow_ceiling.get(&egress).map(|l| l.into_kernel());
            let inspect = self.inspect_ceiling.get(&egress).map(|l| l.into_kernel());
            b.set_egress_ceilings(egress.into_kernel(), allow, inspect);
        }
        for (instr, issuer) in self.instruction_issuer {
            b.register_instruction(InstructionId(instr), IssuerId(issuer));
        }
        b.build()
    }
}

#[derive(Debug, Clone, NifStruct)]
#[module = "ExArgus.Kernel.State"]
pub struct StateN {
    pub agent_active: Vec<String>,
    pub agent_parent: HashMap<String, String>,
    pub agent_cap: HashMap<String, Vec<CapKindN>>,
    pub taint_levels: HashMap<String, Vec<ConfLevelN>>,
    pub in_flight: HashMap<String, Vec<String>>,
    pub invocation_tool: HashMap<String, String>,
    pub tool_registered: Vec<String>,
    pub gh_taint_invoked: HashMap<String, Vec<ConfLevelN>>,
    pub gh_taint_received: HashMap<String, Vec<ConfLevelN>>,
    pub agent_instruction: HashMap<String, Vec<String>>,
    pub override_used: HashMap<String, Vec<(String, ConfLevelN)>>,
    pub flow_override: HashMap<String, Vec<(String, ConfLevelN)>>,
    pub agent_budget: HashMap<String, BudgetLevelN>,
}

fn into_set_map<NV, KV, F>(m: HashMap<String, Vec<NV>>, f: F) -> VecMap<AgentId, VecSet<KV>>
where
    KV: Clone + PartialEq,
    F: Fn(NV) -> KV,
{
    m.into_iter()
        .map(|(k, v)| (AgentId(k), v.into_iter().map(&f).collect()))
        .collect()
}

fn from_set_map<KV, NV, F>(m: &VecMap<AgentId, VecSet<KV>>, f: F) -> HashMap<String, Vec<NV>>
where
    KV: Clone + PartialEq,
    F: Fn(&KV) -> NV,
{
    m.iter()
        .map(|(k, v)| (k.0.clone(), v.iter().map(&f).collect()))
        .collect()
}

impl StateN {
    pub fn into_kernel(self) -> KernelState {
        KernelState {
            agent_active: self.agent_active.into_iter().map(AgentId).collect(),
            agent_parent: self
                .agent_parent
                .into_iter()
                .map(|(k, v)| (AgentId(k), AgentId(v)))
                .collect(),
            agent_cap: into_set_map(self.agent_cap, CapKindN::into_kernel),
            taint_levels: into_set_map(self.taint_levels, ConfLevelN::into_kernel),
            in_flight: into_set_map(self.in_flight, InvocationId),
            invocation_tool: self
                .invocation_tool
                .into_iter()
                .map(|(k, v)| (InvocationId(k), ToolId(v)))
                .collect(),
            tool_registered: self.tool_registered.into_iter().map(ToolId).collect(),
            gh_taint_invoked: into_set_map(self.gh_taint_invoked, ConfLevelN::into_kernel),
            gh_taint_received: into_set_map(self.gh_taint_received, ConfLevelN::into_kernel),
            agent_instruction: into_set_map(self.agent_instruction, InstructionId),
            override_used: into_set_map(self.override_used, |(t, l)| OverrideKey {
                tool: ToolId(t),
                level: l.into_kernel(),
            }),
            flow_override: into_set_map(self.flow_override, |(t, l)| OverrideKey {
                tool: ToolId(t),
                level: l.into_kernel(),
            }),
            agent_budget: self
                .agent_budget
                .into_iter()
                .map(|(k, v)| (AgentId(k), v.into_kernel()))
                .collect(),
        }
    }

    pub fn from_kernel(ks: &KernelState) -> Self {
        StateN {
            agent_active: ks.agent_active.iter().map(|a| a.0.clone()).collect(),
            agent_parent: ks
                .agent_parent
                .iter()
                .map(|(k, v)| (k.0.clone(), v.0.clone()))
                .collect(),
            agent_cap: from_set_map(&ks.agent_cap, |c: &CapKind| CapKindN::from_kernel(*c)),
            taint_levels: from_set_map(&ks.taint_levels, |c: &ConfLevel| {
                ConfLevelN::from_kernel(*c)
            }),
            in_flight: from_set_map(&ks.in_flight, |i: &InvocationId| i.0.clone()),
            invocation_tool: ks
                .invocation_tool
                .iter()
                .map(|(k, v)| (k.0.clone(), v.0.clone()))
                .collect(),
            tool_registered: ks.tool_registered.iter().map(|t| t.0.clone()).collect(),
            gh_taint_invoked: from_set_map(&ks.gh_taint_invoked, |c: &ConfLevel| {
                ConfLevelN::from_kernel(*c)
            }),
            gh_taint_received: from_set_map(&ks.gh_taint_received, |c: &ConfLevel| {
                ConfLevelN::from_kernel(*c)
            }),
            agent_instruction: from_set_map(&ks.agent_instruction, |i: &InstructionId| {
                i.0.clone()
            }),
            override_used: from_set_map(&ks.override_used, |k: &OverrideKey| {
                (k.tool.0.clone(), ConfLevelN::from_kernel(k.level))
            }),
            flow_override: from_set_map(&ks.flow_override, |k: &OverrideKey| {
                (k.tool.0.clone(), ConfLevelN::from_kernel(k.level))
            }),
            agent_budget: ks
                .agent_budget
                .iter()
                .map(|(k, v)| (k.0.clone(), BudgetLevelN::from_kernel(*v)))
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initial_state_roundtrips() {
        let ks = KernelState::initial();
        let back = StateN::from_kernel(&ks).into_kernel();
        assert!(back.agent_active.contains(&AgentId::root()));
        assert_eq!(back.agent_cap.get(&AgentId::root()).unwrap().len(), 18);
        assert_eq!(back, ks);
    }

    #[test]
    fn flow_override_roundtrips() {
        let mut ks = KernelState::initial();
        let agent = AgentId::new("a1");
        ks.flow_override.insert_into(
            agent.clone(),
            OverrideKey { tool: ToolId::new("t"), level: ConfLevel::Sensitive },
        );
        let back = StateN::from_kernel(&ks).into_kernel();
        assert!(back.has_flow_override(&agent, &ToolId::new("t"), ConfLevel::Sensitive));
        assert!(!back.has_flow_override(&agent, &ToolId::new("t"), ConfLevel::Public));
        assert_eq!(back, ks);
    }

    #[test]
    fn single_entry_state_roundtrips() {
        let mut ks = KernelState::initial();
        ks.taint_levels
            .insert_into(AgentId::new("a1"), ConfLevel::Sensitive);
        ks.agent_budget
            .insert(AgentId::new("a1"), argus_kernel::BudgetLevel::L3);
        let back = StateN::from_kernel(&ks).into_kernel();
        assert!(back
            .taint_levels
            .get(&AgentId::new("a1"))
            .unwrap()
            .contains(&ConfLevel::Sensitive));
        assert_eq!(back.budget(&AgentId::new("a1")), argus_kernel::BudgetLevel::L3);
    }
}
