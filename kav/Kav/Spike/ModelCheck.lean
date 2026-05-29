import Kav.Spike.InvokeStart

namespace Kav.Spike

-- Finite index types: 2 agents, 2 tools, 2 invocations.
abbrev A2 := Fin 2

def allFin2 : List A2 := List.finRange 2
def allConf : List ConfLevel := [.«public», .«internal», .sensitive, .restricted]
def allEgress : List EgressKind := [.net, .fs, .«log»]

-- Decidable Bool-valued mirror of St, restricted to Fin 2 indices.
-- Fields mirror exactly what guard/post/override_consumed read.
structure DSt where
  agent_active        : A2 → Bool
  tool_registered     : A2 → Bool
  in_flight           : A2 → A2 → Bool          -- agent × inv
  speculative_taint   : A2 → ConfLevel → Bool
  override_used       : A2 → A2 → ConfLevel → Bool  -- agent × tool × level
  invocation_tool     : A2 → A2               -- inv → tool
  tool_egress         : A2 → EgressKind → Bool
  flow_allows         : ConfLevel → EgressKind → Bool
  flow_inspects       : ConfLevel → EgressKind → Bool
  flow_override       : A2 → A2 → ConfLevel → Bool  -- agent × tool × level
  content_gate_passes : A2 → A2 → Bool          -- agent × tool
  authorizer_allows   : A2 → A2 → Bool          -- agent × tool
  tool_cap            : A2 → ConfLevel → Bool
  agent_cap           : A2 → ConfLevel → Bool
  root_agent          : A2

-- Bool mirror of the override_consumed invariant.
-- For every in-flight (A, I, L): if flow_override, speculative_taint, and a
-- denying egress exist, then override_used must be set.
def override_consumedB (s : DSt) : Bool :=
  allFin2.all fun A =>
  allFin2.all fun I =>
  allConf.all fun L =>
    let tool := s.invocation_tool I
    !(s.in_flight A I
      && s.flow_override A tool L
      && s.speculative_taint A L
      && allEgress.any fun E =>
           s.tool_egress tool E
           && !s.flow_allows L E
           && !(s.flow_inspects L E && s.content_gate_passes A tool))
    || s.override_used A tool L

-- Bool mirror of the guard predicate.
def guardB (s : DSt) (a : A2) (tool : A2) (inv : A2) : Bool :=
  s.agent_active a
  && decide (a ≠ s.root_agent)
  && s.tool_registered tool
  && decide (s.invocation_tool inv = tool)
  && allFin2.all (fun AG => !s.in_flight AG inv)
  && allConf.all (fun C => !s.tool_cap tool C || s.agent_cap a C)
  && allConf.all (fun L =>
       allEgress.all fun E =>
         !(s.speculative_taint a L && s.tool_egress tool E)
         || s.flow_allows L E
         || (s.flow_inspects L E && s.content_gate_passes a tool)
         || (s.flow_override a tool L && !s.override_used a tool L))
  && s.authorizer_allows a tool

-- Bool mirror of the post function.
-- Extends in_flight and consumes override_used under the same taint-gated clause.
def postB (s : DSt) (a : A2) (tool : A2) (inv : A2) : DSt :=
  { s with
    in_flight := fun A I =>
      s.in_flight A I || (A == a && I == inv)
    override_used := fun A T L =>
      s.override_used A T L
      || (A == a && T == tool
          && s.flow_override a tool L
          && s.speculative_taint a L
          && allEgress.any fun E =>
               s.tool_egress tool E
               && !s.flow_allows L E
               && !(s.flow_inspects L E && s.content_gate_passes a tool)) }

-- Broken post: extends in_flight but NEVER consumes override_used.
-- This is the planted bug — the override consumption clause is dropped entirely.
def postB_broken (s : DSt) (a : A2) (_tool : A2) (inv : A2) : DSt :=
  { s with
    in_flight := fun A I => s.in_flight A I || (A == a && I == inv) }

-- A seed state crafted to exercise the override consumption path.
-- Agent 0 is the invoking agent; tool 0; inv 1 (fresh, not yet in_flight).
-- Conditions set so that: flow_override = true, speculative_taint = true,
-- tool_egress = true, flow_allows = false, flow_inspects = false for (agent 0, tool 0, .sensitive).
-- This means: after postB adds (agent 0, inv 1) to in_flight, override_used must be set.
-- postB_broken will NOT set it, so override_consumedB will be false on the post state.
def seed0 : DSt where
  agent_active        := fun a => a == 0          -- agent 0 active, agent 1 inactive
  tool_registered     := fun t => t == 0          -- tool 0 registered
  in_flight           := fun _ _ => false          -- nothing in flight yet
  speculative_taint   := fun a L =>
    a == 0 && decide (L = .sensitive)              -- agent 0 tainted at .sensitive
  override_used       := fun _ _ _ => false        -- no overrides consumed yet
  invocation_tool     := fun _ => 0                -- all invocations map to tool 0
  tool_egress         := fun t E =>
    t == 0 && decide (E = .net)                    -- tool 0 has net egress
  flow_allows         := fun _ _ => false          -- nothing allowed by default
  flow_inspects       := fun _ _ => false          -- nothing inspectable
  flow_override       := fun a t L =>
    a == 0 && t == 0 && decide (L = .sensitive)    -- agent 0 has override for tool 0 at .sensitive
  content_gate_passes := fun _ _ => false
  authorizer_allows   := fun a t => a == 0 && t == 0
  tool_cap            := fun _ _ => false          -- no capability constraints
  agent_cap           := fun _ _ => true
  root_agent          := 1                         -- agent 0 is NOT root

-- seed1: same as seed0 but agent 1 also active (more coverage).
def seed1 : DSt :=
  { seed0 with
    agent_active := fun _ => true }

-- seed2: agent 0 has inv 0 already in_flight (with override consumed), inv 1 is fresh.
-- Confirms the model is consistent: in_flight entry with consumed override satisfies the invariant.
def seed2 : DSt :=
  { seed0 with
    in_flight    := fun a i => a == 0 && i == 0
    override_used := fun a t L =>
      a == 0 && t == 0 && decide (L = .sensitive) }

def seeds : List DSt := [seed0, seed1, seed2]

-- CTI search over the seed set.
-- For each seed s where override_consumedB s = true, and each (a, tool, inv)
-- where guardB fires, check that the post state also satisfies override_consumedB.
-- Returns the first violating (s, a, tool, inv), or none.
def findCTI : Option (DSt × A2 × A2 × A2) :=
  (seeds.filter (fun s => override_consumedB s)).findSome? fun s =>
    allFin2.findSome? fun a =>
    allFin2.findSome? fun tool =>
    allFin2.findSome? fun inv =>
      if guardB s a tool inv && !override_consumedB (postB s a tool inv)
      then some (s, a, tool, inv)
      else none

def no_cti : Bool := findCTI.isNone

theorem invoke_start_model_check : no_cti = true := by native_decide

-- Broken-postB CTI search: same search but uses postB_broken.
def findCTI_broken : Option (DSt × A2 × A2 × A2) :=
  (seeds.filter (fun s => override_consumedB s)).findSome? fun s =>
    allFin2.findSome? fun a =>
    allFin2.findSome? fun tool =>
    allFin2.findSome? fun inv =>
      if guardB s a tool inv && !override_consumedB (postB_broken s a tool inv)
      then some (s, a, tool, inv)
      else none

def no_cti_broken : Bool := findCTI_broken.isNone

-- The planted bug IS detected: broken postB fails to consume override_used,
-- so override_consumedB on the post state is false — a CTI exists.
example : no_cti_broken = false := by native_decide

end Kav.Spike
