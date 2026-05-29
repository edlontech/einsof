import Auto.Tactic
import Duper.Tactic

open Lean Auto in
def Auto.duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option auto.native true

namespace Kav.Spike

-- Uninterpreted sorts → opaque types carried as section variables.
variable {AgentId ToolId InvId : Type}

-- ConfLevel becomes a concrete inductive (deletes Veil's ~30 ordering axioms).
-- «public» and «internal» are escaped because they are Lean 4 keywords.
inductive ConfLevel where
  | «public» | «internal» | sensitive | restricted
deriving instance DecidableEq, Repr for ConfLevel

-- «log» is escaped because it is a Lean 4 keyword.
inductive EgressKind where
  | net | fs | «log»
deriving instance DecidableEq, Repr for EgressKind

structure St (AgentId ToolId InvId : Type) where
  agent_active   : AgentId → Prop
  tool_registered: ToolId → Prop
  in_flight      : AgentId → InvId → Prop
  speculative_taint : AgentId → ConfLevel → Prop
  override_used  : AgentId → ToolId → ConfLevel → Prop
  invocation_tool: InvId → ToolId
  tool_egress    : ToolId → EgressKind → Prop
  flow_allows    : ConfLevel → EgressKind → Prop
  flow_inspects  : ConfLevel → EgressKind → Prop
  flow_override  : AgentId → ToolId → ConfLevel → Prop
  content_gate_passes : AgentId → ToolId → Prop
  authorizer_allows   : AgentId → ToolId → Prop
  tool_cap       : ToolId → ConfLevel → Prop
  agent_cap      : AgentId → ConfLevel → Prop
  root_agent     : AgentId

def guard (s : St AgentId ToolId InvId) (a : AgentId) (tool : ToolId) (inv : InvId) : Prop :=
  s.agent_active a ∧ a ≠ s.root_agent ∧ s.tool_registered tool ∧
  s.invocation_tool inv = tool ∧
  (∀ AG, ¬ s.in_flight AG inv) ∧
  (∀ (C : ConfLevel), s.tool_cap tool C → s.agent_cap a C) ∧
  (∀ (L : ConfLevel) (E : EgressKind), s.speculative_taint a L ∧ s.tool_egress tool E →
      s.flow_allows L E
      ∨ (s.flow_inspects L E ∧ s.content_gate_passes a tool)
      ∨ (s.flow_override a tool L ∧ ¬ s.override_used a tool L)) ∧
  s.authorizer_allows a tool

def post (s : St AgentId ToolId InvId) (a : AgentId) (tool : ToolId) (inv : InvId) :
    St AgentId ToolId InvId :=
  { s with
    in_flight := fun A I => s.in_flight A I ∨ (A = a ∧ I = inv)
    override_used := fun A T L =>
      s.override_used A T L
      ∨ (A = a ∧ T = tool ∧ s.flow_override a tool L ∧ s.speculative_taint a L
         ∧ (∃ E, s.tool_egress tool E
              ∧ ¬ s.flow_allows L E
              ∧ ¬ (s.flow_inspects L E ∧ s.content_gate_passes a tool))) }

def in_flight_active (s : St AgentId ToolId InvId) : Prop :=
  ∀ A I, s.in_flight A I → s.agent_active A

def override_consumed (s : St AgentId ToolId InvId) : Prop :=
  ∀ A I (L : ConfLevel),
    s.in_flight A I →
    s.flow_override A (s.invocation_tool I) L →
    s.speculative_taint A L →
    (∃ E, s.tool_egress (s.invocation_tool I) E
       ∧ ¬ s.flow_allows L E
       ∧ ¬ (s.flow_inspects L E ∧ s.content_gate_passes A (s.invocation_tool I))) →
    s.override_used A (s.invocation_tool I) L

theorem invoke_start_pres_in_flight_active
    (s : St AgentId ToolId InvId) (a : AgentId) (tool : ToolId) (inv : InvId)
    (hinv : in_flight_active s) (hg : guard s a tool inv) :
    in_flight_active (post s a tool inv) := by
  unfold in_flight_active guard post at *
  intro A I h
  rcases h with h | ⟨rfl, rfl⟩
  · exact hinv A I h
  · exact hg.1

set_option maxHeartbeats 1000000 in
theorem invoke_start_pres_override_consumed
    (s : St AgentId ToolId InvId) (a : AgentId) (tool : ToolId) (inv : InvId)
    (hinv : override_consumed s) (hg : guard s a tool inv) :
    override_consumed (post s a tool inv) := by
  unfold override_consumed guard post at *
  intro A I L hflight hov htaint hden
  by_cases hcase : (A = a ∧ I = inv)
  · -- freshly-modified cell: the consumption update fires
    obtain ⟨rfl, rfl⟩ := hcase
    have htool : s.invocation_tool I = tool := hg.2.2.2.1
    rw [htool] at hov hden
    right
    exact ⟨rfl, htool, hov, htaint, hden⟩
  · -- carried over: in_flight in s, so hinv applies; override_used monotone under post
    rcases hflight with hflight | hflight
    · left
      exact hinv A I L hflight hov htaint hden
    · exact absurd hflight hcase

-- Data point: can full automation close the corrected hard VC with NO manual case split?
set_option maxHeartbeats 1000000 in
theorem invoke_start_pres_override_consumed_auto
    (s : St AgentId ToolId InvId) (a : AgentId) (tool : ToolId) (inv : InvId)
    (hinv : override_consumed s) (hg : guard s a tool inv) :
    override_consumed (post s a tool inv) := by
  unfold override_consumed guard post at *
  auto

-- Same VC, bare `duper` (no auto wrapper) as an independent data point.
set_option maxHeartbeats 1000000 in
theorem invoke_start_pres_override_consumed_duper
    (s : St AgentId ToolId InvId) (a : AgentId) (tool : ToolId) (inv : InvId)
    (hinv : override_consumed s) (hg : guard s a tool inv) :
    override_consumed (post s a tool inv) := by
  unfold override_consumed guard post at *
  duper [hinv, hg]

#print axioms invoke_start_pres_override_consumed
#print axioms invoke_start_pres_override_consumed_auto

end Kav.Spike
