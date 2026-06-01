import ArgusLean.Refinement.Collections
import Tzimtzum

/-! # C1 refinement spike — state relation

The abstract TzimtzumV2 state (`Tzimtzum.St`) instantiated at the kernel's concrete
sorts, plus the relation `Rtool` capturing exactly the fields the `register_tool`
transition reads or writes. (The full state relation `R` over all 28 fields is the C2
fan-out task; `Rtool` is the per-action slice the spike's simulation needs.) -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std argus_kernel

/-- The abstract TzimtzumV2 state at the kernel's concrete sorts. `ConfLevel`/`BudgetLevel`
    are concrete inductives baked into `St`; the remaining seven sorts are the extracted
    `String`/inductive types. -/
abbrev AbsState := Tzimtzum.St types.AgentId types.ToolId types.InvocationId
  capability.CapKind types.EgressKind types.IssuerId types.InstructionId

/-- State relation for the fields `register_tool` touches:
    * the mutable `tool_registered` set ↔ the concrete `VecSet`;
    * the background `trusted_issuer` predicate ↔ the `trusted_issuers` `VecSet`;
    * the background `tool_issuer` function ↔ the registered tools' metadata issuer. -/
def Rtool (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ t, a.tool_registered t ↔ vsMem st.tool_registered t) ∧
  (∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i) ∧
  (∀ t tm, bg.tool_metadata t = .ok (some tm) → a.tool_issuer t = tm.issuer)

/-- State relation for the fields `load_instruction` touches:
    * the mutable `agent_active` set ↔ the concrete `VecSet`;
    * the background `trusted_issuer` predicate ↔ the `trusted_issuers` `VecSet`;
    * the background `instruction_issuer` function ↔ the concrete lookup;
    * the mutable nested `agent_instruction` relation ↔ the concrete `VecMap`-of-`VecSet`. -/
def Rinstr (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i) ∧
  (∀ i issuer, background.BackgroundTheory.impl.instruction_issuer bg i = .ok (some issuer) →
      a.instruction_issuer i = issuer) ∧
  (∀ ag ins, a.agent_instruction ag ins ↔ vmsMem st.agent_instruction ag ins)

end ArgusLean.Refinement
