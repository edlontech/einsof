import ArgusLean.Refinement.StateRelation

/-! # Refinement — `load_instruction`

Forward simulation for `load_instruction`, the structural twin of `register_tool`: same
two-gate shape (an active-agent gate + a trusted-issuer gate), but the write lands in the
*nested* per-agent set `agent_instruction : VecMap AgentId (VecSet InstructionId)`, exercised
through `VecMapKVecSet.insert_into`. This is the first action to consume the nested-membership
bridging (`vmsMem` / `vecMapKVecSetInsertInto_spec`) that every agent-keyed write reuses.

Same two-part split as the `register_tool` exemplar:

* `load_instruction_ok_inv` — inversion: peels the `Result`-monad success path into the active
  agent, the resolved-and-trusted instruction issuer, the post-state equation, and the nested
  membership characterisation of the inserted `agent_instruction` map.
* `load_instruction_refines` — simulation: builds the abstract witness and discharges guard /
  next / `Rinstr`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Inversion lemma for a successful extracted `load_instruction` step. The capacity side
    conditions feed the underlying `insert_into` (its inner `VecSet.insert`/`Vec.push`). -/
theorem load_instruction_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (agent : types.AgentId) (instr : types.InstructionId)
    (hcapE : st.agent_instruction.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_instruction.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.load_instruction st bg agent instr = .ok (.Ok (st', ev))) :
    ∃ issuer vmAfter,
      vsMem st.agent_active agent ∧
      background.BackgroundTheory.impl.instruction_issuer bg instr = .ok (some issuer) ∧
      vsMem bg.trusted_issuers issuer ∧
      st' = { st with agent_instruction := vmAfter } ∧
      (∀ ag ins, vmsMem vmAfter ag ins ↔
        vmsMem st.agent_instruction ag ins ∨ (ag = agent ∧ ins = instr)) := by
  simp only [transitions.load_instruction] at hok
  -- Gate 1: the agent is active.
  obtain ⟨activeB, hActiveEq, hActiveIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hActiveEq] at hok
  simp only [bind_tc_ok] at hok
  have hActive : activeB = true := by
    cases activeB with
    | true => rfl
    | false => simp at hok
  simp only [hActive, reduceIte] at hok
  -- Gate 2: the instruction issuer resolves (`some`).
  obtain ⟨issuerOpt, hIssuerEq⟩ :
      ∃ o, background.BackgroundTheory.impl.instruction_issuer bg instr = .ok o := by
    cases h : background.BackgroundTheory.impl.instruction_issuer bg instr with
    | ok o => exact ⟨o, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hIssuerEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨issuer, rfl⟩ : ∃ iss, issuerOpt = some iss := by
    cases issuerOpt with
    | none => simp at hok
    | some iss => exact ⟨iss, rfl⟩
  simp only [issuerId_clone_spec, bind_tc_ok] at hok
  -- Gate 3: that issuer is trusted.
  obtain ⟨trustedB, hTrustedEq, hTrustedIff⟩ := spec_imp_exists (isTrustedIssuer_spec bg issuer)
  rw [hTrustedEq] at hok
  simp only [bind_tc_ok] at hok
  have hTrusted : trustedB = true := by
    cases trustedB with
    | true => rfl
    | false => simp at hok
  simp only [hTrusted, reduceIte] at hok
  -- The nested insert, then read off the result.
  simp only [agentId_clone_spec, instructionId_clone_spec, bind_tc_ok] at hok
  obtain ⟨vmAfter, hInsertEq, hInsertMem⟩ :=
    spec_imp_exists (vecMapKVecSetInsertInto_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InstructionId.Insts.CoreCloneClone
      types.InstructionId.Insts.CoreCmpPartialEqInstructionId instructionId_eq_spec
      instructionId_clone_spec st.agent_instruction agent instr hcapE hcapS)
  rw [hInsertEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨issuer, vmAfter, hActiveIff.mp hActive, hIssuerEq, hTrustedIff.mp hTrusted,
    hStateEq.symm, hInsertMem⟩

/-- Forward simulation: a successful extracted `load_instruction` step is matched by the
    abstract action, preserving `Rinstr`. -/
theorem load_instruction_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (agent : types.AgentId) (instr : types.InstructionId)
    (hR : Rinstr st bg a)
    (hcapE : st.agent_instruction.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_instruction.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.load_instruction st bg agent instr = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.load_instruction agent instr).guard a ∧
          (Tzimtzum.load_instruction agent instr).next a a' ∧ Rinstr st' bg a' := by
  obtain ⟨hActiveRel, hTrustRel, hIssuerRel, hInstrRel⟩ := hR
  obtain ⟨issuer, vmAfter, hAgentActive, hIssuerEq, hIssuerTrusted, hStEq, hNewInstr⟩ :=
    load_instruction_ok_inv st bg agent instr hcapE hcapS st' ev hok
  refine ⟨{a with agent_instruction := fun A I => a.agent_instruction A I ∨ (A = agent ∧ I = instr)},
    ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.load_instruction]
    refine ⟨?_, ?_⟩
    · rw [hActiveRel]; exact hAgentActive
    · rw [hIssuerRel instr issuer hIssuerEq, hTrustRel]; exact hIssuerTrusted
  · -- next
    simp [Tzimtzum.load_instruction]
  · -- Rinstr st' bg a'
    subst hStEq
    refine ⟨hActiveRel, hTrustRel, hIssuerRel, ?_⟩
    intro ag ins
    show (a.agent_instruction ag ins ∨ (ag = agent ∧ ins = instr)) ↔ vmsMem vmAfter ag ins
    have h1 := hInstrRel ag ins
    have h2 := hNewInstr ag ins
    tauto

end ArgusLean.Refinement

-- Trust-base audit: identical to the `register_tool` exemplar (3 standard axioms + the
-- documented `String`/id extractor-model residuals). No solver.
#print axioms ArgusLean.Refinement.load_instruction_ok_inv
#print axioms ArgusLean.Refinement.load_instruction_refines
