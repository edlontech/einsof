import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `load_instruction` preserves the unified `R`

`load_instruction` writes only the nested `agent_instruction` map (via `insert_into`), framing
everything else as `{ st with agent_instruction := vm }`. The exemplar for **insert-into** actions:
the changed field is re-related through the last-match `vmsMemLast` characterisation
(`vecMapKVecSetInsertInto_vmLast_spec`) and its `vmNodupKeys` post (`vecMapKVecSetInsertInto_nodup`),
both read off the *same* insert call. Every other conjunct transports definitionally. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Comprehensive inversion exposing the structural frame, the **last-match** membership
    characterisation of the inserted map, and its key-uniqueness post (the two read off the same
    `insert_into` call, linked by determinism). -/
theorem load_instruction_inv_full
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
      (∀ ag ins, vmsMemLast vmAfter ag ins ↔
        vmsMemLast st.agent_instruction ag ins ∨ (ag = agent ∧ ins = instr)) ∧
      (vmNodupKeys st.agent_instruction → vmNodupKeys vmAfter) := by
  simp only [transitions.load_instruction] at hok
  obtain ⟨activeB, hActiveEq, hActiveIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hActiveEq] at hok
  simp only [bind_tc_ok] at hok
  have hActive : activeB = true := by cases activeB with | true => rfl | false => simp at hok
  simp only [hActive, reduceIte] at hok
  obtain ⟨issuerOpt, hIssuerEq⟩ :
      ∃ o, background.BackgroundTheory.impl.instruction_issuer bg instr = .ok o := by
    cases h : background.BackgroundTheory.impl.instruction_issuer bg instr with
    | ok o => exact ⟨o, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hIssuerEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨issuer, rfl⟩ : ∃ iss, issuerOpt = some iss := by
    cases issuerOpt with | none => simp at hok | some iss => exact ⟨iss, rfl⟩
  simp only [issuerId_clone_spec, bind_tc_ok] at hok
  obtain ⟨trustedB, hTrustedEq, hTrustedIff⟩ := spec_imp_exists (isTrustedIssuer_spec bg issuer)
  rw [hTrustedEq] at hok
  simp only [bind_tc_ok] at hok
  have hTrusted : trustedB = true := by cases trustedB with | true => rfl | false => simp at hok
  simp only [hTrusted, reduceIte] at hok
  simp only [agentId_clone_spec, instructionId_clone_spec, bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmLast⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InstructionId.Insts.CoreCloneClone
      types.InstructionId.Insts.CoreCmpPartialEqInstructionId instructionId_eq_spec
      instructionId_clone_spec st.agent_instruction agent instr hcapE hcapS)
  obtain ⟨vm2, hvm2Eq, hvm2nd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InstructionId.Insts.CoreCloneClone
      types.InstructionId.Insts.CoreCmpPartialEqInstructionId instructionId_eq_spec
      instructionId_clone_spec st.agent_instruction agent instr hcapE hcapS)
  have hvv : vm2 = vm := Result.ok.inj (hvm2Eq.symm.trans hvmEq)
  rw [hvmEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨issuer, vm, hActiveIff.mp hActive, hIssuerEq, hTrustedIff.mp hTrusted, hStateEq.symm,
    hvmLast, hvv ▸ hvm2nd⟩

/-- `load_instruction` preserves the unified `R`. -/
theorem load_instruction_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (agent : types.AgentId) (instr : types.InstructionId)
    (hR : R st bg a)
    (hcapE : st.agent_instruction.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_instruction.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.load_instruction st bg agent instr = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.load_instruction agent instr).guard a ∧
          (Tzimtzum.load_instruction agent instr).next a a' ∧ R st' bg a' := by
  obtain ⟨issuer, vmAfter, hAgentActive, hIssuerEq, hIssuerTrusted, rfl, hvmLast, hvmNd⟩ :=
    load_instruction_inv_full st bg agent instr hcapE hcapS st' ev hok
  refine ⟨{ a with agent_instruction := fun A I => a.agent_instruction A I ∨ (A = agent ∧ I = instr) },
    ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.load_instruction]
    refine ⟨?_, ?_⟩
    · rw [hR.active]; exact hAgentActive
    · rw [hR.instrIssuer instr issuer hIssuerEq, hR.trustedIss]; exact hIssuerTrusted
  · -- next
    simp [Tzimtzum.load_instruction]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.active, hR.tool_reg, hR.parent, hR.cap, ?_,
      hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, hR.override, hR.budget, hR.toolCap,
      hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, ?_,
      hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, hR.ndOverride, hR.ndBudget,
      hR.wfInflight⟩
    · -- instr: last-match view, converted from R's pre-state view
      intro ag ins
      show (a.agent_instruction ag ins ∨ (ag = agent ∧ ins = instr)) ↔ vmsMemLast vmAfter ag ins
      rw [hvmLast ag ins, ← hR.instr ag ins]
    · -- ndInstr: insert preserves key-uniqueness
      exact hvmNd hR.ndInstr

end ArgusLean.Refinement
