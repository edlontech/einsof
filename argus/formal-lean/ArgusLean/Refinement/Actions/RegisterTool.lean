import ArgusLean.Refinement.StateRelation

/-! # Refinement — `register_tool`

Forward simulation for the warm-up exemplar (the C1 spike, now the C2 template): whenever
the extracted `register_tool` transition succeeds from a concrete state related to an
abstract state `a`, the abstract `Tzimtzum.register_tool` action can take a matching step
whose post-state stays related.

The proof is split in two so every per-action file in the fan-out has the same shape:

* `register_tool_ok_inv` — the *inversion* lemma. Pure concrete-side decoding: it peels the
  `Result`-monad success path and exposes the preconditions the transition checks (metadata
  present, issuer trusted, tool not already registered) plus the membership characterisation
  of the post-state's `tool_registered` set. No abstract state appears.
* `register_tool_refines` — the *simulation* proper. Consumes the inversion lemma's clean
  outputs, builds the abstract witness, and discharges guard / next / state relation.

## Naming convention (reused across the fan-out)

Each `obtain ⟨_, _, _⟩ := spec_imp_exists (..._spec ...)` destructures the *same* triple in
the *same* order, so the three names always play the same roles:

* 1st — the **value** the operation returned (`issuerTrusted`, `alreadyRegistered`,
  `registeredAfter`);
* 2nd — the **equation** `operation = .ok value` (`…Eq`), used to rewrite it inside `hok`;
* 3rd — the **property** of that value (`…Iff` / `…Mem`).

`hStateEq`/`_hEventEq` are the two halves of the decoded result; the leading underscore on
the event marks it deliberately unused. In `register_tool_refines`, `hRegRel`/`hTrustRel`/
`hIssuerRel` are the three components of `Rtool` (registered / trusted-issuer / tool-issuer
correspondences). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Inversion lemma for a successful extracted `register_tool` step. Decodes the
    `Result`-monad success path of `transitions.register_tool` into the facts a caller
    actually needs: the looked-up metadata `toolMeta`, the two preconditions it gates on, and
    the post-state membership characterisation. This is the mechanical, abstract-side-free
    part every per-action simulation reuses (the C2 template). -/
theorem register_tool_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory) (tool : types.ToolId)
    (hcap : st.tool_registered.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.register_tool st bg tool = .ok (.Ok (st', ev))) :
    ∃ toolMeta,
      bg.tool_metadata tool = .ok (some toolMeta) ∧
      vsMem bg.trusted_issuers toolMeta.issuer ∧
      ¬ vsMem st.tool_registered tool ∧
      ∀ y, vsMem st'.tool_registered y ↔ vsMem st.tool_registered y ∨ y = tool := by
  simp only [transitions.register_tool] at hok
  -- Gate 1: the metadata lookup returns `.ok` of some option.
  obtain ⟨metaOpt, hMetaEq⟩ : ∃ o, bg.tool_metadata tool = .ok o := by
    cases h : bg.tool_metadata tool with
    | ok o => exact ⟨o, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hMetaEq] at hok
  simp only [bind_tc_ok] at hok
  -- Gate 2: the metadata is present (`some`).
  obtain ⟨toolMeta, rfl⟩ : ∃ tm, metaOpt = some tm := by
    cases metaOpt with
    | none => simp at hok
    | some tm => exact ⟨tm, rfl⟩
  simp only [issuerId_clone_spec, bind_tc_ok] at hok
  -- Gate 3: the issuer is trusted.
  obtain ⟨issuerTrusted, hIssuerTrustedEq, hIssuerTrustedIff⟩ :=
    spec_imp_exists (isTrustedIssuer_spec bg toolMeta.issuer)
  rw [hIssuerTrustedEq] at hok
  simp only [bind_tc_ok] at hok
  have hTrusted : issuerTrusted = true := by
    cases issuerTrusted with
    | true => rfl
    | false => simp at hok
  simp only [hTrusted, reduceIte] at hok
  -- Gate 4: the tool is not already registered.
  obtain ⟨alreadyRegistered, hContainsEq, hContainsIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hContainsEq] at hok
  simp only [bind_tc_ok] at hok
  have hNotReg : alreadyRegistered = false := by
    cases alreadyRegistered with
    | false => rfl
    | true => simp at hok
  simp only [hNotReg, reduceIte, Bool.false_eq_true] at hok
  -- The insert, then read off the result.
  simp only [toolId_clone_spec, bind_tc_ok] at hok
  obtain ⟨registeredAfter, hInsertEq, hInsertMem⟩ :=
    spec_imp_exists (vecSetInsert_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool hcap)
  rw [hInsertEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  refine ⟨toolMeta, hMetaEq, hIssuerTrustedIff.mp hTrusted, ?_, ?_⟩
  · intro hmem
    have hc := hContainsIff.mpr hmem
    rw [hNotReg] at hc
    exact Bool.false_ne_true hc
  · subst hStateEq
    exact hInsertMem

/-- Forward simulation: a successful extracted `register_tool` step is matched by the
    abstract action, preserving `Rtool`. The capacity side condition feeds the underlying
    `Vec.push`. -/
theorem register_tool_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (tool : types.ToolId)
    (hR : Rtool st bg a)
    (hcap : st.tool_registered.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.register_tool st bg tool = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.register_tool tool).guard a ∧
          (Tzimtzum.register_tool tool).next a a' ∧ Rtool st' bg a' := by
  obtain ⟨hRegRel, hTrustRel, hIssuerRel⟩ := hR
  obtain ⟨toolMeta, hMeta, hIssuerTrusted, hNotRegistered, hNewReg⟩ :=
    register_tool_ok_inv st bg tool hcap st' ev hok
  refine ⟨{a with tool_registered := fun T => a.tool_registered T ∨ T = tool}, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.register_tool]
    refine ⟨?_, ?_⟩
    · rw [hRegRel]; exact hNotRegistered
    · rw [hIssuerRel tool toolMeta hMeta, hTrustRel]; exact hIssuerTrusted
  · -- next
    simp [Tzimtzum.register_tool]
  · -- Rtool st' bg a'
    refine ⟨fun t => ?_, hTrustRel, hIssuerRel⟩
    have hPost := hNewReg t
    have hReg := hRegRel t
    simp only [vsMem] at hReg hPost ⊢
    grind

end ArgusLean.Refinement

-- Trust-base audit: only the kernel axioms + the two documented `String` extractor-model
-- axioms (`string_eq_spec`, `string_clone_spec`). No solver.
#print axioms ArgusLean.Refinement.register_tool_ok_inv
#print axioms ArgusLean.Refinement.register_tool_refines
