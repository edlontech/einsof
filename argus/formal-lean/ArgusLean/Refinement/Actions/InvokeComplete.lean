import ArgusLean.Refinement.Actions.SentinelElevateTaint

/-! # Refinement — `invoke_complete`

`invoke_complete agent inv` point-clears `inv` from `agent`'s in-flight set, then on the **endorsed**
path (`output_bounded ∧ conforms ∧ ¬budget_exhausted`) self-debits `agent`'s budget, and on the
**unendorsed** path adds the completed tool's `conf_floor` to `agent`'s `taint_levels`/`gh_taint_invoked`.
No loops: the whole action branches on the single conformance gate.

It refines against `Rcomplete`, whose budget clause is the get-style `budgetReadC` convention (like
`Rret`), whose `in_flight` clause is the last-match `vmsMemLast` view (what `set_contains` reads and
`remove_from` writes), and which carries: the metadata correspondences (`tool_conf_floor`/
`tool_output_bounded` ↔ `ToolMetadata`) plus the well-formedness invariant that every in-flight
invocation is bound to a tool with metadata (maintained by `invoke_start`) — this rules out the kernel's
defensive "no binding"/"no metadata" early-exit paths under the gate. `output_conforms` is the one
opaque oracle (separate totality+agreement hypotheses, like the content gate). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## Extractor residual: `InvocationId.ne`

Same `PartialEq::ne` default-method residual as `agentId_ne_spec`; needed by the `VecSet.remove`
inside `remove_from` (the in-flight point-clear removes an `InvocationId`). -/

/-- The opaque extracted `InvocationId.ne` is faithful decidable disequality. -/
axiom invocationId_ne_spec (a b : types.InvocationId) :
    types.InvocationId.Insts.CoreCmpPartialEqInvocationId.ne a b = .ok (decide (a ≠ b))

/-! ## `set_contains` — last-match characterisation

The existing `vecMapKVecSetSetContains_spec` only gives `b = true → vmsMem` (∃-entry). `set_contains`
actually reads the *live* (last) entry, so it is faithfully the **iff** with `vmsMemLast`. -/

theorem setContainsLast_spec {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (vm : collections.VecMap K (collections.VecSet T)) (key : K) (elem : T) :
    collections.VecMapKVecSet.set_contains cloneK eqK cloneT eqT vm key elem ⦃ b =>
      b = true ↔ vmsMemLast vm key elem ⦄ := by
  unfold collections.VecMapKVecSet.set_contains
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec cloneK eqK heqK (collections.VecSet.Insts.CoreCloneClone cloneT)
      (vecSetClone_spec cloneT hcloneT) vm key)
  rw [hoEq]; simp only [bind_tc_ok]
  cases hL : vmLastEntry vm.entries.val key with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho
    simp only [spec_ok, Bool.false_eq_true, false_iff]
    rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
  | some p =>
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    have hp1 : p.1 = key := vmLastEntry_fst _ _ _ hL
    have hLk : vmLastEntry vm.entries.val key = some (key, p.2) := by rw [hL, ← hp1]
    show collections.VecSet.contains cloneT eqT p.2 elem ⦃ b => b = true ↔ vmsMemLast vm key elem ⦄
    obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists (vecSetContains_spec cloneT eqT heqT p.2 elem)
    rw [hbEq]; simp only [spec_ok]; rw [hbIff]
    constructor
    · intro hmem; exact ⟨p.2, hLk, hmem⟩
    · rintro ⟨vs, hvs, hv⟩
      rw [hLk, Option.some_inj, Prod.mk.injEq] at hvs
      obtain ⟨_, rfl⟩ := hvs; exact hv

/-! ## `remove_from` — last-match element removal

`remove_from self key elem` removes `elem` from the live (last) `key`-keyed set, framing every other
key. Last-match nested membership (`vmsMemLast`) — the `VecSet.remove` counterpart of `extend_into`'s
`union_with`. The find-last-index loop reuses the `lastMatchInv` machinery. -/

theorem removeFromLoop_spec {K T : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (entries : alloc.vec.Vec (K × collections.VecSet T)) (key : K) (idx0 i0 : Usize)
    (hi0 : i0.val ≤ entries.val.length)
    (hInv : lastMatchInv entries.val key idx0.val i0.val) :
    collections.VecMapKVecSet.remove_from_loop eqK entries key idx0 i0 ⦃ idx1 =>
      lastMatchInv entries.val key idx1.val entries.val.length ⦄ := by
  unfold collections.VecMapKVecSet.remove_from_loop
  apply loop.spec_decr_nat
    (measure := fun p => entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ entries.val.length ∧ lastMatchInv entries.val key p.1.val p.2.val)
  · rintro ⟨idx, i⟩ ⟨hile, hinv⟩
    simp only [collections.VecMapKVecSet.remove_from_loop.body, alloc.vec.Vec.len]
    split
    case isTrue h =>
      have hlt : i.val < entries.val.length := by scalar_tac
      step as ⟨t, vs0, he⟩
      have hget : entries.val[i.val]? = some (t, vs0) := by
        rw [List.getElem?_eq_getElem hlt, ← he]
      rw [heq t key]
      step*
      split
      · rename_i hb
        step*
        have ht : t = key := by simpa using hb
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        right
        refine ⟨hlt, ⟨(t, vs0), hget, ht⟩, ?_⟩
        intro k hk1 hk2 p hp; exfalso; omega
      · rename_i hb
        step*
        have ht : t ≠ key := by simpa using hb
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rcases hinv with ⟨hidxlen, hno⟩ | ⟨hidxlt, hex, hno⟩
        · left
          refine ⟨hidxlen, ?_⟩
          intro k hk p hp
          rcases (by omega : k < i.val ∨ k = i.val) with hlt' | heqk
          · exact hno k hlt' p hp
          · subst heqk; rw [hget, Option.some_inj] at hp; subst hp; exact ht
        · right
          refine ⟨hidxlt, hex, ?_⟩
          intro k hk1 hk2 p hp
          rcases (by omega : k < i.val ∨ k = i.val) with hlt' | heqk
          · exact hno k hk1 hlt' p hp
          · subst heqk; rw [hget, Option.some_inj] at hp; subst hp; exact ht
    case isFalse h =>
      have heq' : i.val = entries.val.length := by scalar_tac
      simp only [spec_ok]
      rwa [heq'] at hinv
  · exact ⟨hi0, hInv⟩

theorem vecMapKVecSetRemoveFrom_spec {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (hcloneK : ∀ x : K, cloneK.clone x = .ok x)
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (hneT : ∀ a b : T, eqT.ne a b = .ok (decide (a ≠ b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (key : K) (elem : T) :
    collections.VecMapKVecSet.remove_from cloneK eqK cloneT eqT self key elem ⦃ vm' =>
      ∀ k v, vmsMemLast vm' k v ↔ vmsMemLast self k v ∧ ¬ (k = key ∧ v = elem) ⦄ := by
  unfold collections.VecMapKVecSet.remove_from
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (removeFromLoop_spec eqK heqK self.entries key (alloc.vec.Vec.len self.entries) 0#usize
      (by scalar_tac) (by left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩))
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < self.entries.val.length := by scalar_tac
    rcases hlmi with ⟨hlen, _⟩ | ⟨_, hex, hno⟩
    · omega
    · obtain ⟨p, hp, hpk⟩ := hex
      have hpe : self.entries.val[idx1.val]'hidxlt = p := by
        rw [List.getElem?_eq_getElem hidxlt] at hp; exact Option.some_inj.mp hp
      have hmatch : (self.entries.val[idx1.val]'hidxlt).1 = key := by rw [hpe]; exact hpk
      have hlast : ∀ k, (hk : k < self.entries.val.length) → idx1.val < k →
          (self.entries.val[k]'hk).1 ≠ key := fun k hk hik =>
        hno k hik hk _ (List.getElem?_eq_getElem hk)
      step as ⟨kk, vs0, hidx⟩
      have hpair : (kk, vs0) = p := by
        have : (kk, vs0) = self.entries.val[idx1.val]'hidxlt := hidx; rw [hpe] at this; exact this
      have hvs0 : vs0 = p.2 := (Prod.mk.injEq .. ▸ hpair).2
      have hkk : kk = key := ((Prod.mk.injEq .. ▸ hpair).1).trans hpk
      rw [hcloneK kk, bind_tc_ok, vecSetClone_spec cloneT hcloneT vs0, bind_tc_ok]
      obtain ⟨s1, hs1Eq, hs1Mem⟩ :=
        spec_imp_exists (vecSetRemove_spec cloneT eqT hneT hcloneT vs0 elem)
      rw [hs1Eq]; simp only [bind_tc_ok]
      step*
      have hlastSelf : vmLastEntry self.entries.val key = some (key, p.2) := by
        rw [vmLastEntry_eq_of_isLast self.entries.val idx1.val key hidxlt hmatch hlast, hpe, ← hpk]
      intro k v
      unfold vmsMemLast
      rw [__post2, alloc.vec.Vec.set_val_eq, hkk,
        vmLastEntry_set_lastmatch _ idx1.val key s1 hidxlt hmatch hlast k]
      by_cases hk : k = key
      · subst k
        rw [if_pos rfl, hlastSelf]
        constructor
        · rintro ⟨ss, hss, hv⟩
          rw [Option.some_inj, Prod.mk.injEq] at hss
          obtain ⟨_, rfl⟩ := hss
          have := (hs1Mem v).mp hv
          exact ⟨⟨p.2, rfl, by rw [← hvs0]; exact this.1⟩, fun ⟨_, hve⟩ => this.2 hve⟩
        · rintro ⟨⟨ss, hss, hv⟩, hne⟩
          rw [Option.some_inj, Prod.mk.injEq] at hss
          obtain ⟨_, rfl⟩ := hss
          exact ⟨s1, rfl, (hs1Mem v).mpr ⟨by rw [hvs0]; exact hv, fun hve => hne ⟨rfl, hve⟩⟩⟩
      · rw [if_neg hk]; simp only [hk, false_and, not_false_eq_true, and_true]
  case isFalse hcond =>
    have hidxlen : idx1.val = self.entries.val.length := by
      rcases hlmi with ⟨hlen, _⟩ | ⟨hlt, _, _⟩
      · exact hlen
      · scalar_tac
    have hno : ∀ p ∈ self.entries.val, p.1 ≠ key := by
      rcases hlmi with ⟨_, h⟩ | ⟨hlt, _, _⟩
      · intro p hp
        obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
        exact h k (by omega) p (by rw [List.getElem?_eq_getElem hk, hkp])
      · omega
    simp only [spec_ok]
    intro k v
    by_cases hk : k = key
    · subst k
      have habs : ¬ vmsMemLast self key v := by
        rintro ⟨vs, hvs, _⟩; exact absurd (vmLastEntry_mem _ _ _ hvs) (fun hm => hno _ hm rfl)
      simp only [habs, false_and]
    · simp only [hk, false_and, not_false_eq_true, and_true]

/-! ## State relation `Rcomplete` -/

/-- Oracle-agreement relation for `invoke_complete`. `in_flight` via the last-match `vmsMemLast` view
    (`set_contains` reads / `remove_from` writes it); `taint_levels`/`gh_taint_invoked` via the insert
    `vmsMem` view; `agent_budget` get-style (`budgetReadC`, like `Rret`); `invocation_tool`
    one-directional; the immutable `tool_conf_floor`/`tool_output_bounded` pinned to `ToolMetadata`; and
    the **well-formedness** invariant that every in-flight invocation is bound to a tool with metadata
    (so the kernel's defensive no-binding / no-metadata exits cannot fire under the in-flight gate). -/
def Rcomplete (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ ag I, a.in_flight ag I ↔ vmsMemLast st.in_flight ag I) ∧
  (∀ ag L, a.taint_levels ag L ↔ vmsMem st.taint_levels ag (confC L)) ∧
  (∀ ag L, a.gh_taint_invoked ag L ↔ vmsMem st.gh_taint_invoked ag (confC L)) ∧
  (∀ G L, a.agent_budget G L ↔ budgetReadC st.agent_budget G = budgetC L) ∧
  (∀ I t, invToolC st I = some t → a.invocation_tool I = t) ∧
  (∀ t tmeta, toolMetaC bg t = some tmeta → a.tool_conf_floor t = confA tmeta.conf_floor) ∧
  (∀ t tmeta, toolMetaC bg t = some tmeta → (a.tool_output_bounded t ↔ tmeta.output_bounded = true)) ∧
  (∀ ag I, vmsMemLast st.in_flight ag I →
    ∃ t tmeta, invToolC st I = some t ∧ toolMetaC bg t = some tmeta)

/-- The endorsed (zero-taint) condition: the completed tool's output is bounded, the conformance
    oracle passes, and the agent's budget is not exhausted. -/
def completeEndorsed (st : state.KernelState) (agent : types.AgentId)
    (tmeta : background.ToolMetadata) (cf : Bool) : Prop :=
  tmeta.output_bounded = true ∧ cf = true ∧
    budgetReadC st.agent_budget agent ≠ types.BudgetLevel.Exhausted

/-! ## Inversion + refinement (TODO)

`invoke_complete_ok_inv` / `invoke_complete_refines` remain. The loop-free transition is fully scoped:
peel the two gates, the `remove_from` point-clear (`vecMapKVecSetRemoveFrom_spec`), the tool/metadata
lookups (ruled total by `Rcomplete`'s well-formedness invariant + the in-flight gate), and the
`zero_taint` conformance gate (`completeEndorsed` ↔ `output_bounded ∧ conforms ∧ ¬exhausted`), then the
two writes per path (endorsed: `debitBudget_spec`; unendorsed: two `insert_into` of `conf_floor`).

Open mechanics: (1) the do-notation `let (conf_floor, output_bounded) := (..)` tuple-`let` needs full
`simp` to reduce (same as the sentinel proof — `simp only`/`dsimp` won't); (2) the budget post must be
stated as endorsed/unendorsed implications, NOT `ite` on the non-decidable `completeEndorsed` Prop; (3)
the content/conformance oracle is the one opaque input (state-independent `hcf` + agreement `hcfA`). -/

end ArgusLean.Refinement
