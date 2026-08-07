import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `unregister_tool` preserves the unified `R` (V4)

`unregister_tool` writes only `tool_registered` (via `VecSet.remove`), framing everything else. Its
two ∀-guards — no pending record and no open challenge names the tool — are computed by
`unregister_tool_loop0` / `loop1`, which scan the `pending` / `challenges` maps entry-by-entry
(`key_at` + last-match `get_cloned`) and fold a `Bool`. Under the `vmNodupKeys` invariant each key
resolves to its own entry's value, so the fold decides "some record's `policy.tool` equals `tool`".
That concrete `∃`-over-entries is bridged to the abstract `∀`-over-`pending`/`challenges` guards via
`R.pending` / `R.challenges` + `snapshotRel` (which pins `policy.tool`). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- `unregister_tool_loop0` decides whether some pending record's `policy.tool` equals `tool`. -/
theorem unregisterLoop0_spec
    (vm : collections.VecMap types.InvocationId types.PendingInvocation) (tool : types.ToolId)
    (hnd : (vm.entries.val.map Prod.fst).Nodup)
    (start : Bool) (i0 : Usize) (hi0 : i0.val ≤ vm.entries.val.length)
    (hstart : start = true ↔ ∃ p ∈ vm.entries.val.take i0.val, p.2.policy.tool = tool) :
    transitions.unregister_tool_loop0 vm tool start i0 ⦃ b =>
      b = true ↔ ∃ p ∈ vm.entries.val, p.2.policy.tool = tool ⦄ := by
  unfold transitions.unregister_tool_loop0
  apply loop.spec_decr_nat
    (measure := fun p => vm.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ vm.entries.val.length ∧
      (p.1 = true ↔ ∃ q ∈ vm.entries.val.take p.2.val, q.2.policy.tool = tool))
  · rintro ⟨inUse, i⟩ ⟨hile, hinv⟩
    simp only [transitions.unregister_tool_loop0.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < vm.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.PendingInvocation.Insts.CoreCloneClone vm i hlt)
      rw [hkEq]; simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.PendingInvocation.Insts.CoreCloneClone pendingInvocation_clone_spec vm k)
      have hlast : vmLastEntry vm.entries.val k =
          some ((vm.entries.val[i.val]'hlt).1, (vm.entries.val[i.val]'hlt).2) := by
        rw [hk]; exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, toolId_eq_spec, bind_tc_ok]
      have htk : (∃ q ∈ vm.entries.val.take (i.val + 1), q.2.policy.tool = tool) ↔
          (∃ q ∈ vm.entries.val.take i.val, q.2.policy.tool = tool)
            ∨ (vm.entries.val[i.val]'hlt).2.policy.tool = tool := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨q, hq | hq, hpe⟩
          · exact Or.inl ⟨q, hq, hpe⟩
          · exact Or.inr (by rw [← hq]; exact hpe)
        · rintro (⟨q, hq, hpe⟩ | hpe)
          · exact ⟨q, Or.inl hq, hpe⟩
          · exact ⟨_, Or.inr rfl, hpe⟩
      by_cases hpt : (vm.entries.val[i.val]'hlt).2.policy.tool = tool
      · simp only [hpt, decide_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk]
        exact iff_of_true trivial (Or.inr hpt)
      · simp only [hpt, decide_false, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, htk, hinv]
        constructor
        · exact fun hh => Or.inl hh
        · rintro (hh | hh)
          · exact hh
          · exact absurd hh hpt
    case isFalse h =>
      have heq' : i.val = vm.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

/-- `unregister_tool_loop1` decides whether some challenge scope's `policy.tool` equals `tool`.
    Threads the pending-loop's result as its start flag. -/
theorem unregisterLoop1_spec
    (vm : collections.VecMap types.InvocationId types.ChallengeScope) (tool : types.ToolId)
    (hnd : (vm.entries.val.map Prod.fst).Nodup)
    (start : Bool) (i0 : Usize) (hi0 : i0.val ≤ vm.entries.val.length)
    (hstart : start = true ↔ P ∨ ∃ p ∈ vm.entries.val.take i0.val, p.2.policy.tool = tool) :
    transitions.unregister_tool_loop1 vm tool start i0 ⦃ b =>
      b = true ↔ P ∨ ∃ p ∈ vm.entries.val, p.2.policy.tool = tool ⦄ := by
  unfold transitions.unregister_tool_loop1
  apply loop.spec_decr_nat
    (measure := fun p => vm.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ vm.entries.val.length ∧
      (p.1 = true ↔ P ∨ ∃ q ∈ vm.entries.val.take p.2.val, q.2.policy.tool = tool))
  · rintro ⟨inUse, i⟩ ⟨hile, hinv⟩
    simp only [transitions.unregister_tool_loop1.body, collections.VecMap.len, alloc.vec.Vec.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < vm.entries.val.length := by scalar_tac
      obtain ⟨k, hkEq, hk⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId
          types.ChallengeScope.Insts.CoreCloneClone vm i hlt)
      rw [hkEq]; simp only [invocationId_clone_spec, bind_tc_ok]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ChallengeScope.Insts.CoreCloneClone challengeScope_clone_spec vm k)
      have hlast : vmLastEntry vm.entries.val k =
          some ((vm.entries.val[i.val]'hlt).1, (vm.entries.val[i.val]'hlt).2) := by
        rw [hk]; exact (vmLastEntry_nodup _ _ _ hnd).mpr (by simpa using List.getElem_mem hlt)
      rw [hoEq, ho, hlast]
      simp only [Option.map_some, toolId_eq_spec, bind_tc_ok]
      have htk : (∃ q ∈ vm.entries.val.take (i.val + 1), q.2.policy.tool = tool) ↔
          (∃ q ∈ vm.entries.val.take i.val, q.2.policy.tool = tool)
            ∨ (vm.entries.val[i.val]'hlt).2.policy.tool = tool := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨q, hq | hq, hpe⟩
          · exact Or.inl ⟨q, hq, hpe⟩
          · exact Or.inr (by rw [← hq]; exact hpe)
        · rintro (⟨q, hq, hpe⟩ | hpe)
          · exact ⟨q, Or.inl hq, hpe⟩
          · exact ⟨_, Or.inr rfl, hpe⟩
      by_cases hpt : (vm.entries.val[i.val]'hlt).2.policy.tool = tool
      · simp only [hpt, decide_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac]
        exact iff_of_true trivial (Or.inr (htk.mpr (Or.inr hpt)))
      · simp only [hpt, decide_false, Bool.false_eq_true, reduceIte]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i2.val = i.val + 1 from by scalar_tac, hinv]
        constructor
        · rintro (hh | hh)
          · exact Or.inl hh
          · exact Or.inr (htk.mpr (Or.inl hh))
        · rintro (hh | hh)
          · exact Or.inl hh
          · rcases htk.mp hh with hh' | hh'
            · exact Or.inr hh'
            · exact absurd hh' hpt
    case isFalse h =>
      have heq' : i.val = vm.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hinv ⊢
      exact hinv
  · exact ⟨hi0, by simpa using hstart⟩

/-- Bridge: some pending entry names `tool` ↔ some abstract pending record names `tool`. -/
theorem pending_tool_bridge (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState)
    (hR : R st bg a) (tool : types.ToolId) :
    (∃ p ∈ st.pending.entries.val, p.2.policy.tool = tool) ↔
      ∃ I J, a.pending I = some J ∧ J.policy.tool = tool := by
  constructor
  · rintro ⟨p, hp, hpt⟩
    have hlast : vmLastEntry st.pending.entries.val p.1 = some (p.1, p.2) :=
      (vmLastEntry_nodup _ _ _ hR.ndPending).mpr (by simpa using hp)
    have hpc : pendingC st p.1 = some p.2 := by
      unfold pendingC; rw [hlast]; rfl
    have hRp := hR.pending p.1
    rw [hpc] at hRp
    cases hap : a.pending p.1 with
    | none => rw [hap] at hRp; simp only [optRel] at hRp
    | some J =>
      rw [hap] at hRp; simp only [optRel, pendingRel, snapshotRel] at hRp
      obtain ⟨_, ⟨htool, _⟩, _⟩ := hRp
      exact ⟨p.1, J, hap, htool.trans hpt⟩
  · rintro ⟨I, J, haI, hJt⟩
    have hRp := hR.pending I
    rw [haI] at hRp
    cases hpc : pendingC st I with
    | none => rw [hpc] at hRp; simp only [optRel] at hRp
    | some cj =>
      rw [hpc] at hRp; simp only [optRel, pendingRel, snapshotRel] at hRp
      obtain ⟨_, ⟨htool, _⟩, _⟩ := hRp
      have hlast : vmLastEntry st.pending.entries.val I = some (I, cj) := by
        unfold pendingC at hpc
        cases hL : vmLastEntry st.pending.entries.val I with
        | none => rw [hL] at hpc; simp at hpc
        | some q =>
          obtain ⟨qk, qv⟩ := q
          have hq1 : qk = I := vmLastEntry_fst _ _ _ hL
          rw [hL] at hpc; simp only [Option.map_some, Option.some_inj] at hpc
          rw [hq1, hpc]
      exact ⟨(I, cj), (vmLastEntry_nodup _ _ _ hR.ndPending).mp hlast, htool.symm.trans hJt⟩

/-- Bridge: some challenge entry names `tool` ↔ some abstract challenge names `tool`. -/
theorem challenge_tool_bridge (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (hR : R st bg a) (tool : types.ToolId) :
    (∃ p ∈ st.challenges.entries.val, p.2.policy.tool = tool) ↔
      ∃ I sc, a.challenges I = some sc ∧ sc.policy.tool = tool := by
  constructor
  · rintro ⟨p, hp, hpt⟩
    have hlast : vmLastEntry st.challenges.entries.val p.1 = some (p.1, p.2) :=
      (vmLastEntry_nodup _ _ _ hR.ndChallenges).mpr (by simpa using hp)
    have hpc : challengeC st p.1 = some p.2 := by unfold challengeC; rw [hlast]; rfl
    have hRc := hR.challenges p.1
    rw [hpc] at hRc
    cases hac : a.challenges p.1 with
    | none => rw [hac] at hRc; simp only [optRel] at hRc
    | some sc =>
      rw [hac] at hRc; simp only [optRel, challengeRel, snapshotRel] at hRc
      obtain ⟨_, _, ⟨htool, _⟩, _⟩ := hRc
      exact ⟨p.1, sc, hac, htool.trans hpt⟩
  · rintro ⟨I, sc, haI, hsct⟩
    have hRc := hR.challenges I
    rw [haI] at hRc
    cases hcc : challengeC st I with
    | none => rw [hcc] at hRc; simp only [optRel] at hRc
    | some cc =>
      rw [hcc] at hRc; simp only [optRel, challengeRel, snapshotRel] at hRc
      obtain ⟨_, _, ⟨htool, _⟩, _⟩ := hRc
      have hlast : vmLastEntry st.challenges.entries.val I = some (I, cc) := by
        unfold challengeC at hcc
        cases hL : vmLastEntry st.challenges.entries.val I with
        | none => rw [hL] at hcc; simp at hcc
        | some q =>
          obtain ⟨qk, qv⟩ := q
          have hq1 : qk = I := vmLastEntry_fst _ _ _ hL
          rw [hL] at hcc; simp only [Option.map_some, Option.some_inj] at hcc
          rw [hq1, hcc]
      exact ⟨(I, cc), (vmLastEntry_nodup _ _ _ hR.ndChallenges).mp hlast, htool.symm.trans hsct⟩

/-- `unregister_tool` preserves the unified `R`. -/
theorem unregister_tool_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (tool : types.ToolId)
    (hR : R st bg a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.unregister_tool st tool = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.unregister_tool tool).guard a ∧
          (Tzimtzum.unregister_tool tool).next a a' ∧ R st' bg a' := by
  simp only [transitions.unregister_tool] at hok
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  obtain ⟨u0, hu0Eq, hu0Iff⟩ := spec_imp_exists
    (unregisterLoop0_spec st.pending tool hR.ndPending false 0#usize (by simp) (by simp))
  rw [hu0Eq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨u1, hu1Eq, hu1Iff⟩ := spec_imp_exists
    (unregisterLoop1_spec (P := ∃ p ∈ st.pending.entries.val, p.2.policy.tool = tool)
      st.challenges tool hR.ndChallenges u0 0#usize (by simp)
      (by simpa using hu0Iff))
  rw [hu1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hu1False : u1 = false := by
    cases u1 with
    | false => rfl
    | true => simp only [reduceIte] at hok; simp at hok
  simp only [hu1False, Bool.false_eq_true, reduceIte] at hok
  obtain ⟨vs, hvsEq, hvsMem⟩ := spec_imp_exists
    (vecSetRemove_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_ne_spec toolId_clone_spec
      st.tool_registered tool)
  rw [hvsEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEv⟩ := hok
  subst hStateEq
  -- The two guards hold (neither loop found the tool).
  have hNoPending : ¬ ∃ I J, a.pending I = some J ∧ J.policy.tool = tool := by
    rw [← pending_tool_bridge st bg a hR tool]
    intro hc
    have : u1 = true := hu1Iff.mpr (Or.inl hc)
    rw [hu1False] at this; exact Bool.false_ne_true this
  have hNoChallenge : ¬ ∃ I sc, a.challenges I = some sc ∧ sc.policy.tool = tool := by
    rw [← challenge_tool_bridge st bg a hR tool]
    intro hc
    have : u1 = true := hu1Iff.mpr (Or.inr hc)
    rw [hu1False] at this; exact Bool.false_ne_true this
  refine ⟨{ a with tool_registered := fun T => a.tool_registered T ∧ T ≠ tool }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.unregister_tool]
    refine ⟨(hR.tool_reg tool).mpr (hbIff.mp hb), ?_, ?_⟩
    · intro I J hJ hJt; exact hNoPending ⟨I, J, hJ, hJt⟩
    · intro I sc hsc hsct; exact hNoChallenge ⟨I, sc, hsc, hsct⟩
  · -- next
    simp [Tzimtzum.unregister_tool]
  · -- R st' bg a'
    refine ⟨hR.root, hR.mode, hR.active, ?_, hR.parent, hR.cap, hR.taint, hR.integ, hR.pending,
      hR.challenges, hR.grants, hR.consumedIds, hR.consumedAtt, hR.consumedCross, hR.flowAllows,
      hR.flowInspects, hR.ndParent, hR.ndCap, hR.ndTaint, hR.ndInteg, hR.ndPending, hR.ndChallenges,
      hR.ndGrants⟩
    intro t
    show (a.tool_registered t ∧ t ≠ tool) ↔ vsMem vs t
    rw [hvsMem t, hR.tool_reg t]

end ArgusLean.Refinement
