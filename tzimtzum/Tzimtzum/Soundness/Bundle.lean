import Tzimtzum.Soundness.PresMost
import Tzimtzum.Soundness.PresInvokeComplete
import Tzimtzum.Soundness.PresReturnEndorsed
import Tzimtzum.Soundness.PresGrantOverride
import Tzimtzum.Soundness.PresSentinelCreditBudget

/-! # C0 — assembly: `kav_sound` via `reachable_sound`

Feeds the per-action preservation lemmas + initiation into the protocol-independent
`Kav.reachable_sound` meta-induction to obtain: every reachable TzimtzumV2 state
satisfies the full invariant bundle. -/

set_option maxHeartbeats 1000000

namespace Tzimtzum

theorem hinit_bundle : ∀ s, ksystem.init s → allInv s := by
  intro s hi
  exact init_sound s hi

theorem hpres_bundle : ∀ na ∈ ksystem.actions, ∀ s s',
    allInv s → na.2.guard s → na.2.next s s' → allInv s' := by
  intro na hmem s s' hinv _hg hn
  simp only [ksystem, system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pres_register_tool s s' hinv hn
  · exact pres_unregister_tool s s' hinv hn
  · exact pres_load_instruction s s' hinv hn
  · exact pres_delegate s s' hinv hn
  · exact pres_grant_capability s s' hinv hn
  · exact pres_revoke s s' hinv hn
  · exact pres_cascade_revoke s s' hinv hn
  · exact pres_invoke_start s s' hinv hn
  · exact pres_invoke_complete_endorsed s s' hinv hn
  · exact pres_invoke_complete_unendorsed s s' hinv hn
  · exact pres_return_endorsed s s' hinv hn
  · exact pres_return_unendorsed s s' hinv hn
  · exact pres_sentinel_elevate_taint s s' hinv hn
  · exact pres_sentinel_credit_budget s s' hinv hn
  · exact pres_grant_override s s' hinv hn

/-- **Crown of C0:** every reachable state of the TzimtzumV2 transition system satisfies
    the full invariant bundle (9 safeties + 14 strengthening invariants). -/
theorem kav_sound (s : KSt) (h : Kav.Reachable ksystem s) : allInv s :=
  Kav.reachable_sound hinit_bundle hpres_bundle h

/-! ## Sort-polymorphic soundness

The `KSt` `kav_sound` above is the headline (and what the `#kav_check` audit prints axioms for), but
it is monomorphised at the opaque audit sorts. The Aeneas/Charon-extracted refinement
(`argus/formal-lean`) lives over the concrete `String`-backed id types, so it needs soundness at *its*
sorts. Since the invariants, actions, `system`, and `initial` are all sort-polymorphic and the
preservation proofs are sort-agnostic (`kav_discharge`), the bundle generalises verbatim: `kav_soundP`
is `kav_sound` over an arbitrary sort instantiation, and the `KSt` version is just `kav_soundP` at the
audit sorts. -/

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

theorem hinit_bundleP :
    ∀ s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId,
      system.init s → allInv s := by
  intro s hi
  exact init_sound s hi

theorem hpres_bundleP :
    ∀ na ∈ (system : Kav.TransitionSystem
        (St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)).actions,
      ∀ s s', allInv s → na.2.guard s → na.2.next s s' → allInv s' := by
  intro na hmem s s' hinv _hg hn
  simp only [system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pres_register_tool s s' hinv hn
  · exact pres_unregister_tool s s' hinv hn
  · exact pres_load_instruction s s' hinv hn
  · exact pres_delegate s s' hinv hn
  · exact pres_grant_capability s s' hinv hn
  · exact pres_revoke s s' hinv hn
  · exact pres_cascade_revoke s s' hinv hn
  · exact pres_invoke_start s s' hinv hn
  · exact pres_invoke_complete_endorsed s s' hinv hn
  · exact pres_invoke_complete_unendorsed s s' hinv hn
  · exact pres_return_endorsed s s' hinv hn
  · exact pres_return_unendorsed s s' hinv hn
  · exact pres_sentinel_elevate_taint s s' hinv hn
  · exact pres_sentinel_credit_budget s s' hinv hn
  · exact pres_grant_override s s' hinv hn

/-- **Sort-polymorphic crown of C0:** every reachable state of the TzimtzumV2 system — at *any* sort
    instantiation — satisfies the full invariant bundle. The refinement instantiates this at the
    extracted kernel's concrete id sorts. -/
theorem kav_soundP
    (s : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (h : Kav.Reachable system s) : allInv s :=
  Kav.reachable_sound hinit_bundleP hpres_bundleP h

end Tzimtzum
