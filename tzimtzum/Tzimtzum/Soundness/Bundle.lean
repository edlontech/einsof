import Tzimtzum.Soundness.PresMost
import Tzimtzum.Soundness.PresInvokeComplete
import Tzimtzum.Soundness.PresReturnEndorsed

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
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pres_register_tool s s' hinv hn
  · exact pres_load_instruction s s' hinv hn
  · exact pres_delegate s s' hinv hn
  · exact pres_grant_capability s s' hinv hn
  · exact pres_revoke s s' hinv hn
  · exact pres_cascade_revoke s s' hinv hn
  · exact pres_invoke_start s s' hinv hn
  · exact pres_invoke_complete s s' hinv hn
  · exact pres_return_endorsed s s' hinv hn
  · exact pres_return_unendorsed s s' hinv hn
  · exact pres_sentinel_elevate_taint s s' hinv hn
  · exact pres_sentinel_refresh_budget s s' hinv hn

/-- **Crown of C0:** every reachable state of the TzimtzumV2 transition system satisfies
    the full invariant bundle (10 safeties + 15 strengthening invariants). -/
theorem kav_sound (s : KSt) (h : Kav.Reachable ksystem s) : allInv s :=
  Kav.reachable_sound hinit_bundle hpres_bundle h

end Tzimtzum
