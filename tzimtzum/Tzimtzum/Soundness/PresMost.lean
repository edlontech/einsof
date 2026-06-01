import Tzimtzum.Soundness.Common

/-! # C0 — initiation + the ten cascade-discharged actions

Every action whose 25 preservation VCs the `kav_discharge` cascade closes outright
(no budget-debit existential to reconstruct). The two budget actions
(`invoke_complete`, `return_endorsed`) live in their own modules. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

/-! ## Initiation -/

theorem init_sound (s : KSt) (hi : initial s) : allInv s := by
  kav_discharge initial

/-! ## Per-action preservation (cascade) -/

theorem pres_register_tool (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close1 register_tool).next s s') : allInv s' := by
  simp only [Kav.close1] at hn
  obtain ⟨tool, hg, hn⟩ := hn
  kav_discharge register_tool

theorem pres_load_instruction (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close2 load_instruction).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, instr, hg, hn⟩ := hn
  kav_discharge load_instruction

theorem pres_delegate (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close2 delegate).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨grantor, grantee, hg, hn⟩ := hn
  kav_discharge delegate

theorem pres_grant_capability (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close3 grant_capability).next s s') : allInv s' := by
  simp only [Kav.close3] at hn
  obtain ⟨prnt, child, cap, hg, hn⟩ := hn
  kav_discharge grant_capability

theorem pres_revoke (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close2 revoke).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨prnt, target, hg, hn⟩ := hn
  kav_discharge revoke

theorem pres_cascade_revoke (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close2 cascade_revoke).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨child, prnt, hg, hn⟩ := hn
  kav_discharge cascade_revoke

theorem pres_invoke_start (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close3 invoke_start).next s s') : allInv s' := by
  simp only [Kav.close3] at hn
  obtain ⟨a, tool, inv, hg, hn⟩ := hn
  kav_discharge invoke_start

theorem pres_return_unendorsed (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close2 return_unendorsed).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨child, prnt, hg, hn⟩ := hn
  kav_discharge return_unendorsed

theorem pres_sentinel_elevate_taint (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close2 sentinel_elevate_taint).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, l, hg, hn⟩ := hn
  kav_discharge sentinel_elevate_taint

theorem pres_sentinel_refresh_budget (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close1 sentinel_refresh_budget).next s s') : allInv s' := by
  simp only [Kav.close1] at hn
  obtain ⟨a, hg, hn⟩ := hn
  kav_discharge sentinel_refresh_budget

end Tzimtzum
