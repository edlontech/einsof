import Tzimtzum.Soundness.Common

/-! # Budget conservation — the budget's first verified statement

Design §5.7 "Per-action lemmas outside the bundle" / finding 5 (protocol evaluation):
delegation used to mint declassification budget for free (a child spawned with full
capacity, then could endorse on its own fresh meter and hand the parent laundered
results at zero fleet-wide cost). Task 3 closed the mint by spawning children at
budget `0`; this file is that fix's verified witness.

Lives OUTSIDE the kernel-checked invariant bundle (`allInv`) — it is a property of
individual transitions, not a state predicate preserved across all of them, so it is
proved directly against each action's `guard`/`next` rather than via `kav_discharge`.

Claim: every one of the 16 actions except `sentinel_credit_budget` is budget
non-increasing (`∀ A, s'.agent_budget A ≤ s.agent_budget A`). Eleven actions leave
`agent_budget` entirely framed (equality, hence `≤` by `rfl`-under-the-hood); `delegate`
sets the grantee's budget to `0` (`Nat.zero_le`); the three debiting actions
(`invoke_complete_endorsed`, `return_endorsed`, `grant_override`) subtract a weight
(`Nat.sub_le`). `sentinel_credit_budget` is deliberately excluded — it is the sole
faucet, per the design's "conservation-modulo-explicit-credit" framing.
-/

set_option maxHeartbeats 400000

namespace Tzimtzum

private def regTool : KTool → Kav.Action KSt := register_tool
private def unregTool : KTool → Kav.Action KSt := unregister_tool
private def loadInstr : KAgent → KInstr → Kav.Action KSt := load_instruction
private def deleg : KAgent → KAgent → Kav.Action KSt := delegate
private def grantCap : KAgent → KAgent → KCap → Kav.Action KSt := grant_capability
private def revokeAction : KAgent → KAgent → Kav.Action KSt := revoke
private def cascadeRevokeAction : KAgent → KAgent → Kav.Action KSt := cascade_revoke
private def invStart : KAgent → KTool → KInv → Kav.Action KSt := invoke_start
private def invCompEndorsed : KAgent → KInv → Kav.Action KSt := invoke_complete_endorsed
private def invCompUnendorsed : KAgent → KInv → Kav.Action KSt := invoke_complete_unendorsed
private def retEndorsed :
    KAgent → KAgent → ConfLevel → IntegLevel → Kav.Action KSt := return_endorsed
private def retUnendorsed : KAgent → KAgent → Kav.Action KSt := return_unendorsed
private def sentElevate : KAgent → ConfLevel → Kav.Action KSt := sentinel_elevate_taint
private def sentDegrade : KAgent → IntegLevel → Kav.Action KSt := sentinel_degrade_integrity
private def grantOverrideAction :
    KAgent → KAgent → KTool → ConfLevel → Kav.Action KSt := grant_override

/-! ## Frame-only actions (11)

`agent_budget` is not mentioned in any of these actions' bodies, so `kav_action`
auto-generates the frame conjunct `s'.agent_budget = s.agent_budget`; non-increase
follows by rewriting. -/

theorem budget_noninc_register_tool
    (tool : KTool) (s s' : KSt)
    (_hg : (regTool tool).guard s) (hn : (regTool tool).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold regTool register_tool Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_unregister_tool
    (tool : KTool) (s s' : KSt)
    (_hg : (unregTool tool).guard s) (hn : (unregTool tool).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold unregTool unregister_tool Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_load_instruction
    (a : KAgent) (instr : KInstr) (s s' : KSt)
    (_hg : (loadInstr a instr).guard s) (hn : (loadInstr a instr).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold loadInstr load_instruction Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_grant_capability
    (prnt child : KAgent) (cap : KCap) (s s' : KSt)
    (_hg : (grantCap prnt child cap).guard s) (hn : (grantCap prnt child cap).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold grantCap grant_capability Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_revoke
    (prnt target : KAgent) (s s' : KSt)
    (_hg : (revokeAction prnt target).guard s) (hn : (revokeAction prnt target).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold revokeAction revoke Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_cascade_revoke
    (child prnt : KAgent) (s s' : KSt)
    (_hg : (cascadeRevokeAction child prnt).guard s)
    (hn : (cascadeRevokeAction child prnt).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold cascadeRevokeAction cascade_revoke Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_invoke_start
    (a : KAgent) (tool : KTool) (inv : KInv) (s s' : KSt)
    (_hg : (invStart a tool inv).guard s) (hn : (invStart a tool inv).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold invStart invoke_start Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_invoke_complete_unendorsed
    (a : KAgent) (inv : KInv) (s s' : KSt)
    (_hg : (invCompUnendorsed a inv).guard s) (hn : (invCompUnendorsed a inv).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold invCompUnendorsed invoke_complete_unendorsed Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_return_unendorsed
    (child prnt : KAgent) (s s' : KSt)
    (_hg : (retUnendorsed child prnt).guard s) (hn : (retUnendorsed child prnt).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold retUnendorsed return_unendorsed Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_sentinel_elevate_taint
    (a : KAgent) (l : ConfLevel) (s s' : KSt)
    (_hg : (sentElevate a l).guard s) (hn : (sentElevate a l).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold sentElevate sentinel_elevate_taint Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

theorem budget_noninc_sentinel_degrade_integrity
    (a : KAgent) (l : IntegLevel) (s s' : KSt)
    (_hg : (sentDegrade a l).guard s) (hn : (sentDegrade a l).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold sentDegrade sentinel_degrade_integrity Kav.Action.next at hn
  have hbudget : s'.agent_budget = s.agent_budget := by grind
  intro A; rw [hbudget]; exact Nat.le_refl _

/-! ## The zero-spawn action (1)

`delegate` sets the grantee's budget to `0` (the mint fix, Task 3) — `0 ≤` anything. -/

open Classical in
theorem budget_noninc_delegate
    (grantor grantee : KAgent) (s s' : KSt)
    (_hg : (deleg grantor grantee).guard s) (hn : (deleg grantor grantee).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold deleg delegate Kav.Action.next at hn
  have hbudget : s'.agent_budget = fun G => if G = grantee then 0 else s.agent_budget G := by
    grind
  intro A
  simp only [hbudget]
  by_cases h : A = grantee
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]; exact Nat.le_refl _

/-! ## The debiting actions (3)

Each subtracts a weight from exactly one agent's budget; `Nat.sub_le` covers the
debited branch, the framed branch is `rfl`. -/

open Classical in
theorem budget_noninc_invoke_complete_endorsed
    (a : KAgent) (inv : KInv) (s s' : KSt)
    (_hg : (invCompEndorsed a inv).guard s) (hn : (invCompEndorsed a inv).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold invCompEndorsed invoke_complete_endorsed Kav.Action.next at hn
  have hbudget : s'.agent_budget =
      fun A => if A = a then s.agent_budget a - crossing_weight s a inv else s.agent_budget A := by
    grind
  intro A
  simp only [hbudget]
  by_cases h : A = a
  · subst h; rw [if_pos rfl]; exact Nat.sub_le _ _
  · rw [if_neg h]; exact Nat.le_refl _

open Classical in
theorem budget_noninc_return_endorsed
    (child prnt : KAgent) (clvl : ConfLevel) (ilvl : IntegLevel) (s s' : KSt)
    (_hg : (retEndorsed child prnt clvl ilvl).guard s)
    (hn : (retEndorsed child prnt clvl ilvl).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold retEndorsed return_endorsed Kav.Action.next at hn
  have hbudget : s'.agent_budget =
      fun A => if A = prnt
        then s.agent_budget prnt - (declass_weight clvl + integ_weight ilvl)
        else s.agent_budget A := by
    grind
  intro A
  simp only [hbudget]
  by_cases h : A = prnt
  · subst h; rw [if_pos rfl]; exact Nat.sub_le _ _
  · rw [if_neg h]; exact Nat.le_refl _

open Classical in
theorem budget_noninc_grant_override
    (granter target : KAgent) (tool : KTool) (lvl : ConfLevel) (s s' : KSt)
    (_hg : (grantOverrideAction granter target tool lvl).guard s)
    (hn : (grantOverrideAction granter target tool lvl).next s s') :
    ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  unfold grantOverrideAction grant_override Kav.Action.next at hn
  have hbudget : s'.agent_budget =
      fun A => if A = granter then s.agent_budget granter - declass_weight lvl else s.agent_budget A := by
    grind
  intro A
  simp only [hbudget]
  by_cases h : A = granter
  · subst h; rw [if_pos rfl]; exact Nat.sub_le _ _
  · rw [if_neg h]; exact Nat.le_refl _

/-! ## Bundled statement

Quantifies over every action in `ksystem.actions` except `sentinel_credit_budget` —
dispatch mirrors `Soundness/Bundle.lean`'s `hpres_bundle` `rcases` shape, destructuring
each `Kav.close_k`-existential to hand off to the matching per-action lemma above. -/

theorem budget_conservation :
    ∀ na ∈ ksystem.actions, na.1 ≠ "sentinel_credit_budget" →
      ∀ s s' : KSt, na.2.guard s → na.2.next s s' → ∀ A, s'.agent_budget A ≤ s.agent_budget A := by
  intro na hmem hne s s' hg hn
  simp only [ksystem, system, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Kav.close1] at hn; obtain ⟨tool, hg', hn'⟩ := hn
    exact budget_noninc_register_tool tool s s' hg' hn'
  · simp only [Kav.close1] at hn; obtain ⟨tool, hg', hn'⟩ := hn
    exact budget_noninc_unregister_tool tool s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨a, instr, hg', hn'⟩ := hn
    exact budget_noninc_load_instruction a instr s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨grantor, grantee, hg', hn'⟩ := hn
    exact budget_noninc_delegate grantor grantee s s' hg' hn'
  · simp only [Kav.close3] at hn; obtain ⟨prnt, child, cap, hg', hn'⟩ := hn
    exact budget_noninc_grant_capability prnt child cap s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨prnt, target, hg', hn'⟩ := hn
    exact budget_noninc_revoke prnt target s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨child, prnt, hg', hn'⟩ := hn
    exact budget_noninc_cascade_revoke child prnt s s' hg' hn'
  · simp only [Kav.close3] at hn; obtain ⟨a, tool, inv, hg', hn'⟩ := hn
    exact budget_noninc_invoke_start a tool inv s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨a, inv, hg', hn'⟩ := hn
    exact budget_noninc_invoke_complete_endorsed a inv s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨a, inv, hg', hn'⟩ := hn
    exact budget_noninc_invoke_complete_unendorsed a inv s s' hg' hn'
  · simp only [Kav.close4] at hn; obtain ⟨child, prnt, clvl, ilvl, hg', hn'⟩ := hn
    exact budget_noninc_return_endorsed child prnt clvl ilvl s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨child, prnt, hg', hn'⟩ := hn
    exact budget_noninc_return_unendorsed child prnt s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨a, l, hg', hn'⟩ := hn
    exact budget_noninc_sentinel_elevate_taint a l s s' hg' hn'
  · simp only [Kav.close2] at hn; obtain ⟨a, l, hg', hn'⟩ := hn
    exact budget_noninc_sentinel_degrade_integrity a l s s' hg' hn'
  · exact absurd rfl hne
  · simp only [Kav.close4] at hn; obtain ⟨granter, target, tool, lvl, hg', hn'⟩ := hn
    exact budget_noninc_grant_override granter target tool lvl s s' hg' hn'

#print axioms budget_conservation

end Tzimtzum
