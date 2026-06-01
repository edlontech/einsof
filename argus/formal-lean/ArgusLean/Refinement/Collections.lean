import ArgusLean.Generated.ArgusKernel

/-! # C1 refinement spike — collections bridging lemmas

Relates the Aeneas-extracted `VecSet`/`VecMap` operations (Vec-backed, with explicit
index `while` loops) to their abstract meaning as membership predicates over the
underlying list. These are the transparent bridging lemmas the state relation + the
per-action simulation proofs consume.

## Trust assumptions (extractor residual)

Rust's `String` is a stdlib primitive with no MIR body, so Charon/Aeneas extract its
`PartialEq::eq` and `Clone::clone` as bare, unspecified axioms (`String.…eq`/`…clone`).
We pin their behaviour to faithful decidable equality / identity. This is part of the
already-accepted "trust the extractor" residual — the same status the `String` model
itself has — and is the ONLY thing these axioms add to the TCB beyond
`propext`/`Classical.choice`/`Quot.sound` + Aeneas. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 1000000

/-- The opaque extracted `String` equality is faithful decidable equality. -/
axiom string_eq_spec (a b : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq a b = .ok (decide (a = b))

/-- The opaque extracted `String` clone is the identity. -/
axiom string_clone_spec (a : String) :
    alloc.string.String.Insts.CoreCloneClone.clone a = .ok a

instance : DecidableEq types.ToolId := inferInstanceAs (DecidableEq String)
instance : DecidableEq types.IssuerId := inferInstanceAs (DecidableEq String)
instance : DecidableEq types.AgentId := inferInstanceAs (DecidableEq String)
instance : DecidableEq types.InstructionId := inferInstanceAs (DecidableEq String)

/-- `ToolId.eq` inherits the faithful-decidable-equality behaviour from `String.eq`. -/
@[simp] theorem toolId_eq_spec (a b : types.ToolId) :
    types.ToolId.Insts.CoreCmpPartialEqToolId.eq a b = .ok (decide (a = b)) := by
  unfold types.ToolId.Insts.CoreCmpPartialEqToolId.eq
  exact string_eq_spec a b

/-- `IssuerId.eq` likewise. -/
@[simp] theorem issuerId_eq_spec (a b : types.IssuerId) :
    types.IssuerId.Insts.CoreCmpPartialEqIssuerId.eq a b = .ok (decide (a = b)) := by
  unfold types.IssuerId.Insts.CoreCmpPartialEqIssuerId.eq
  exact string_eq_spec a b

/-- `ToolId.clone` is the identity (inherited from `String.clone`). -/
@[simp] theorem toolId_clone_spec (a : types.ToolId) :
    types.ToolId.Insts.CoreCloneClone.clone a = .ok a := by
  simp only [types.ToolId.Insts.CoreCloneClone.clone, string_clone_spec, bind_tc_ok]

/-- `IssuerId.clone` is the identity. -/
@[simp] theorem issuerId_clone_spec (a : types.IssuerId) :
    types.IssuerId.Insts.CoreCloneClone.clone a = .ok a := by
  simp only [types.IssuerId.Insts.CoreCloneClone.clone, string_clone_spec, bind_tc_ok]

/-- `AgentId.eq` inherits faithful decidable equality from `String.eq`. -/
@[simp] theorem agentId_eq_spec (a b : types.AgentId) :
    types.AgentId.Insts.CoreCmpPartialEqAgentId.eq a b = .ok (decide (a = b)) := by
  unfold types.AgentId.Insts.CoreCmpPartialEqAgentId.eq
  exact string_eq_spec a b

/-- `InstructionId.eq` likewise. -/
@[simp] theorem instructionId_eq_spec (a b : types.InstructionId) :
    types.InstructionId.Insts.CoreCmpPartialEqInstructionId.eq a b = .ok (decide (a = b)) := by
  unfold types.InstructionId.Insts.CoreCmpPartialEqInstructionId.eq
  exact string_eq_spec a b

/-- `AgentId.clone` is the identity. -/
@[simp] theorem agentId_clone_spec (a : types.AgentId) :
    types.AgentId.Insts.CoreCloneClone.clone a = .ok a := by
  simp only [types.AgentId.Insts.CoreCloneClone.clone, string_clone_spec, bind_tc_ok]

/-- `InstructionId.clone` is the identity. -/
@[simp] theorem instructionId_clone_spec (a : types.InstructionId) :
    types.InstructionId.Insts.CoreCloneClone.clone a = .ok a := by
  simp only [types.InstructionId.Insts.CoreCloneClone.clone, string_clone_spec, bind_tc_ok]

/-! ## `PartialEq::ne` extractor residual

`PartialEq::ne` is a *default* trait method (`!self.eq(other)`), so Charon extracts the
per-type `…ne` as a bare, unspecified axiom (just like the `String` primitives). We pin it
to faithful decidable disequality — the same already-accepted "trust the extractor" status
as `string_eq_spec` / `string_clone_spec`. Only `AgentId.ne` is needed for the cleared-map
removes in `clear_agent_state`; other key types get their own residual when first used. -/

/-- The opaque extracted `AgentId.ne` is faithful decidable disequality. -/
axiom agentId_ne_spec (a b : types.AgentId) :
    types.AgentId.Insts.CoreCmpPartialEqAgentId.ne a b = .ok (decide (a ≠ b))

/-! ## VecSet membership abstraction -/

/-- A `VecSet`'s abstract meaning: membership in its underlying list. -/
def vsMem {T : Type} (vs : collections.VecSet T) (x : T) : Prop := x ∈ vs.items.val

/-! ## `VecSet.contains` -/

/-- Generalised loop spec for `VecSet.contains_loop`: starting from any position `i0`
    with the accumulator `found0` reflecting membership in the already-scanned prefix,
    the loop returns whether `x` is in the whole underlying list. Proved by the
    `loop.spec_decr_nat` invariant principle (measure = remaining elements). -/
theorem vecSetContains_loop_spec {T : Type} [DecidableEq T]
    (inst_eq : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst_eq.eq a b = .ok (decide (a = b)))
    (vs : collections.VecSet T) (x : T) (found0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ vs.items.val.length)
    (hfound0 : found0 = true ↔ x ∈ vs.items.val.take i0.val) :
    collections.VecSet.contains_loop inst_eq vs x found0 i0 ⦃ b =>
      (b = true ↔ x ∈ vs.items.val) ⦄ := by
  unfold collections.VecSet.contains_loop
  apply loop.spec_decr_nat
    (measure := fun p => vs.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ vs.items.val.length ∧
        (p.1 = true ↔ x ∈ vs.items.val.take p.2.val))
  · rintro ⟨found, i⟩ ⟨hile, hfound⟩
    simp only [collections.VecSet.contains_loop.body]
    split
    case isTrue h =>
      have hlt : i.val < vs.items.val.length := by scalar_tac
      step as ⟨t, ht⟩
      rw [heq t x]
      step*
      split <;>
        (step*
         simp only [i2_post]
         refine ⟨by omega, ?_, by omega⟩
         simp only [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
           List.mem_append, List.mem_singleton, ← ht]
         grind)
    case isFalse h =>
      have heq' : i.val = vs.items.val.length := by scalar_tac
      simp only [spec_ok]
      simp only [heq', List.take_length] at hfound
      simpa using hfound
  · exact ⟨hi0, hfound0⟩

/-- `VecSet.contains` decides membership in the abstract set. -/
theorem vecSetContains_spec {T : Type} [DecidableEq T]
    (inst_c : core.clone.Clone T) (inst_eq : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst_eq.eq a b = .ok (decide (a = b)))
    (vs : collections.VecSet T) (x : T) :
    collections.VecSet.contains inst_c inst_eq vs x ⦃ b => (b = true ↔ vsMem vs x) ⦄ := by
  unfold collections.VecSet.contains vsMem
  apply vecSetContains_loop_spec inst_eq heq vs x false 0#usize
  · simp
  · simp

/-! ## `VecSet.insert` -/

/-- `VecSet.insert` adds `x` to the abstract set (idempotently). The capacity side
    condition `length < Usize.max` is what the underlying `Vec.push` needs; it holds for
    any realistically-sized state and is the concrete counterpart of the abstract set
    being unbounded. -/
theorem vecSetInsert_spec {T : Type} [DecidableEq T]
    (inst_c : core.clone.Clone T) (inst_eq : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst_eq.eq a b = .ok (decide (a = b)))
    (vs : collections.VecSet T) (x : T) (hcap : vs.items.val.length < Usize.max) :
    collections.VecSet.insert inst_c inst_eq vs x ⦃ vs' =>
      ∀ y, vsMem vs' y ↔ vsMem vs y ∨ y = x ⦄ := by
  unfold collections.VecSet.insert
  obtain ⟨b, hcontains, hb⟩ :=
    spec_imp_exists (vecSetContains_spec inst_c inst_eq heq vs x)
  rw [hcontains]
  step*
  intro y
  simp only [vsMem, v_post, List.mem_append, List.mem_singleton]

/-! ## Background helper: `is_trusted_issuer`

`is_trusted_issuer` is literally `VecSet.contains` on `trusted_issuers`, so its spec is a
direct corollary — illustrating that the background-theory accessors compose out of the
collection bridging lemmas. -/

theorem isTrustedIssuer_spec (bg : background.BackgroundTheory) (i : types.IssuerId) :
    bg.is_trusted_issuer i ⦃ b => (b = true ↔ vsMem bg.trusted_issuers i) ⦄ := by
  unfold background.BackgroundTheory.is_trusted_issuer
  exact vecSetContains_spec _ _ issuerId_eq_spec bg.trusted_issuers i

/-! ## `VecSet.clone`

When the element clone is the identity (the case for every `String`-backed id), cloning a
`VecSet` is the identity. Delegates to the Aeneas `Slice.clone_spec`. -/

/-- Cloning a `VecSet` is the identity when the element clone is the identity. -/
theorem vecSetClone_spec {T : Type} (inst_c : core.clone.Clone T)
    (hclone : ∀ x, inst_c.clone x = .ok x) (vs : collections.VecSet T) :
    collections.VecSet.Insts.CoreCloneClone.clone inst_c vs = .ok vs := by
  unfold collections.VecSet.Insts.CoreCloneClone.clone alloc.vec.CloneVec.clone
  have h : ∀ x ∈ vs.items.val, inst_c.clone x = .ok x := fun x _ => hclone x
  obtain ⟨s', hs', heq⟩ := spec_imp_exists (Slice.clone_spec h)
  subst heq
  rw [hs']
  rfl

/-! ## VecMap-of-VecSet nested membership

`VecMap K (VecSet T)` is the concrete representation of every agent-keyed relation
(`agent_instruction`, `agent_cap`, `taint_levels`, `gh_taint_*`, `override_used`). Its
abstract meaning is the nested membership predicate `vmsMem`: key `k` maps to a set that
contains `v`. With the `∃ entry` formulation the `insert_into` characterisation below holds
without a key-uniqueness side condition (duplicate keys, were they present, contribute on
both sides of the iff). -/

/-- Nested membership for a `VecMap K (VecSet T)`: some entry keyed `k` holds `v`. -/
def vmsMem {K T : Type} (vm : collections.VecMap K (collections.VecSet T)) (k : K) (v : T) :
    Prop := ∃ vs, (k, vs) ∈ vm.entries.val ∧ v ∈ vs.items.val

/-! ## `VecMapKVecSet.insert_into` -/

/-- Find-index loop for `insert_into`: the returned index either runs off the end (key
    absent) or points at an entry whose key is `key`. We only need the latter half — the
    found branch of `insert_into` reads exactly this entry. The invariant carries it through:
    the accumulator starts at `len` (no entry there) and is only ever set to a matching
    position. -/
theorem vecMapKVecSetInsertIntoLoop_spec {K T : Type} [DecidableEq K]
    (inst_eq : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, inst_eq.eq a b = .ok (decide (a = b)))
    (v : alloc.vec.Vec (K × collections.VecSet T)) (key : K) (idx0 i0 : Usize)
    (hi0 : i0.val ≤ v.val.length)
    (hidx0 : ∀ p, v.val[idx0.val]? = some p → p.1 = key) :
    collections.VecMapKVecSet.insert_into_loop inst_eq v key idx0 i0 ⦃ idx1 =>
      ∀ p, v.val[idx1.val]? = some p → p.1 = key ⦄ := by
  unfold collections.VecMapKVecSet.insert_into_loop
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧
        (∀ q, v.val[p.1.val]? = some q → q.1 = key))
  · rintro ⟨idx, i⟩ ⟨hile, hidx⟩
    simp only [collections.VecMapKVecSet.insert_into_loop.body]
    split
    case isTrue h =>
      have hlt : i.val < v.val.length := by scalar_tac
      step as ⟨t, vs0, he⟩
      rw [heq t key]
      step*
      have hget : v.val[i.val]? = some (t, vs0) := by
        rw [List.getElem?_eq_getElem hlt, ← he]
      split <;>
        (step*
         refine ⟨by omega, ?_, by omega⟩
         intro q hq
         grind)
    case isFalse h =>
      simp only [spec_ok]
      exact hidx
  · exact ⟨hi0, hidx0⟩

/-- `insert_into vm key elem` adds `elem` to the set stored under `key`, creating that entry
    if absent. Stated as nested-membership preservation. The `∃ entry` formulation of `vmsMem`
    makes this hold with no key-uniqueness side condition. Capacity side conditions feed the
    inner `VecSet.insert`/`Vec.push`; `hcloneT`/`heqT` pin the element clone and equality. -/
theorem vecMapKVecSetInsertInto_spec {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (vm : collections.VecMap K (collections.VecSet T)) (key : K) (elem : T)
    (hcapE : vm.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ vm.entries.val, p.2.items.val.length < Usize.max) :
    collections.VecMapKVecSet.insert_into cloneK eqK cloneT eqT vm key elem ⦃ vm' =>
      ∀ k v, vmsMem vm' k v ↔ vmsMem vm k v ∨ (k = key ∧ v = elem) ⦄ := by
  unfold collections.VecMapKVecSet.insert_into
  simp only []
  obtain ⟨idx1, hloop, hidx1⟩ := spec_imp_exists
    (vecMapKVecSetInsertIntoLoop_spec eqK heqK vm.entries key
      (alloc.vec.Vec.len vm.entries) 0#usize (by scalar_tac)
      (by intro p hp; obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hp; scalar_tac))
  rw [hloop]
  simp only [bind_tc_ok]
  split
  case isTrue hcond =>
    have hlt : idx1.val < vm.entries.val.length := by scalar_tac
    step as ⟨k0, vs0, hidxEq⟩
    have hentry : vm.entries.val[idx1.val]? = some (k0, vs0) := by
      rw [List.getElem?_eq_getElem hlt, ← hidxEq]
    have hk0 : k0 = key := by simpa using hidx1 (k0, vs0) hentry
    have hmem0 : (k0, vs0) ∈ vm.entries.val := by rw [hidxEq]; exact List.getElem_mem hlt
    rw [vecSetClone_spec cloneT hcloneT vs0]
    simp only [bind_tc_ok]
    obtain ⟨s1, hs1Eq, hs1Mem⟩ :=
      spec_imp_exists (vecSetInsert_spec cloneT eqT heqT vs0 elem (hcapS _ hmem0))
    rw [hs1Eq]
    simp only [bind_tc_ok]
    step*
    subst hk0
    intro k v
    simp only [vmsMem, vsMem] at hs1Mem ⊢
    simp only [__post2]
    have hval : (↑(vm.entries.set idx1 (k0, s1)) : List (K × collections.VecSet T))
        = (↑vm.entries : List (K × collections.VecSet T)).set idx1.val (k0, s1) := rfl
    rw [hval]
    have hgetL : (↑vm.entries : List (K × collections.VecSet T))[idx1.val]'hlt = (k0, vs0) :=
      hidxEq.symm
    grind [List.mem_iff_getElem, List.length_set, List.getElem_set_self]
  case isFalse hcond =>
    simp only [collections.VecSet.new, bind_tc_ok]
    obtain ⟨s1, hs1Eq, hs1Mem⟩ :=
      spec_imp_exists (vecSetInsert_spec cloneT eqT heqT { items := alloc.vec.Vec.new T } elem
        (by scalar_tac))
    rw [hs1Eq]
    simp only [bind_tc_ok]
    step*
    intro k v
    simp only [vmsMem, vsMem] at hs1Mem ⊢
    rw [v_post]
    grind

/-! ## `VecMap.remove`

`remove` rebuilds the entry list keeping every pair whose key differs from the target — a
pure `List.filter`. The `BuiltinClone` on the kept pair is the identity (`.ok`), so no
per-element clone hypothesis is needed. This single characterisation feeds every
key-deletion: the nested-`vmsMem` corollary (the six maps `clear_agent_state` wipes) and the
plain-key `agent_budget` reasoning. -/

/-- Predicate kept by `VecMap.remove`: the entry's key is not the removed key. -/
abbrev removeKept {K V : Type} [DecidableEq K] (key : K) : K × V → Bool :=
  fun p => decide (p.1 ≠ key)

/-- Loop spec for `remove_loop`: the accumulator is the key-filtered prefix scanned so far,
    so at the end it is the whole filtered list. Mirrors the `VecSet.contains` loop shape,
    but accumulates a `Vec` via `push` instead of folding a `Bool`. -/
theorem vecMapRemoveLoop_spec {K V : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K)
    (hne : ∀ a b : K, eqK.ne a b = .ok (decide (a ≠ b)))
    (self : collections.VecMap K V) (key : K)
    (kept0 : alloc.vec.Vec (K × V)) (i0 : Usize)
    (hi0 : i0.val ≤ self.entries.val.length)
    (hkept0 : kept0.val = (self.entries.val.take i0.val).filter (removeKept key)) :
    collections.VecMap.remove_loop eqK self key kept0 i0 ⦃ kept =>
      kept.val = self.entries.val.filter (removeKept key) ⦄ := by
  unfold collections.VecMap.remove_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.entries.val.length ∧
        p.1.val = (self.entries.val.take p.2.val).filter (removeKept key))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [collections.VecMap.remove_loop.body]
    split
    case isTrue h =>
      have hlt : i.val < self.entries.val.length := by scalar_tac
      step as ⟨t, t1, he⟩
      have hget : self.entries.val[i.val]? = some (t, t1) := by
        rw [List.getElem?_eq_getElem hlt, ← he]
      have hcapk : kept.val.length < Usize.max := by
        have h1 : kept.val.length ≤ i.val := by
          rw [hkept]
          exact le_trans (List.length_filter_le _ _)
            (by rw [List.length_take]; exact Nat.min_le_left _ _)
        scalar_tac
      rw [hne t key]
      step*
      split
      · rename_i hb
        simp only [BuiltinClone]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [kept1_post, i2_post, List.take_add_one, hget, Option.toList_some]
        simp [List.filter_append, removeKept, hb, ← hkept]
      · rename_i hb
        step*
        have hbf : decide (t ≠ key) = false := by simpa using hb
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [i2_post, List.take_add_one, hget, Option.toList_some]
        simp [List.filter_append, removeKept, hbf, ← hkept]
    case isFalse h =>
      have heq' : i.val = self.entries.val.length := by scalar_tac
      simp only [spec_ok]
      simpa [heq', List.take_length] using hkept
  · exact ⟨hi0, hkept0⟩

/-- `VecMap.remove self key` returns the key-filtered entry list. -/
theorem vecMapRemove_spec {K V : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (hne : ∀ a b : K, eqK.ne a b = .ok (decide (a ≠ b)))
    (cloneV : core.clone.Clone V)
    (self : collections.VecMap K V) (key : K) :
    collections.VecMap.remove cloneK eqK cloneV self key ⦃ vm' =>
      vm'.entries.val = self.entries.val.filter (removeKept key) ⦄ := by
  unfold collections.VecMap.remove
  obtain ⟨kept, hkeptEq, hkeptMem⟩ :=
    spec_imp_exists (vecMapRemoveLoop_spec eqK hne self key
      ⟨[], by simp⟩ 0#usize (by simp) (by simp))
  rw [hkeptEq]
  simpa using hkeptMem

/-- Nested-membership corollary of `remove`: deleting `key` drops exactly the entries keyed
    `key`. Holds with no key-uniqueness side condition (`vmsMem` is `∃`-entry, and `filter`
    commutes with it). This is what the six `clear_agent_state` wipes consume. -/
theorem vecMapRemove_vmsMem {K T : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (hne : ∀ a b : K, eqK.ne a b = .ok (decide (a ≠ b)))
    (cloneV : core.clone.Clone (collections.VecSet T))
    (vm : collections.VecMap K (collections.VecSet T)) (key : K) :
    collections.VecMap.remove cloneK eqK cloneV vm key ⦃ vm' =>
      ∀ k v, vmsMem vm' k v ↔ vmsMem vm k v ∧ k ≠ key ⦄ := by
  obtain ⟨vm', hEq, hMem⟩ := spec_imp_exists (vecMapRemove_spec cloneK eqK hne cloneV vm key)
  rw [hEq]
  intro k v
  simp only [vmsMem, hMem, List.mem_filter, removeKept, decide_not, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not]
  constructor
  · rintro ⟨vs, ⟨hmem, hk⟩, hv⟩; exact ⟨⟨vs, hmem, hv⟩, hk⟩
  · rintro ⟨⟨vs, hmem, hv⟩, hk⟩; exact ⟨vs, ⟨hmem, hk⟩, hv⟩

/-- `(k, v) ∈ filter (removeKept key) l ↔ (k, v) ∈ l ∧ k ≠ key`. Plain-key membership through
    the `clear_agent_state` filter (consumed by the `agent_budget` reasoning). -/
theorem mem_filter_removeKept {K V : Type} [DecidableEq K] (l : List (K × V)) (key k : K) (v : V) :
    (k, v) ∈ l.filter (removeKept key) ↔ (k, v) ∈ l ∧ k ≠ key := by
  rw [List.mem_filter]
  simp only [removeKept, decide_eq_true_eq]

/-- Nested `vmsMem` through the `clear_agent_state` filter: a field whose entries became
    `filter (removeKept key)` keeps every member except those keyed `key`. -/
theorem vmsMem_filter_removeKept {K T : Type} [DecidableEq K]
    (vm' vm : collections.VecMap K (collections.VecSet T)) (key : K)
    (h : vm'.entries.val = vm.entries.val.filter (removeKept key)) (k : K) (v : T) :
    vmsMem vm' k v ↔ vmsMem vm k v ∧ k ≠ key := by
  simp only [vmsMem, h]
  constructor
  · rintro ⟨vs, hmem, hv⟩
    rw [List.mem_filter] at hmem
    obtain ⟨hmem', hk⟩ := hmem
    simp only [removeKept, decide_eq_true_eq] at hk
    exact ⟨⟨vs, hmem', hv⟩, hk⟩
  · rintro ⟨⟨vs, hmem, hv⟩, hk⟩
    exact ⟨vs, by rw [List.mem_filter]; exact ⟨hmem, by simp [removeKept, hk]⟩, hv⟩

/-! ## `VecMap.insert` at the last-entry level

`VecMap.insert` uses *last-match* semantics: it overwrites the last entry whose key matches
(or appends if none). The functional reading that survives duplicate keys is therefore
**get-style**: a key resolves to the value of its *last* matching entry. We capture that as
`vmLastEntry` (the `getLast?` of the key-filtered sublist) and prove `insert` updates exactly
the queried key. No separate `VecMap.get` loop spec is needed — the relation reads
`vmLastEntry` directly. This is what `agent_cap` (cleared by `insert grantee ∅`) consumes. -/

/-- The boolean key-matcher used by the `VecMap` find loops. -/
abbrev vmKeyEq {K V : Type} [DecidableEq K] (key : K) : K × V → Bool := fun p => decide (p.1 = key)

/-- A key's resolved entry: the *last* list entry whose key matches (last-match semantics). -/
def vmLastEntry {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K) : Option (K × V) :=
  (l.filter (vmKeyEq key)).getLast?

/-- Appending a fresh `(key, val)` to a list with no prior `key` entry makes `key` resolve to
    `val` and leaves every other key untouched. -/
theorem vmLastEntry_append_nomatch {K V : Type} [DecidableEq K]
    (l : List (K × V)) (key : K) (val : V) (hno : ∀ p ∈ l, p.1 ≠ key) (j : K) :
    vmLastEntry (l ++ [(key, val)]) j = if j = key then some (key, val) else vmLastEntry l j := by
  simp only [vmLastEntry, List.filter_append]
  by_cases hj : j = key
  · subst hj
    have hl : l.filter (fun p => decide (p.1 = j)) = [] :=
      List.filter_eq_nil_iff.mpr (by intro p hp; simpa using hno p hp)
    simp [hl]
  · have hsingle : List.filter (fun p => decide (p.1 = j)) [(key, val)] = [] := by
      simp [Ne.symm hj]
    simp [hsingle, hj]

/-- Overwriting the *last* `key` entry with `(key, val)` makes `key` resolve to `val` and
    leaves every other key untouched. `hmatch`/`hlast` pin `idx` as that last matching entry. -/
theorem vmLastEntry_set_lastmatch {K V : Type} [DecidableEq K]
    (l : List (K × V)) (idx : Nat) (key : K) (val : V)
    (hidx : idx < l.length) (hmatch : (l[idx]).1 = key)
    (hlast : ∀ k, (hk : k < l.length) → idx < k → (l[k]).1 ≠ key) (j : K) :
    vmLastEntry (l.set idx (key, val)) j = if j = key then some (key, val) else vmLastEntry l j := by
  have hset : l.set idx (key, val) = l.take idx ++ (key, val) :: l.drop (idx + 1) := by
    rw [List.set_eq_take_append_cons_drop]; simp [hidx]
  have hl : l = l.take idx ++ l[idx] :: l.drop (idx + 1) := by
    conv_lhs => rw [← List.take_append_drop idx l, List.drop_eq_getElem_cons hidx]
  have hdropno : (l.drop (idx + 1)).filter (vmKeyEq key) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    obtain ⟨n, hn, hpn⟩ := List.getElem_of_mem hp
    rw [List.length_drop] at hn
    have hb : idx + 1 + n < l.length := by omega
    have hpk : p.1 ≠ key := by
      rw [← hpn, List.getElem_drop]; exact hlast _ hb (by omega)
    simp [vmKeyEq, hpk]
  simp only [vmLastEntry]
  by_cases hj : j = key
  · subst hj
    rw [hset, List.filter_append]
    simp [vmKeyEq, hdropno]
  · rw [if_neg hj]
    congr 1
    rw [hset]
    conv_rhs => rw [hl]
    simp only [List.filter_append, List.filter_cons, vmKeyEq, hmatch]
    simp [Ne.symm hj]

/-- Last-match invariant for the `VecMap.insert`/`get` find loop: scanning `[0, iv)`, the
    accumulator `idxv` is either the sentinel `l.length` (no key seen) or the index of the
    last key-match so far (with nothing matching strictly after it within `[0, iv)`). -/
def lastMatchInv {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K) (idxv iv : Nat) : Prop :=
  (idxv = l.length ∧ ∀ k, k < iv → ∀ p, l[k]? = some p → p.1 ≠ key) ∨
  (idxv < l.length ∧ (∃ p, l[idxv]? = some p ∧ p.1 = key) ∧
    ∀ k, idxv < k → k < iv → ∀ p, l[k]? = some p → p.1 ≠ key)

theorem vecMapInsertLoop_spec {K V : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (entries : alloc.vec.Vec (K × V)) (key : K) (idx0 i0 : Usize)
    (hi0 : i0.val ≤ entries.val.length)
    (hInv : lastMatchInv entries.val key idx0.val i0.val) :
    collections.VecMap.insert_loop eqK entries key idx0 i0 ⦃ idx1 =>
      lastMatchInv entries.val key idx1.val entries.val.length ⦄ := by
  unfold collections.VecMap.insert_loop
  apply loop.spec_decr_nat
    (measure := fun p => entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ entries.val.length ∧ lastMatchInv entries.val key p.1.val p.2.val)
  · rintro ⟨idx, i⟩ ⟨hile, hinv⟩
    simp only [collections.VecMap.insert_loop.body]
    split
    case isTrue h =>
      have hlt : i.val < entries.val.length := by scalar_tac
      step as ⟨t, t1, he⟩
      have hget : entries.val[i.val]? = some (t, t1) := by
        rw [List.getElem?_eq_getElem hlt, ← he]
      rw [heq t key]
      step*
      split
      · rename_i hb
        step*
        have ht : t = key := by simpa using hb
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        right
        refine ⟨hlt, ⟨(t, t1), hget, ht⟩, ?_⟩
        intro k hk1 hk2 p hp
        exfalso; omega
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

/-- `VecMap.insert vm key val` updates `key` to resolve to `val` (last-match overwrite or
    append) and leaves every other key's resolution unchanged. The get-style spec that
    survives duplicate keys; consumed by `agent_cap` (cleared via `insert grantee ∅`). -/
theorem vecMapInsert_vmLast_spec {K V : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneV : core.clone.Clone V)
    (vm : collections.VecMap K V) (key : K) (val : V)
    (hcap : vm.entries.val.length < Usize.max) :
    collections.VecMap.insert cloneK eqK cloneV vm key val ⦃ vm' =>
      ∀ j, vmLastEntry vm'.entries.val j =
        if j = key then some (key, val) else vmLastEntry vm.entries.val j ⦄ := by
  unfold collections.VecMap.insert
  have hinv0 : lastMatchInv vm.entries.val key (alloc.vec.Vec.len vm.entries).val (0#usize).val := by
    left
    refine ⟨by scalar_tac, ?_⟩
    intro k hk
    exact absurd hk (by scalar_tac)
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (vecMapInsertLoop_spec eqK heq vm.entries key (alloc.vec.Vec.len vm.entries) 0#usize
      (by scalar_tac) hinv0)
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < vm.entries.val.length := by scalar_tac
    rcases hlmi with ⟨hlen, _⟩ | ⟨_, hex, hno⟩
    · omega
    · obtain ⟨p, hp, hpk⟩ := hex
      step*
      have hm : (↑vm.entries : List (K × V))[idx1.val] = p := by
        rw [List.getElem?_eq_getElem hidxlt] at hp; exact Option.some_inj.mp hp
      have hmatch : ((↑vm.entries : List (K × V))[idx1.val]).1 = key := by rw [hm]; exact hpk
      have hlast : ∀ k, (hk : k < (↑vm.entries : List (K × V)).length) → idx1.val < k →
          ((↑vm.entries : List (K × V))[k]).1 ≠ key := by
        intro k hk hik
        exact hno k hik hk _ (List.getElem?_eq_getElem hk)
      intro j
      rw [__post2, alloc.vec.Vec.set_val_eq]
      exact vmLastEntry_set_lastmatch _ idx1.val key val hidxlt hmatch hlast j
  case isFalse hcond =>
    have hidxlen : idx1.val = vm.entries.val.length := by
      rcases hlmi with ⟨hlen, _⟩ | ⟨hlt, _, _⟩
      · exact hlen
      · scalar_tac
    step*
    have hno : ∀ p ∈ (↑vm.entries : List (K × V)), p.1 ≠ key := by
      rcases hlmi with ⟨_, h⟩ | ⟨hlt, _, _⟩
      · intro p hp
        obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
        exact h k hk p (by rw [List.getElem?_eq_getElem hk, hkp])
      · omega
    intro j
    rw [v_post]
    exact vmLastEntry_append_nomatch _ key val hno j

end ArgusLean.Refinement
