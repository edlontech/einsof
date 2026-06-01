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

end ArgusLean.Refinement
