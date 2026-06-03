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

/-- `InvocationId.eq` inherits faithful decidable equality from `String.eq`. -/
@[simp] theorem invocationId_eq_spec (a b : types.InvocationId) :
    types.InvocationId.Insts.CoreCmpPartialEqInvocationId.eq a b = .ok (decide (a = b)) := by
  unfold types.InvocationId.Insts.CoreCmpPartialEqInvocationId.eq
  exact string_eq_spec a b

/-- `InvocationId.clone` is the identity. -/
@[simp] theorem invocationId_clone_spec (a : types.InvocationId) :
    types.InvocationId.Insts.CoreCloneClone.clone a = .ok a := by
  simp only [types.InvocationId.Insts.CoreCloneClone.clone, string_clone_spec, bind_tc_ok]

/-! ## `CapKind` equality / clone

Unlike the `String`-backed ids, `CapKind` is a concrete nullary enum: its extracted `eq` is a
discriminant comparison and its `clone` is the identity, so both specs are *proved* (no extractor
trust). Consumed by the `agent_cap` set operations (`set_contains` / `insert_into`). -/

deriving instance DecidableEq for capability.CapKind

/-- `CapKind.eq` is faithful decidable equality (discriminant comparison on a nullary enum). -/
@[simp] theorem capKind_eq_spec (a b : capability.CapKind) :
    capability.CapKind.Insts.CoreCmpPartialEqCapKind.eq a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp [capability.CapKind.Insts.CoreCmpPartialEqCapKind.eq, capability.CapKind.read_discriminant]

/-- `CapKind.clone` is the identity. -/
@[simp] theorem capKind_clone_spec (a : capability.CapKind) :
    capability.CapKind.Insts.CoreCloneClone.clone a = .ok a := rfl

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
         simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
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

/-! ## `agent_parent_drop_endpoint` bridging

`agent_parent` is a `VecMap AgentId AgentId` carrying a *functional* parent edge, so its
get-style reading needs the keys to be unique. The extracted `agent_parent_drop_endpoint`
rebuilds the map from an empty `VecMap` via `VecMap.insert`, so (a) its output keys are unique
by construction and (b) under a unique-key *input* every insert lands on a fresh key, i.e. is an
append — making the output exactly the input filtered to entries whose child and parent both
differ from the dropped agent. These two pure lemmas are the only place key-uniqueness is used;
they discharge, in a real proof, the deferral the Plausible harness pinned to `Nodup`. -/

/-- In a `Nodup` list the element at index `i` cannot occur earlier: it is the head of the
    suffix `drop i`, which is disjoint from the prefix `take i`. The freshness fact that turns
    each rebuild insert into an append. -/
theorem getElem_not_mem_take {α : Type} {xs : List α} (h : xs.Nodup)
    {i : Nat} (hi : i < xs.length) : xs[i] ∉ xs.take i := by
  have hND : (xs.take i ++ xs.drop i).Nodup := by rw [List.take_append_drop]; exact h
  have hdisj := (List.nodup_append.mp hND).2.2
  have hmem : xs[i] ∈ xs.drop i := by
    rw [List.drop_eq_getElem_cons hi]; exact List.mem_cons_self
  exact fun hmt => hdisj _ hmt _ hmem rfl

/-- Under unique keys the get-style `vmLastEntry` read coincides with plain membership: the last
    (hence only) `C`-keyed entry is `some (C, P)` exactly when `(C, P)` is in the list. The bridge
    that turns the get-style `agent_parent` clause into the membership facts the rewrite produces. -/
theorem vmLastEntry_nodup {K V : Type} [DecidableEq K] (l : List (K × V)) (C : K) (P : V)
    (hnd : (l.map Prod.fst).Nodup) :
    vmLastEntry l C = some (C, P) ↔ (C, P) ∈ l := by
  induction l with
  | nil => simp [vmLastEntry]
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hknotin, hndtl⟩ := hnd
    have hfilcons : ((k, v) :: tl).filter (vmKeyEq C) =
        if k = C then (k, v) :: tl.filter (vmKeyEq C) else tl.filter (vmKeyEq C) := by
      by_cases hk : k = C <;> simp [vmKeyEq, hk]
    simp only [vmLastEntry] at ih ⊢
    rw [hfilcons]
    by_cases hk : k = C
    · subst hk
      have htlfil : tl.filter (vmKeyEq k) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro p hp
        simp only [vmKeyEq, decide_eq_true_eq]
        exact fun hpk => hknotin (hpk ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hnotin' : (k, P) ∉ tl := fun hw => hknotin (List.mem_map.mpr ⟨(k, P), hw, rfl⟩)
      rw [if_pos rfl, htlfil, List.getLast?_singleton, List.mem_cons]
      grind
    · rw [if_neg hk, ih hndtl, List.mem_cons]
      have hne : (C, P) ≠ (k, v) := fun h => hk (congrArg Prod.fst h).symm
      grind

/-- `VecMap.insert` on a key absent from the map appends `(key, val)`. The list-level form the
    rebuild needs: starting from an empty map (and under unique input keys), every insert lands
    on a fresh key, so the rebuilt list is exactly the kept entries in order. -/
theorem vecMapInsert_append_spec {K V : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneV : core.clone.Clone V)
    (vm : collections.VecMap K V) (key : K) (val : V)
    (hcap : vm.entries.val.length < Usize.max)
    (habsent : ∀ p ∈ vm.entries.val, p.1 ≠ key) :
    collections.VecMap.insert cloneK eqK cloneV vm key val ⦃ vm' =>
      vm'.entries.val = vm.entries.val ++ [(key, val)] ⦄ := by
  unfold collections.VecMap.insert
  have hinv0 : lastMatchInv vm.entries.val key (alloc.vec.Vec.len vm.entries).val (0#usize).val := by
    left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (vecMapInsertLoop_spec eqK heq vm.entries key (alloc.vec.Vec.len vm.entries) 0#usize
      (by scalar_tac) hinv0)
  simp only [hloopEq, bind_tc_ok]
  have hidxlen : idx1.val = vm.entries.val.length := by
    rcases hlmi with ⟨hlen, _⟩ | ⟨_, ⟨p, hp, hpk⟩, _⟩
    · exact hlen
    · obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hp
      exact absurd hpk (habsent p (h2 ▸ List.getElem_mem h1))
  split
  case isTrue hcond =>
    exfalso
    have hlt : idx1.val < vm.entries.val.length := by scalar_tac
    omega
  case isFalse hcond =>
    step*

/-- The boolean "keep this edge" matcher of `agent_parent_drop_endpoint`: neither the child
    (key) nor the parent (value) is the dropped agent. -/
abbrev parentKept {K : Type} [DecidableEq K] (dropped : K) : K × K → Bool :=
  fun p => decide (p.1 ≠ dropped ∧ p.2 ≠ dropped)

/-- `VecMap.key_at self i` reads the `i`-th entry's key. -/
theorem vecMapKeyAt_spec {K V : Type}
    (cK : core.clone.Clone K) (eK : core.cmp.PartialEq K K) (cV : core.clone.Clone V)
    (self : collections.VecMap K V) (i : Usize) (hi : i.val < self.entries.val.length) :
    collections.VecMap.key_at cK eK cV self i ⦃ k => k = (self.entries.val[i.val]'hi).1 ⦄ := by
  unfold collections.VecMap.key_at
  step as ⟨t, t1, he⟩
  simp [← he]

/-- `VecMap.val_at self i` reads the `i`-th entry's value. -/
theorem vecMapValAt_spec {K V : Type}
    (cK : core.clone.Clone K) (eK : core.cmp.PartialEq K K) (cV : core.clone.Clone V)
    (self : collections.VecMap K V) (i : Usize) (hi : i.val < self.entries.val.length) :
    collections.VecMap.val_at cK eK cV self i ⦃ v => v = (self.entries.val[i.val]'hi).2 ⦄ := by
  unfold collections.VecMap.val_at
  step as ⟨t, t1, he⟩
  simp [← he]

/-- The key at index `i` of a unique-keyed pair list does not occur among the keys of the prefix
    `take i`. Specialises `getElem_not_mem_take` to the projected key list. -/
theorem fst_getElem_not_mem_map_take {α β : Type} (l : List (α × β)) (i : Nat) (hi : i < l.length)
    (hnd : (l.map Prod.fst).Nodup) : (l[i]'hi).1 ∉ (l.take i).map Prod.fst := by
  have h1 : (l.map Prod.fst)[i]'(by simpa using hi) ∉ (l.map Prod.fst).take i :=
    getElem_not_mem_take hnd (by simpa using hi)
  rw [List.getElem_map] at h1
  rwa [← List.map_take] at h1

set_option maxRecDepth 8000 in
/-- Loop spec for `agent_parent_drop_endpoint`. With the accumulator already holding the kept
    entries of the scanned prefix, the loop returns the kept entries of the whole list. Unique
    input keys make every rebuild insert land on a fresh key (an append), so the accumulator
    stays exactly the filtered prefix. -/
theorem agentParentDropEndpointLoop_spec
    (map : collections.VecMap types.AgentId types.AgentId) (dropped : types.AgentId)
    (hnd : (map.entries.val.map Prod.fst).Nodup)
    (kept : collections.VecMap types.AgentId types.AgentId) (i0 : Usize)
    (hi0 : i0.val ≤ map.entries.val.length)
    (hkept0 : kept.entries.val = (map.entries.val.take i0.val).filter (parentKept dropped)) :
    transitions.agent_parent_drop_endpoint_loop map dropped kept i0 ⦃ out =>
      out.entries.val = map.entries.val.filter (parentKept dropped) ⦄ := by
  unfold transitions.agent_parent_drop_endpoint_loop
  apply loop.spec_decr_nat
    (measure := fun p => map.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ map.entries.val.length ∧
        p.1.entries.val = (map.entries.val.take p.2.val).filter (parentKept dropped))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [transitions.agent_parent_drop_endpoint_loop.body, collections.VecMap.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < map.entries.val.length := by scalar_tac
      obtain ⟨child, hchildEq, hchild⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone
          map i hlt)
      rw [hchildEq]; simp only [bind_tc_ok]
      obtain ⟨parent, hparentEq, hparent⟩ := spec_imp_exists
        (vecMapValAt_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone
          map i hlt)
      rw [hparentEq]; simp only [bind_tc_ok]
      have hcapk : kept.entries.val.length < Usize.max := by
        have hle : kept.entries.val.length ≤ i.val := by
          rw [hkept]
          refine le_trans (List.length_filter_le _ _) ?_
          rw [List.length_take]; exact Nat.min_le_left _ _
        scalar_tac
      have hfresh : ∀ p ∈ kept.entries.val, p.1 ≠ child := by
        have hfm := fst_getElem_not_mem_map_take map.entries.val i.val hlt hnd
        rw [hkept]; intro p hp hpc
        exact hfm (by rw [← hchild, ← hpc]; exact List.mem_map.mpr ⟨p, List.mem_of_mem_filter hp, rfl⟩)
      have hpair : map.entries.val[i.val]'hlt = (child, parent) := by
        cases hpx : map.entries.val[i.val]'hlt with
        | mk a b => simp_all
      have hget : map.entries.val[i.val]? = some (child, parent) := by
        rw [List.getElem?_eq_getElem hlt, hpair]
      clear hpair hchild hparent
      simp only [core.cmp.impls.PartialEqShared.ne]
      rw [agentId_ne_spec child dropped]
      step*
      split
      · rename_i hbo
        rw [agentId_ne_spec parent dropped]
        step*
        split
        · rename_i hbi
          simp only [agentId_clone_spec, bind_tc_ok]
          obtain ⟨kept1, hkept1Eq, hkept1⟩ := spec_imp_exists
            (vecMapInsert_append_spec types.AgentId.Insts.CoreCloneClone
              types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
              types.AgentId.Insts.CoreCloneClone kept child parent hcapk hfresh)
          rw [hkept1Eq]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hkept1, i2_post, List.take_add_one, hget, Option.toList_some]
          have hcd : child ≠ dropped := decide_eq_true_eq.mp hbo
          have hpd : parent ≠ dropped := decide_eq_true_eq.mp hbi
          have hpk : parentKept dropped (child, parent) = true := by simp [parentKept, hcd, hpd]
          simp [List.filter_append, hpk, ← hkept]
        · rename_i hbi
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [i2_post, List.take_add_one, hget, Option.toList_some]
          have hpd : parent = dropped := not_not.mp (fun hc => hbi (decide_eq_true_eq.mpr hc))
          have hpk : parentKept dropped (child, parent) = false := by simp [parentKept, hpd]
          simp [List.filter_append, hpk, ← hkept]
      · rename_i hbo
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [i2_post, List.take_add_one, hget, Option.toList_some]
        have hcd : child = dropped := not_not.mp (fun hc => hbo (decide_eq_true_eq.mpr hc))
        have hpk : parentKept dropped (child, parent) = false := by simp [parentKept, hcd]
        simp [List.filter_append, hpk, ← hkept]
    case isFalse h =>
      have heq' : i.val = map.entries.val.length := by scalar_tac
      simp only [spec_ok]
      simpa [heq', List.take_length] using hkept
  · exact ⟨hi0, hkept0⟩

/-- `agent_parent_drop_endpoint map dropped` returns the entries of `map` whose child and parent
    both differ from `dropped`, in order — provided `map` has unique keys. -/
theorem agentParentDropEndpoint_spec
    (map : collections.VecMap types.AgentId types.AgentId) (dropped : types.AgentId)
    (hnd : (map.entries.val.map Prod.fst).Nodup) :
    transitions.agent_parent_drop_endpoint map dropped ⦃ out =>
      out.entries.val = map.entries.val.filter (parentKept dropped) ⦄ := by
  unfold transitions.agent_parent_drop_endpoint
  simp only [collections.VecMap.new, bind_tc_ok]
  exact agentParentDropEndpointLoop_spec map dropped hnd _ 0#usize (by scalar_tac) (by simp)

/-- The get-style read of the `delegate` `agent_parent` post-state — the kept (filtered) edges
    followed by the fresh `(grantee, grantor)` edge — matches the abstract post-image exactly,
    provided the pre-state keys are unique. This is the proven form of the clause the Plausible
    harness pinned to `Nodup`. -/
theorem parentPost_vmLast {K : Type} [DecidableEq K] (l : List (K × K)) (grantee grantor C P : K)
    (hnd : (l.map Prod.fst).Nodup) :
    vmLastEntry (l.filter (parentKept grantee) ++ [(grantee, grantor)]) C = some (C, P) ↔
      (C = grantee ∧ P = grantor) ∨
        (vmLastEntry l C = some (C, P) ∧ C ≠ grantee ∧ P ≠ grantee) := by
  have hno : ∀ p ∈ l.filter (parentKept grantee), p.1 ≠ grantee := by
    intro p hp
    have hp' := List.mem_filter.mp hp
    simp only [parentKept, decide_eq_true_eq] at hp'
    exact hp'.2.1
  have hfnd : ((l.filter (parentKept grantee)).map Prod.fst).Nodup := by
    have hs : List.Sublist (l.filter (parentKept grantee)) l := List.filter_sublist
    exact List.Nodup.sublist (List.Sublist.map Prod.fst hs) hnd
  rw [vmLastEntry_append_nomatch _ grantee grantor hno C]
  by_cases hC : C = grantee
  · subst hC
    grind
  · rw [if_neg hC, vmLastEntry_nodup _ C P hfnd, vmLastEntry_nodup _ C P hnd, List.mem_filter]
    simp only [parentKept, decide_eq_true_eq]
    grind

/-- The `delegate` `agent_parent` post-state keeps unique keys: the kept (filtered) edges inherit
    uniqueness from the pre-state, and the fresh key `grantee` was filtered out. Re-establishes the
    `vmNodupKeys` invariant after the rewrite. -/
theorem parentPost_nodupKeys {K : Type} [DecidableEq K] (l : List (K × K)) (grantee grantor : K)
    (hnd : (l.map Prod.fst).Nodup) :
    ((l.filter (parentKept grantee) ++ [(grantee, grantor)]).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · have hs : List.Sublist (l.filter (parentKept grantee)) l := List.filter_sublist
    exact List.Nodup.sublist (List.Sublist.map Prod.fst hs) hnd
  · intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp ha
    have hp' := List.mem_filter.mp hp
    simp only [parentKept, decide_eq_true_eq] at hp'
    rw [← hpe]; exact hp'.2.1

/-! ## `cascade_revoke` / `revoke` bridging: parent-edge get, set-remove, drop-child

`cascade_revoke child parent` and `revoke parent target` both (a) gate on the parent edge via
`VecMap.get`, (b) remove the agent from the `agent_active` `VecSet`, (c) rebuild `agent_parent`
via `agent_parent_drop_child` (a pure key-filter — no re-appended edge, unlike `drop_endpoint`),
and (d) `VecMap.remove` the agent's caps. The lemmas below are the bridging those need; they are
shared between the two removal actions. -/

/-- The opaque extracted `Option AgentId` disequality is faithful decidable disequality. Same
    extractor-residual status as `agentId_ne_spec`: `PartialEq::ne` is a default trait method,
    so Charon emits the per-type `…ne` as a bare axiom. Consumed by the parent-edge gate of
    `revoke` / `cascade_revoke` (and later `grant_capability`). -/
axiom optionAgentId_ne_spec (o1 o2 : Option types.AgentId) :
    core.option.Option.Insts.CoreCmpPartialEqOption.ne
      (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId) o1 o2
      = .ok (decide (o1 ≠ o2))

/-- A present last-match entry is keyed by the queried key (it came out of the key-filter). -/
theorem vmLastEntry_fst {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K) (p : K × V)
    (h : vmLastEntry l key = some p) : p.1 = key := by
  have hmem : p ∈ l.filter (vmKeyEq key) := List.mem_of_getLast? h
  have h2 := (List.mem_filter.mp hmem).2
  simpa [vmKeyEq] using h2

/-- No `key`-entry anywhere ⇒ the last-match read is `none`. -/
theorem vmLastEntry_eq_none {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K)
    (hno : ∀ p ∈ l, p.1 ≠ key) : vmLastEntry l key = none := by
  unfold vmLastEntry
  rw [List.filter_eq_nil_iff.mpr (by intro p hp; simp [vmKeyEq, hno p hp])]
  rfl

/-- If `idx` is the last `key`-matching index then the last-match read is its entry. Mirrors the
    `hdropno` reasoning of `vmLastEntry_set_lastmatch`: the suffix past `idx` has no `key`-match,
    so the key-filter ends in `l[idx]`. -/
theorem vmLastEntry_eq_of_isLast {K V : Type} [DecidableEq K] (l : List (K × V)) (idx : Nat)
    (key : K) (hidx : idx < l.length) (hmatch : (l[idx]'hidx).1 = key)
    (hlast : ∀ k, (hk : k < l.length) → idx < k → (l[k]'hk).1 ≠ key) :
    vmLastEntry l key = some (l[idx]'hidx) := by
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
  have hmatchb : vmKeyEq key (l[idx]'hidx) = true := by simp [vmKeyEq, hmatch]
  unfold vmLastEntry
  conv_lhs => rw [hl]
  rw [List.filter_append, List.filter_cons, hmatchb, if_pos rfl, hdropno]
  rw [List.getLast?_append]
  simp

/-- The last-match read through the `VecMap.remove` / `agent_parent_drop_child` key-filter: the
    removed key resolves to `none`, every other key is untouched (filtering a *different* key
    preserves the last matching entry, with or without duplicate keys). -/
theorem vmLastEntry_filter_removeKept {K V : Type} [DecidableEq K] (l : List (K × V)) (key N : K) :
    vmLastEntry (l.filter (removeKept key)) N =
      if N = key then none else vmLastEntry l N := by
  by_cases hN : N = key
  · subst hN
    rw [if_pos rfl]
    apply vmLastEntry_eq_none
    intro p hp hpN
    have h2 := (List.mem_filter.mp hp).2
    simp [removeKept, hpN] at h2
  · rw [if_neg hN]
    unfold vmLastEntry
    congr 1
    rw [List.filter_filter]
    apply List.filter_congr
    intro p _
    by_cases hp : p.1 = N
    · simp [vmKeyEq, removeKept, hp, hN]
    · simp [vmKeyEq, hp]

/-! ### `VecMap.get` (last-match read) -/

/-- Find-index loop for `VecMap.get`: identical body to `insert_loop`, so it carries the same
    `lastMatchInv` (the accumulator is the last key-match seen, sentinel `len` if none). -/
theorem vecMapGetLoop_spec {K V : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (entries : alloc.vec.Vec (K × V)) (key : K) (idx0 i0 : Usize)
    (hi0 : i0.val ≤ entries.val.length)
    (hInv : lastMatchInv entries.val key idx0.val i0.val) :
    collections.VecMap.get_loop eqK entries key idx0 i0 ⦃ idx1 =>
      lastMatchInv entries.val key idx1.val entries.val.length ⦄ := by
  unfold collections.VecMap.get_loop
  apply loop.spec_decr_nat
    (measure := fun p => entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ entries.val.length ∧ lastMatchInv entries.val key p.1.val p.2.val)
  · rintro ⟨idx, i⟩ ⟨hile, hinv⟩
    simp only [collections.VecMap.get_loop.body]
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

/-- `VecMap.get vm key` returns the value of the last `key`-keyed entry (last-match semantics),
    expressed as `(vmLastEntry …).map Prod.snd`. The get-style bridge for the parent-edge gate. -/
theorem vecMapGet_spec {K V : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneV : core.clone.Clone V)
    (vm : collections.VecMap K V) (key : K) :
    collections.VecMap.get cloneK eqK cloneV vm key ⦃ o =>
      o = (vmLastEntry vm.entries.val key).map Prod.snd ⦄ := by
  unfold collections.VecMap.get
  have hinv0 : lastMatchInv vm.entries.val key (alloc.vec.Vec.len vm.entries).val (0#usize).val := by
    left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (vecMapGetLoop_spec eqK heq vm.entries key (alloc.vec.Vec.len vm.entries) 0#usize
      (by scalar_tac) hinv0)
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < vm.entries.val.length := by scalar_tac
    rcases hlmi with ⟨hlen, _⟩ | ⟨_, ⟨p, hp, hpk⟩, hno⟩
    · omega
    · have hpe : vm.entries.val[idx1.val]'hidxlt = p := by
        rw [List.getElem?_eq_getElem hidxlt] at hp; exact Option.some_inj.mp hp
      have hmatch : (vm.entries.val[idx1.val]'hidxlt).1 = key := by rw [hpe]; exact hpk
      have hlast : ∀ k, (hk : k < vm.entries.val.length) → idx1.val < k →
          (vm.entries.val[k]'hk).1 ≠ key := fun k hk hik =>
        hno k hik hk _ (List.getElem?_eq_getElem hk)
      step as ⟨k0, v0, he⟩
      rw [vmLastEntry_eq_of_isLast vm.entries.val idx1.val key hidxlt hmatch hlast]
      simp only [Option.map_some, ← he]
  case isFalse hcond =>
    have hidxlen : idx1.val = vm.entries.val.length := by
      rcases hlmi with ⟨hlen, _⟩ | ⟨hlt, _, _⟩
      · exact hlen
      · scalar_tac
    have hno : ∀ p ∈ vm.entries.val, p.1 ≠ key := by
      rcases hlmi with ⟨_, h⟩ | ⟨hlt, _, _⟩
      · intro p hp
        obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
        exact h k (by omega) p (by rw [List.getElem?_eq_getElem hk, hkp])
      · omega
    rw [vmLastEntry_eq_none vm.entries.val key hno]
    rfl

/-! ### `VecSet.remove` -/

/-- Predicate kept by `VecSet.remove`: the element is not the removed one. A folded abbrev
    (like `removeKept`) so the running-filter accumulator survives `simp` rewrites intact. -/
abbrev setRemoveKept {T : Type} [DecidableEq T] (x : T) : T → Bool := fun t => decide (t ≠ x)

/-- Loop spec for `VecSet.remove_loop`: the accumulator is the running filter (keep `≠ x`).
    Mirrors `vecMapRemoveLoop_spec`; the element clone (`hclone`) is the identity. -/
theorem vecSetRemoveLoop_spec {T : Type} [DecidableEq T]
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (hne : ∀ a b : T, eqT.ne a b = .ok (decide (a ≠ b)))
    (hclone : ∀ t : T, cloneT.clone t = .ok t)
    (self : collections.VecSet T) (x : T)
    (kept0 : alloc.vec.Vec T) (i0 : Usize)
    (hi0 : i0.val ≤ self.items.val.length)
    (hkept0 : kept0.val = (self.items.val.take i0.val).filter (setRemoveKept x)) :
    collections.VecSet.remove_loop cloneT eqT self x kept0 i0 ⦃ kept =>
      kept.val = self.items.val.filter (setRemoveKept x) ⦄ := by
  unfold collections.VecSet.remove_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.items.val.length ∧
        p.1.val = (self.items.val.take p.2.val).filter (setRemoveKept x))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [collections.VecSet.remove_loop.body]
    split
    case isTrue h =>
      have hlt : i.val < self.items.val.length := by scalar_tac
      step as ⟨t, he⟩
      have hget : self.items.val[i.val]? = some t := by
        rw [List.getElem?_eq_getElem hlt, ← he]
      have hcapk : kept.val.length < Usize.max := by
        have h1 : kept.val.length ≤ i.val := by
          rw [hkept]
          exact le_trans (List.length_filter_le _ _)
            (by rw [List.length_take]; exact Nat.min_le_left _ _)
        scalar_tac
      rw [hne t x]
      step*
      split
      · rename_i hb
        rw [hclone t]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [kept1_post, i2_post, List.take_add_one, hget, Option.toList_some]
        simp [List.filter_append, setRemoveKept, hb, ← hkept]
      · rename_i hb
        step*
        have hbf : decide (t ≠ x) = false := by simpa using hb
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [i2_post, List.take_add_one, hget, Option.toList_some]
        simp [List.filter_append, setRemoveKept, hbf, ← hkept]
    case isFalse h =>
      have heq' : i.val = self.items.val.length := by scalar_tac
      simp only [spec_ok]
      simpa [heq', List.take_length] using hkept
  · exact ⟨hi0, hkept0⟩

/-- `VecSet.remove self x` returns the `≠ x`-filtered items; hence membership drops exactly `x`. -/
theorem vecSetRemove_spec {T : Type} [DecidableEq T]
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (hne : ∀ a b : T, eqT.ne a b = .ok (decide (a ≠ b)))
    (hclone : ∀ t : T, cloneT.clone t = .ok t)
    (self : collections.VecSet T) (x : T) :
    collections.VecSet.remove cloneT eqT self x ⦃ vs' =>
      ∀ y, vsMem vs' y ↔ vsMem self y ∧ y ≠ x ⦄ := by
  unfold collections.VecSet.remove
  obtain ⟨kept, hkeptEq, hkeptMem⟩ :=
    spec_imp_exists (vecSetRemoveLoop_spec cloneT eqT hne hclone self x
      ⟨[], by simp⟩ 0#usize (by simp) (by simp))
  rw [hkeptEq]
  intro y
  simp only [vsMem, hkeptMem, List.mem_filter, setRemoveKept, decide_eq_true_eq]

/-! ### `agent_parent_drop_child` (pure key-filter rebuild)

Unlike `agent_parent_drop_endpoint`, `drop_child` only inspects each entry's *key*: it keeps the
edge iff the child differs from the dropped agent. So under unique input keys the rebuild is the
plain `removeKept`-filter (no re-appended edge). -/

set_option maxRecDepth 8000 in
theorem agentParentDropChildLoop_spec
    (map : collections.VecMap types.AgentId types.AgentId) (dropped : types.AgentId)
    (hnd : (map.entries.val.map Prod.fst).Nodup)
    (kept : collections.VecMap types.AgentId types.AgentId) (i0 : Usize)
    (hi0 : i0.val ≤ map.entries.val.length)
    (hkept0 : kept.entries.val = (map.entries.val.take i0.val).filter (removeKept dropped)) :
    transitions.agent_parent_drop_child_loop map dropped kept i0 ⦃ out =>
      out.entries.val = map.entries.val.filter (removeKept dropped) ⦄ := by
  unfold transitions.agent_parent_drop_child_loop
  apply loop.spec_decr_nat
    (measure := fun p => map.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ map.entries.val.length ∧
        p.1.entries.val = (map.entries.val.take p.2.val).filter (removeKept dropped))
  · rintro ⟨kept, i⟩ ⟨hile, hkept⟩
    simp only [transitions.agent_parent_drop_child_loop.body, collections.VecMap.len,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < map.entries.val.length := by scalar_tac
      obtain ⟨child, hchildEq, hchild⟩ := spec_imp_exists
        (vecMapKeyAt_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone
          map i hlt)
      rw [hchildEq]; simp only [bind_tc_ok]
      have hcapk : kept.entries.val.length < Usize.max := by
        have hle : kept.entries.val.length ≤ i.val := by
          rw [hkept]
          refine le_trans (List.length_filter_le _ _) ?_
          rw [List.length_take]; exact Nat.min_le_left _ _
        scalar_tac
      have hfresh : ∀ p ∈ kept.entries.val, p.1 ≠ child := by
        have hfm := fst_getElem_not_mem_map_take map.entries.val i.val hlt hnd
        rw [hkept]; intro p hp hpc
        exact hfm (by rw [← hchild, ← hpc]; exact List.mem_map.mpr ⟨p, List.mem_of_mem_filter hp, rfl⟩)
      simp only [core.cmp.impls.PartialEqShared.ne]
      rw [agentId_ne_spec child dropped]
      step*
      split
      · rename_i hbo
        simp only [agentId_clone_spec, bind_tc_ok]
        obtain ⟨parent, hparentEq, hparent⟩ := spec_imp_exists
          (vecMapValAt_spec types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId types.AgentId.Insts.CoreCloneClone
            map i hlt)
        rw [hparentEq]; simp only [bind_tc_ok]
        obtain ⟨kept1, hkept1Eq, hkept1⟩ := spec_imp_exists
          (vecMapInsert_append_spec types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
            types.AgentId.Insts.CoreCloneClone kept child parent hcapk hfresh)
        rw [hkept1Eq]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hpair : map.entries.val[i.val]'hlt = (child, parent) := by
          cases hpx : map.entries.val[i.val]'hlt with
          | mk a b => simp_all
        have hget : map.entries.val[i.val]? = some (child, parent) := by
          rw [List.getElem?_eq_getElem hlt, hpair]
        rw [hkept1, i2_post, List.take_add_one, hget, Option.toList_some]
        have hcd : child ≠ dropped := decide_eq_true_eq.mp hbo
        have hpk : removeKept dropped (child, parent) = true := by simp [removeKept, hcd]
        simp [List.filter_append, hpk, ← hkept]
      · rename_i hbo
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have hget : map.entries.val[i.val]? = some (map.entries.val[i.val]'hlt) :=
          List.getElem?_eq_getElem hlt
        have hcd : child = dropped := not_not.mp (fun hc => hbo (decide_eq_true_eq.mpr hc))
        have hpk : removeKept dropped (map.entries.val[i.val]'hlt) = false := by
          simp only [removeKept, ← hchild, hcd, ne_eq, not_true_eq_false, decide_false]
        have hfilt : List.filter (removeKept dropped) [map.entries.val[i.val]'hlt] = [] := by
          simp [hpk]
        rw [i2_post, List.take_add_one, hget, Option.toList_some, List.filter_append, ← hkept,
          hfilt, List.append_nil]
    case isFalse h =>
      have heq' : i.val = map.entries.val.length := by scalar_tac
      simp only [spec_ok]
      simpa [heq', List.take_length] using hkept
  · exact ⟨hi0, hkept0⟩

/-- `agent_parent_drop_child map dropped` returns the entries of `map` whose *key* differs from
    `dropped`, in order — provided `map` has unique keys. -/
theorem agentParentDropChild_spec
    (map : collections.VecMap types.AgentId types.AgentId) (dropped : types.AgentId)
    (hnd : (map.entries.val.map Prod.fst).Nodup) :
    transitions.agent_parent_drop_child map dropped ⦃ out =>
      out.entries.val = map.entries.val.filter (removeKept dropped) ⦄ := by
  unfold transitions.agent_parent_drop_child
  simp only [collections.VecMap.new, bind_tc_ok]
  exact agentParentDropChildLoop_spec map dropped hnd _ 0#usize (by scalar_tac) (by simp)

/-! ### `VecMap.get_cloned` + `VecMapKVecSet.set_contains`

`set_contains key elem` reads the (cloned) last-match set under `key` and tests membership. The
`get_cloned` find-loop is again the same body as `insert_loop`, so it reuses `lastMatchInv`; the
value clone is the identity. We only need the *forward* direction for the `grant_capability` cap
gate: a `true` result witnesses a `key`-entry whose set holds `elem`, i.e. nested membership. -/

/-- A present last-match entry is a member of the underlying list. -/
theorem vmLastEntry_mem {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K) (p : K × V)
    (h : vmLastEntry l key = some p) : p ∈ l :=
  List.mem_of_mem_filter (List.mem_of_getLast? h)

/-- Find-index loop for `VecMap.get_cloned`: same `lastMatchInv` as `get_loop`/`insert_loop`. -/
theorem vecMapGetClonedLoop_spec {K V : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (entries : alloc.vec.Vec (K × V)) (key : K) (idx0 i0 : Usize)
    (hi0 : i0.val ≤ entries.val.length)
    (hInv : lastMatchInv entries.val key idx0.val i0.val) :
    collections.VecMap.get_cloned_loop eqK entries key idx0 i0 ⦃ idx1 =>
      lastMatchInv entries.val key idx1.val entries.val.length ⦄ := by
  unfold collections.VecMap.get_cloned_loop
  apply loop.spec_decr_nat
    (measure := fun p => entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ entries.val.length ∧ lastMatchInv entries.val key p.1.val p.2.val)
  · rintro ⟨idx, i⟩ ⟨hile, hinv⟩
    simp only [collections.VecMap.get_cloned_loop.body]
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

/-- `VecMap.get_cloned vm key` returns the (identity-cloned) value of the last `key`-keyed entry. -/
theorem vecMapGetCloned_spec {K V : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneV : core.clone.Clone V) (hcloneV : ∀ v : V, cloneV.clone v = .ok v)
    (vm : collections.VecMap K V) (key : K) :
    collections.VecMap.get_cloned cloneK eqK cloneV vm key ⦃ o =>
      o = (vmLastEntry vm.entries.val key).map Prod.snd ⦄ := by
  unfold collections.VecMap.get_cloned
  have hinv0 : lastMatchInv vm.entries.val key (alloc.vec.Vec.len vm.entries).val (0#usize).val := by
    left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (vecMapGetClonedLoop_spec eqK heq vm.entries key (alloc.vec.Vec.len vm.entries) 0#usize
      (by scalar_tac) hinv0)
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < vm.entries.val.length := by scalar_tac
    rcases hlmi with ⟨hlen, _⟩ | ⟨_, ⟨p, hp, hpk⟩, hno⟩
    · omega
    · have hpe : vm.entries.val[idx1.val]'hidxlt = p := by
        rw [List.getElem?_eq_getElem hidxlt] at hp; exact Option.some_inj.mp hp
      have hmatch : (vm.entries.val[idx1.val]'hidxlt).1 = key := by rw [hpe]; exact hpk
      have hlast : ∀ k, (hk : k < vm.entries.val.length) → idx1.val < k →
          (vm.entries.val[k]'hk).1 ≠ key := fun k hk hik =>
        hno k hik hk _ (List.getElem?_eq_getElem hk)
      step as ⟨k0, v0, he⟩
      rw [hcloneV v0]
      step*
      rw [vmLastEntry_eq_of_isLast vm.entries.val idx1.val key hidxlt hmatch hlast]
      simp only [Option.map_some, ← he]
  case isFalse hcond =>
    have hidxlen : idx1.val = vm.entries.val.length := by
      rcases hlmi with ⟨hlen, _⟩ | ⟨hlt, _, _⟩
      · exact hlen
      · scalar_tac
    have hno : ∀ p ∈ vm.entries.val, p.1 ≠ key := by
      rcases hlmi with ⟨_, h⟩ | ⟨hlt, _, _⟩
      · intro p hp
        obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
        exact h k (by omega) p (by rw [List.getElem?_eq_getElem hk, hkp])
      · omega
    rw [vmLastEntry_eq_none vm.entries.val key hno]
    rfl

/-- `set_contains key elem`, when `true`, witnesses nested membership of `elem` under `key`. The
    forward direction is all the `grant_capability` capability gate needs (no key-uniqueness). -/
theorem vecMapKVecSetSetContains_spec {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (vm : collections.VecMap K (collections.VecSet T)) (key : K) (elem : T) :
    collections.VecMapKVecSet.set_contains cloneK eqK cloneT eqT vm key elem ⦃ b =>
      b = true → vmsMem vm key elem ⦄ := by
  unfold collections.VecMapKVecSet.set_contains
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec cloneK eqK heqK (collections.VecSet.Insts.CoreCloneClone cloneT)
      (vecSetClone_spec cloneT hcloneT) vm key)
  rw [hoEq]
  simp only [bind_tc_ok]
  cases hL : vmLastEntry vm.entries.val key with
  | none =>
    rw [hL] at ho
    simp only [Option.map_none] at ho
    subst ho
    simp
  | some p =>
    rw [hL] at ho
    simp only [Option.map_some] at ho
    subst ho
    show collections.VecSet.contains cloneT eqT p.2 elem ⦃ b => b = true → vmsMem vm key elem ⦄
    obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists (vecSetContains_spec cloneT eqT heqT p.2 elem)
    rw [hbEq]
    intro hb
    have hp1 : p.1 = key := vmLastEntry_fst _ _ _ hL
    refine ⟨p.2, ?_, hbIff.mp hb⟩
    have hpeq : (key, p.2) = p := by rw [← hp1]
    rw [hpeq]
    exact vmLastEntry_mem vm.entries.val key p hL

/-! ## `BudgetLevel` equality / clone

Like `CapKind`, `BudgetLevel` is a concrete nullary enum: extracted `eq` is a discriminant
comparison and `clone` is the identity, so both specs are *proved* (no extractor trust). Consumed
by the budget reads/writes (`budget`, `budget_exhausted`, `debit_budget`) the return actions use. -/

deriving instance DecidableEq for types.BudgetLevel

/-- `BudgetLevel.eq` is faithful decidable equality (discriminant comparison on a nullary enum). -/
@[simp] theorem budgetLevel_eq_spec (a b : types.BudgetLevel) :
    types.BudgetLevel.Insts.CoreCmpPartialEqBudgetLevel.eq a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp [types.BudgetLevel.Insts.CoreCmpPartialEqBudgetLevel.eq, types.BudgetLevel.read_discriminant]

/-- `BudgetLevel.clone` is the identity. -/
@[simp] theorem budgetLevel_clone_spec (a : types.BudgetLevel) :
    types.BudgetLevel.Insts.CoreCloneClone.clone a = .ok a := rfl

/-- `ConfLevel.clone` is the identity (nullary enum, body is `ok self`). -/
@[simp] theorem confLevel_clone_spec (a : types.ConfLevel) :
    types.ConfLevel.Insts.CoreCloneClone.clone a = .ok a := rfl

/-! ## `OverrideEntry` equality / clone

`OverrideEntry` is the `(agent, tool, level)` struct keying `flow_overrides`. Its `eq` is the
field-wise conjunction (`AgentId` then `ToolId` then `ConfLevel`), its `clone` the field-wise
identity. Both reduce to the already-pinned per-field specs — `eq` is *proved* faithful decidable
equality. Consumed by `has_flow_override` (a `VecSet.contains` on `flow_overrides`). -/

deriving instance DecidableEq for types.ConfLevel
deriving instance DecidableEq for types.OverrideEntry

/-- `ConfLevel.eq` faithful decidable equality (nullary enum; needed for `OverrideEntry.eq`). -/
@[simp] theorem confLevel_eq_spec (a b : types.ConfLevel) :
    types.ConfLevel.Insts.CoreCmpPartialEqConfLevel.eq a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp [types.ConfLevel.Insts.CoreCmpPartialEqConfLevel.eq, types.ConfLevel.read_discriminant]

/-- `OverrideEntry.eq` is faithful decidable equality: agent (`String`) then tool (`String`) then
    level (enum). -/
@[simp] theorem overrideEntry_eq_spec (a b : types.OverrideEntry) :
    types.OverrideEntry.Insts.CoreCmpPartialEqOverrideEntry.eq a b = .ok (decide (a = b)) := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [types.OverrideEntry.Insts.CoreCmpPartialEqOverrideEntry.eq, agentId_eq_spec, bind_tc_ok]
  by_cases h1 : a1 = b1
  · subst h1
    simp only [decide_true, reduceIte, toolId_eq_spec]
    by_cases h2 : a2 = b2
    · subst h2; simp [confLevel_eq_spec]
    · simp [h2]
  · simp [h1]

/-- `OverrideEntry.clone` is the identity (field-wise). -/
@[simp] theorem overrideEntry_clone_spec (a : types.OverrideEntry) :
    types.OverrideEntry.Insts.CoreCloneClone.clone a = .ok a := by
  obtain ⟨a1, a2, a3⟩ := a
  simp only [types.OverrideEntry.Insts.CoreCloneClone.clone, agentId_clone_spec, toolId_clone_spec,
    confLevel_clone_spec, bind_tc_ok]

/-! ## `VecSet.is_empty` and last-match nested membership

`set_nonempty` / `get_set_or_empty` (the in-flight / taint reads the return actions perform) all
resolve a key through `VecMap.get_cloned` — i.e. the **last** matching entry — so their faithful
abstract image is the *last-match* nested membership `vmsMemLast`, the get-style counterpart of the
raw-union `vmsMem`. (They coincide when keys are unique; the get-style view needs no key-uniqueness
side condition and is exactly what the kernel's reads compute.) -/

/-- Last-match nested membership: the live (last) `k`-keyed entry's set holds `v`. The get-style
    counterpart of `vmsMem` — what `set_nonempty` / `get_set_or_empty` actually observe. -/
def vmsMemLast {K T : Type} [DecidableEq K]
    (vm : collections.VecMap K (collections.VecSet T)) (k : K) (v : T) : Prop :=
  ∃ vs, vmLastEntry vm.entries.val k = some (k, vs) ∧ v ∈ vs.items.val

/-- `VecSet.is_empty` is faithful emptiness of the underlying list. -/
theorem vecSetIsEmpty_spec {T : Type} (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (vs : collections.VecSet T) :
    collections.VecSet.is_empty cloneT eqT vs ⦃ b => b = true ↔ vs.items.val = [] ⦄ := by
  unfold collections.VecSet.is_empty
  simp only [spec_ok, decide_eq_true_eq]
  rw [← List.length_eq_zero_iff]
  constructor
  · intro h; scalar_tac
  · intro h; scalar_tac

/-- `set_nonempty key`, characterised exactly: it returns `true` iff the live `key`-keyed set holds
    some element (last-match nested membership). The `∀`-negation of the `false` branch is the
    `child`-has-no-in-flight guard the return actions discharge. -/
theorem vecMapKVecSetSetNonempty_spec {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (vm : collections.VecMap K (collections.VecSet T)) (key : K) :
    collections.VecMapKVecSet.set_nonempty cloneK eqK cloneT eqT vm key ⦃ b =>
      b = true ↔ ∃ v, vmsMemLast vm key v ⦄ := by
  unfold collections.VecMapKVecSet.set_nonempty
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec cloneK eqK heqK (collections.VecSet.Insts.CoreCloneClone cloneT)
      (vecSetClone_spec cloneT hcloneT) vm key)
  rw [hoEq]; simp only [bind_tc_ok]
  cases hL : vmLastEntry vm.entries.val key with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho
    simp only [spec_ok, Bool.false_eq_true, false_iff, not_exists]
    rintro v ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
  | some p =>
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    have hp1 : p.1 = key := vmLastEntry_fst _ _ _ hL
    have hLk : vmLastEntry vm.entries.val key = some (key, p.2) := by rw [hL, ← hp1]
    obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists (vecSetIsEmpty_spec cloneT eqT p.2)
    simp only [hbEq, bind_tc_ok, spec_ok, decide_eq_true_eq]
    rw [hbIff]
    constructor
    · intro hne
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨v, p.2, hLk, hv⟩
    · rintro ⟨v, vs, hvs, hv⟩
      rw [hLk, Option.some_inj, Prod.mk.injEq] at hvs
      obtain ⟨_, rfl⟩ := hvs
      exact List.ne_nil_of_mem hv

/-- `get_set_or_empty key` returns the live (last) `key`-keyed set, or the empty set when `key` is
    absent — its membership is exactly `vmsMemLast`. The taint/in-flight reads `return_unendorsed`
    performs. -/
theorem getSetOrEmpty_spec {K T : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (key : K) :
    collections.VecMapKVecSet.get_set_or_empty cloneK eqK cloneT eqT self key ⦃ vs =>
      ∀ v, vsMem vs v ↔ vmsMemLast self key v ⦄ := by
  unfold collections.VecMapKVecSet.get_set_or_empty
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec cloneK eqK heqK (collections.VecSet.Insts.CoreCloneClone cloneT)
      (vecSetClone_spec cloneT hcloneT) self key)
  rw [hoEq]; simp only [bind_tc_ok]
  cases hL : vmLastEntry self.entries.val key with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho
    unfold collections.VecSet.new
    simp only [spec_ok]
    intro v
    simp only [vsMem, List.not_mem_nil, false_iff]
    rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
  | some p =>
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    have hp1 : p.1 = key := vmLastEntry_fst _ _ _ hL
    have hLk : vmLastEntry self.entries.val key = some (key, p.2) := by rw [hL, ← hp1]
    simp only [spec_ok]
    intro v
    constructor
    · intro hv; exact ⟨p.2, hLk, hv⟩
    · rintro ⟨vs, hvs, hv⟩
      rw [hLk, Option.some_inj, Prod.mk.injEq] at hvs
      obtain ⟨_, rfl⟩ := hvs; exact hv

/-- `VecSet.insert` (membership-only) with a length bound: the result gains `x` and grows by at most
    one element. The length bound lets `union_with` track its capacity through the insertion loop. -/
theorem vecSetInsertLen_spec {T : Type} [DecidableEq T]
    (inst_c : core.clone.Clone T) (inst_eq : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst_eq.eq a b = .ok (decide (a = b)))
    (vs : collections.VecSet T) (x : T) (hcap : vs.items.val.length < Usize.max) :
    collections.VecSet.insert inst_c inst_eq vs x ⦃ vs' =>
      (∀ y, vsMem vs' y ↔ vsMem vs y ∨ y = x) ∧
      vs'.items.val.length ≤ vs.items.val.length + 1 ⦄ := by
  unfold collections.VecSet.insert
  obtain ⟨b, hcontains, hb⟩ :=
    spec_imp_exists (vecSetContains_spec inst_c inst_eq heq vs x)
  rw [hcontains]
  cases b with
  | true =>
    have hx : x ∈ vs.items.val := hb.mp rfl
    simp only [bind_tc_ok, reduceIte, spec_ok]
    refine ⟨fun y => ⟨Or.inl, ?_⟩, by omega⟩
    rintro (hy | rfl)
    · exact hy
    · exact hx
  | false =>
    simp only [bind_tc_ok, Bool.false_eq_true, reduceIte]
    step*
    refine ⟨fun y => ?_, ?_⟩
    · simp only [vsMem, v_post, List.mem_append, List.mem_singleton]
    · simp [v_post]

/-- Loop spec for `union_with`: after scanning the prefix `[0, i)` of `other`, the accumulator holds
    `self`'s elements plus that prefix's, and its length is bounded by `self.length + i`. -/
theorem vecSetUnionWithLoop_spec {T : Type} [DecidableEq T]
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self0 other : collections.VecSet T)
    (hcap : self0.items.val.length + other.items.val.length ≤ Usize.max)
    (acc : collections.VecSet T) (i : Usize)
    (hi : i.val ≤ other.items.val.length)
    (hlen : acc.items.val.length ≤ self0.items.val.length + i.val)
    (hmem : ∀ y, vsMem acc y ↔ vsMem self0 y ∨ y ∈ other.items.val.take i.val) :
    collections.VecSet.union_with_loop cloneT eqT acc other i ⦃ vs' =>
      ∀ y, vsMem vs' y ↔ vsMem self0 y ∨ vsMem other y ⦄ := by
  unfold collections.VecSet.union_with_loop
  apply loop.spec_decr_nat
    (measure := fun p => other.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ other.items.val.length ∧
      p.1.items.val.length ≤ self0.items.val.length + p.2.val ∧
      (∀ y, vsMem p.1 y ↔ vsMem self0 y ∨ y ∈ other.items.val.take p.2.val))
  · rintro ⟨accL, iL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL
    simp only [collections.VecSet.union_with_loop.body, alloc.vec.Vec.len]
    split
    case isTrue h =>
      have hlt : iL.val < other.items.val.length := by scalar_tac
      step as ⟨t, he⟩
      have hcapL : accL.items.val.length < Usize.max := by scalar_tac
      rw [hcloneT t]
      obtain ⟨vs1, hvs1Eq, hvs1Mem, hvs1Len⟩ :=
        spec_imp_exists (vecSetInsertLen_spec cloneT eqT heqT accL t hcapL)
      rw [bind_tc_ok, hvs1Eq]
      simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, by scalar_tac, fun y => ?_, by scalar_tac⟩
      have hi2 : i2.val = iL.val + 1 := by scalar_tac
      rw [hvs1Mem y, hmemL y, hi2]
      have hte : t = other.items.val[iL.val] := he
      simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
        List.mem_append, List.mem_singleton, hte]
      rw [or_assoc]
    case isFalse h =>
      have heq' : iL.val = other.items.val.length := by scalar_tac
      simp only [spec_ok]
      intro y; rw [hmemL y, heq', List.take_length]; rfl
  · exact ⟨hi, hlen, hmem⟩

/-- `VecSet.union_with self other` is set union (membership). The capacity bound `|self| + |other| ≤
    Usize.max` feeds the insertion loop. -/
theorem vecSetUnionWith_spec {T : Type} [DecidableEq T]
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self other : collections.VecSet T)
    (hcap : self.items.val.length + other.items.val.length ≤ Usize.max) :
    collections.VecSet.union_with cloneT eqT self other ⦃ vs' =>
      ∀ y, vsMem vs' y ↔ vsMem self y ∨ vsMem other y ⦄ := by
  unfold collections.VecSet.union_with
  exact vecSetUnionWithLoop_spec cloneT eqT heqT hcloneT self other hcap self 0#usize
    (by simp) (by simp) (by simp [vsMem])

/-! ## `VecMapKVecSet.extend_into`

`extend_into self key other` unions `other` into the live (last) `key`-keyed set, creating that
entry if absent. Its faithful image is the *last-match* nested membership `vmsMemLast`: `key`'s set
gains `other`'s elements, every other key untouched. The find-index loop reuses the `lastMatchInv`
machinery (same as `VecMap.insert`); the value update reuses `vecSetUnionWith_spec`. The shared write
primitive for `return_unendorsed`'s `taint_levels` / `gh_taint_received` / `override_used`. -/

/-- Find-last-index loop for `extend_into`: the returned index satisfies the same `lastMatchInv` as
    the `insert`/`get` loops (last matching key, or off-the-end when absent). -/
theorem extendIntoLoop_spec {K T : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (entries : alloc.vec.Vec (K × collections.VecSet T)) (key : K) (idx0 i0 : Usize)
    (hi0 : i0.val ≤ entries.val.length)
    (hInv : lastMatchInv entries.val key idx0.val i0.val) :
    collections.VecMapKVecSet.extend_into_loop eqK entries key idx0 i0 ⦃ idx1 =>
      lastMatchInv entries.val key idx1.val entries.val.length ⦄ := by
  unfold collections.VecMapKVecSet.extend_into_loop
  apply loop.spec_decr_nat
    (measure := fun p => entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ entries.val.length ∧ lastMatchInv entries.val key p.1.val p.2.val)
  · rintro ⟨idx, i⟩ ⟨hile, hinv⟩
    simp only [collections.VecMapKVecSet.extend_into_loop.body, alloc.vec.Vec.len]
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

/-- `extend_into self key other`: the live `key`-keyed set gains `other`'s elements; every other key
    is untouched. Stated as last-match nested membership (`vmsMemLast`). The capacity side conditions
    feed the `VecSet.union_with` / `Vec.push`. -/
theorem extendInto_spec {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (key : K)
    (other : collections.VecSet T)
    (hcapE : self.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ self.entries.val, p.2.items.val.length + other.items.val.length ≤ Usize.max)
    (hcapO : other.items.val.length ≤ Usize.max) :
    collections.VecMapKVecSet.extend_into cloneK eqK cloneT eqT self key other ⦃ vm' =>
      ∀ k v, vmsMemLast vm' k v ↔ vmsMemLast self k v ∨ (k = key ∧ vsMem other v) ⦄ := by
  unfold collections.VecMapKVecSet.extend_into
  have hinv0 : lastMatchInv self.entries.val key (alloc.vec.Vec.len self.entries).val (0#usize).val := by
    left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (extendIntoLoop_spec eqK heqK self.entries key (alloc.vec.Vec.len self.entries) 0#usize
      (by scalar_tac) hinv0)
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
      have hvs0 : vs0 = p.2 := by
        have : (kk, vs0) = self.entries.val[idx1.val]'hidxlt := hidx
        rw [hpe] at this; exact (Prod.mk.injEq .. ▸ this).2
      rw [vecSetClone_spec cloneT hcloneT vs0]
      have hcapU : vs0.items.val.length + other.items.val.length ≤ Usize.max := by
        rw [hvs0]; exact hcapS p (by rw [← hpe]; exact List.getElem_mem hidxlt)
      obtain ⟨s1, hs1Eq, hs1Mem⟩ :=
        spec_imp_exists (vecSetUnionWith_spec cloneT eqT heqT hcloneT vs0 other hcapU)
      rw [bind_tc_ok, hs1Eq]
      simp only [bind_tc_ok]
      step*
      have hlastSelf : vmLastEntry self.entries.val key = some (key, p.2) := by
        rw [vmLastEntry_eq_of_isLast self.entries.val idx1.val key hidxlt hmatch hlast, hpe, ← hpk]
      intro k v
      unfold vmsMemLast
      rw [__post2, alloc.vec.Vec.set_val_eq,
        vmLastEntry_set_lastmatch _ idx1.val key s1 hidxlt hmatch hlast k]
      by_cases hk : k = key
      · subst hk
        rw [if_pos rfl, hlastSelf]
        constructor
        · rintro ⟨ss, hss, hv⟩
          rw [Option.some_inj, Prod.mk.injEq] at hss
          obtain ⟨_, rfl⟩ := hss
          rcases (hs1Mem v).mp hv with h | h
          · exact Or.inl ⟨p.2, rfl, by rw [← hvs0]; exact h⟩
          · exact Or.inr ⟨rfl, h⟩
        · rintro (⟨ss, hss, hv⟩ | ⟨_, hv⟩)
          · rw [Option.some_inj, Prod.mk.injEq] at hss
            obtain ⟨_, rfl⟩ := hss
            exact ⟨s1, rfl, (hs1Mem v).mpr (Or.inl (by rw [hvs0]; exact hv))⟩
          · exact ⟨s1, rfl, (hs1Mem v).mpr (Or.inr hv)⟩
      · rw [if_neg hk]; simp only [hk, false_and, or_false]
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
    obtain ⟨s0, hs0Eq, hs0Nil⟩ : ∃ s0, collections.VecSet.new cloneT eqT = Result.ok s0 ∧
        s0.items.val = [] := ⟨_, rfl, rfl⟩
    rw [hs0Eq]; simp only [bind_tc_ok]
    obtain ⟨s1, hs1Eq, hs1Mem⟩ :=
      spec_imp_exists (vecSetUnionWith_spec cloneT eqT heqT hcloneT s0 other (by
        rw [hs0Nil]; simpa using hcapO))
    rw [hs1Eq]; simp only [bind_tc_ok]
    obtain ⟨vpush, hpushEq, hpushVal⟩ :=
      spec_imp_exists (alloc.vec.Vec.push_spec self.entries (key, s1) hcapE)
    rw [hpushEq]; simp only [bind_tc_ok, spec_ok]
    intro k v
    simp only [vmsMemLast, hpushVal, vmLastEntry_append_nomatch _ key s1 hno k]
    by_cases hk : k = key
    · subst hk
      rw [if_pos rfl]
      constructor
      · rintro ⟨ss, hss, hv⟩
        rw [Option.some_inj, Prod.mk.injEq] at hss
        obtain ⟨_, rfl⟩ := hss
        refine Or.inr ⟨rfl, ?_⟩
        rcases (hs1Mem v).mp hv with h | h
        · simp [vsMem, hs0Nil] at h
        · exact h
      · rintro (⟨ss, hss, _⟩ | ⟨_, hv⟩)
        · exact absurd (vmLastEntry_mem _ _ _ hss) (fun hm => hno _ hm rfl)
        · exact ⟨s1, rfl, (hs1Mem v).mpr (Or.inr hv)⟩
    · rw [if_neg hk]; simp only [hk, false_and, or_false]

/-! ## Shared specs relocated from the per-action proofs

Generic `VecMap`/`VecSet` last-match insert/remove specs (+ the `InvocationId` ne axiom)
consumed across the refinement; they were originally proved inside the `invoke_*` /
`return_unendorsed` slice files but are action-independent collection bridging. -/

set_option maxHeartbeats 4000000 in
/-- `VecSet.insert` adds `x` (idempotently) and preserves `Nodup`. The capacity bound is required only
    on the push path (`x` absent) — `insert` is a no-op when `x` is already present, so a caller that
    only re-inserts existing elements needs no bound. -/
theorem vecSetInsertNodup_spec {T : Type} [DecidableEq T]
    (inst_c : core.clone.Clone T) (inst_eq : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst_eq.eq a b = .ok (decide (a = b)))
    (vs : collections.VecSet T) (x : T)
    (hcap : x ∉ vs.items.val → vs.items.val.length < Usize.max) :
    collections.VecSet.insert inst_c inst_eq vs x ⦃ vs' =>
      (∀ y, vsMem vs' y ↔ vsMem vs y ∨ y = x) ∧
      (vs.items.val.Nodup → vs'.items.val.Nodup) ⦄ := by
  unfold collections.VecSet.insert
  obtain ⟨b, hcontains, hb⟩ :=
    spec_imp_exists (vecSetContains_spec inst_c inst_eq heq vs x)
  rw [hcontains]
  cases b with
  | true =>
    have hx : x ∈ vs.items.val := hb.mp rfl
    simp only [bind_tc_ok, reduceIte, spec_ok]
    refine ⟨fun y => ⟨Or.inl, ?_⟩, id⟩
    rintro (hy | rfl)
    · exact hy
    · exact hx
  | false =>
    have hx : x ∉ vs.items.val := fun hc => by have := hb.mpr hc; simp at this
    have hcap' : vs.items.val.length < Usize.max := hcap hx
    simp only [bind_tc_ok, Bool.false_eq_true, reduceIte]
    step*
    refine ⟨fun y => ?_, fun hnd => ?_⟩
    · simp only [vsMem, v_post, List.mem_append, List.mem_singleton]
    · simp only [v_post]
      rw [List.nodup_append]
      exact ⟨hnd, List.nodup_singleton x,
        fun a ha b hb hab => hx (by rw [List.mem_singleton] at hb; subst hab; subst hb; exact ha)⟩

/-- The opaque extracted `InvocationId.ne` is faithful decidable disequality. -/
axiom invocationId_ne_spec (a b : types.InvocationId) :
    types.InvocationId.Insts.CoreCmpPartialEqInvocationId.ne a b = .ok (decide (a ≠ b))

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

set_option maxHeartbeats 4000000 in
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

theorem insertIntoLoop_lastMatch_spec {K T : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K) (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (v : alloc.vec.Vec (K × collections.VecSet T)) (key : K) (idx0 i0 : Usize)
    (hi0 : i0.val ≤ v.val.length)
    (hInv : lastMatchInv v.val key idx0.val i0.val) :
    collections.VecMapKVecSet.insert_into_loop eqK v key idx0 i0 ⦃ idx1 =>
      lastMatchInv v.val key idx1.val v.val.length ⦄ := by
  unfold collections.VecMapKVecSet.insert_into_loop
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ v.val.length ∧ lastMatchInv v.val key p.1.val p.2.val)
  · rintro ⟨idx, i⟩ ⟨hile, hinv⟩
    simp only [collections.VecMapKVecSet.insert_into_loop.body, alloc.vec.Vec.len]
    split
    case isTrue h =>
      have hlt : i.val < v.val.length := by scalar_tac
      step as ⟨t, vs0, he⟩
      have hget : v.val[i.val]? = some (t, vs0) := by rw [List.getElem?_eq_getElem hlt, ← he]
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
      have heq' : i.val = v.val.length := by scalar_tac
      simp only [spec_ok]
      rwa [heq'] at hinv
  · exact ⟨hi0, hInv⟩

set_option maxHeartbeats 4000000 in
theorem vecMapKVecSetInsertInto_vmLast_spec {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (key : K) (elem : T)
    (hcapE : self.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ self.entries.val, p.2.items.val.length < Usize.max) :
    collections.VecMapKVecSet.insert_into cloneK eqK cloneT eqT self key elem ⦃ vm' =>
      ∀ k v, vmsMemLast vm' k v ↔ vmsMemLast self k v ∨ (k = key ∧ v = elem) ⦄ := by
  unfold collections.VecMapKVecSet.insert_into
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (insertIntoLoop_lastMatch_spec eqK heqK self.entries key (alloc.vec.Vec.len self.entries) 0#usize
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
      have hvs0 : vs0 = p.2 := by
        have : (kk, vs0) = self.entries.val[idx1.val]'hidxlt := hidx
        rw [hpe] at this; exact (Prod.mk.injEq .. ▸ this).2
      have hmem0 : (kk, vs0) ∈ self.entries.val := by rw [hidx]; exact List.getElem_mem hidxlt
      rw [vecSetClone_spec cloneT hcloneT vs0]; simp only [bind_tc_ok]
      obtain ⟨s1, hs1Eq, hs1Mem, _⟩ := spec_imp_exists
        (vecSetInsertNodup_spec cloneT eqT heqT vs0 elem (fun _ => hcapS (kk, vs0) hmem0))
      rw [hs1Eq]; simp only [bind_tc_ok]
      step*
      have hlastSelf : vmLastEntry self.entries.val key = some (key, p.2) := by
        rw [vmLastEntry_eq_of_isLast self.entries.val idx1.val key hidxlt hmatch hlast, hpe, ← hpk]
      intro k v
      unfold vmsMemLast
      rw [__post2, alloc.vec.Vec.set_val_eq,
        vmLastEntry_set_lastmatch _ idx1.val key s1 hidxlt hmatch hlast k]
      by_cases hk : k = key
      · subst hk
        rw [if_pos rfl, hlastSelf]
        constructor
        · rintro ⟨ss, hss, hv⟩
          rw [Option.some_inj, Prod.mk.injEq] at hss
          obtain ⟨_, rfl⟩ := hss
          rcases (hs1Mem v).mp hv with hh | hh
          · exact Or.inl ⟨p.2, rfl, by rw [← hvs0]; exact hh⟩
          · exact Or.inr ⟨rfl, hh⟩
        · rintro (⟨ss, hss, hv⟩ | ⟨_, hv⟩)
          · rw [Option.some_inj, Prod.mk.injEq] at hss
            obtain ⟨_, rfl⟩ := hss
            exact ⟨s1, rfl, (hs1Mem v).mpr (Or.inl (by rw [hvs0]; exact hv))⟩
          · exact ⟨s1, rfl, (hs1Mem v).mpr (Or.inr hv)⟩
      · rw [if_neg hk]; simp only [hk, false_and, or_false]
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
    obtain ⟨s0, hs0Eq, hs0Nil⟩ : ∃ s0, collections.VecSet.new cloneT eqT = Result.ok s0 ∧
        s0.items.val = [] := ⟨_, rfl, rfl⟩
    rw [hs0Eq]; simp only [bind_tc_ok]
    obtain ⟨s1, hs1Eq, hs1Mem, _⟩ := spec_imp_exists
      (vecSetInsertNodup_spec cloneT eqT heqT s0 elem
        (fun _ => by rw [hs0Nil]; simp only [List.length_nil]; scalar_tac))
    rw [hs1Eq]; simp only [bind_tc_ok]
    obtain ⟨vpush, hpushEq, hpushVal⟩ :=
      spec_imp_exists (alloc.vec.Vec.push_spec self.entries (key, s1) hcapE)
    rw [hpushEq]; simp only [bind_tc_ok, spec_ok]
    intro k v
    simp only [vmsMemLast, hpushVal, vmLastEntry_append_nomatch _ key s1 hno k]
    by_cases hk : k = key
    · subst hk
      rw [if_pos rfl]
      constructor
      · rintro ⟨ss, hss, hv⟩
        rw [Option.some_inj, Prod.mk.injEq] at hss
        obtain ⟨_, rfl⟩ := hss
        refine Or.inr ⟨rfl, ?_⟩
        rcases (hs1Mem v).mp hv with hh | hh
        · simp [vsMem, hs0Nil] at hh
        · exact hh
      · rintro (⟨ss, hss, _⟩ | ⟨_, hv⟩)
        · exact absurd (vmLastEntry_mem _ _ _ hss) (fun hm => hno _ hm rfl)
        · exact ⟨s1, rfl, (hs1Mem v).mpr (Or.inr hv)⟩
    · rw [if_neg hk]; simp only [hk, false_and, or_false]

/-- The length of the live (last-match) `key`-keyed set, `0` when `key` is absent. -/
def vmSetLen {K T : Type} [DecidableEq K]
    (vm : collections.VecMap K (collections.VecSet T)) (key : K) : Nat :=
  match vmLastEntry vm.entries.val key with
  | none => 0
  | some p => p.2.items.val.length

theorem getSetOrEmptyLen_spec {K T : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (key : K) :
    collections.VecMapKVecSet.get_set_or_empty cloneK eqK cloneT eqT self key ⦃ vs =>
      (∀ v, vsMem vs v ↔ vmsMemLast self key v) ∧ vs.items.val.length = vmSetLen self key ⦄ := by
  unfold collections.VecMapKVecSet.get_set_or_empty vmSetLen
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec cloneK eqK heqK (collections.VecSet.Insts.CoreCloneClone cloneT)
      (vecSetClone_spec cloneT hcloneT) self key)
  rw [hoEq]; simp only [bind_tc_ok]
  cases hL : vmLastEntry self.entries.val key with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho
    unfold collections.VecSet.new
    simp only [spec_ok]
    refine ⟨fun v => ?_, by trivial⟩
    simp only [vsMem, List.not_mem_nil, false_iff]
    rintro ⟨vs, hvs, _⟩; rw [hL] at hvs; simp at hvs
  | some p =>
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    have hp1 : p.1 = key := vmLastEntry_fst _ _ _ hL
    have hLk : vmLastEntry self.entries.val key = some (key, p.2) := by rw [hL, ← hp1]
    simp only [spec_ok]
    refine ⟨fun v => ?_, by trivial⟩
    constructor
    · intro hv; exact ⟨p.2, hLk, hv⟩
    · rintro ⟨vs, hvs, hv⟩
      rw [hLk, Option.some_inj, Prod.mk.injEq] at hvs
      obtain ⟨_, rfl⟩ := hvs; exact hv

end ArgusLean.Refinement
