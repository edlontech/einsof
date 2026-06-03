import ArgusLean.Refinement.Bridging.StateRelation

/-! # Layer 1 — key-uniqueness preservation under the writes

The unified relation `R` carries `vmNodupKeys` (key-uniqueness) for every per-agent map, because the
kernel reads them last-match and that view is faithful to the `∃`-entry abstract reading only when keys
are unique (the [[plausible-bridging-harness]] counterexample). Each transition must therefore
re-establish `vmNodupKeys` on every map it writes. This module proves that the four write primitives
preserve key-uniqueness:

* `VecMap.insert` / `VecMapKVecSet.insert_into` / `VecMapKVecSet.extend_into` — all three share the
  *find-then-set-or-push* shape (find the last `key`-match via a `lastMatchInv` loop, then either
  overwrite that entry — keys unchanged — or append a fresh `(key, _)` whose key was provably absent);
* `VecMap.remove` — a key-filter, so the key list is a sublist and stays `Nodup`.

These feed the per-action `R`-preservation lemmas: an action that inserts into a per-agent map discharges
its `vmNodupKeys` post via the matching spec here, reusing the exact `lastMatchInv` loop specs the
membership characterisations already use. Pure proofs; no new axioms. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## Pure list facts -/

/-- Overwriting an entry with `(k, v)` whose key already equals `k` leaves the key list unchanged. -/
theorem nodupKeys_set_sameKey {α β : Type} (l : List (α × β)) (i : Nat) (k : α) (v : β)
    (h : i < l.length) (hk : (l[i]'h).1 = k) :
    (l.set i (k, v)).map Prod.fst = l.map Prod.fst := by
  rw [List.map_set]
  have hki : (l.map Prod.fst)[i]'(by simpa using h) = k := by rw [List.getElem_map]; exact hk
  show (l.map Prod.fst).set i k = l.map Prod.fst
  rw [← hki, List.set_getElem_self]

/-- Appending a pair whose key is absent keeps the key list `Nodup`. -/
theorem nodupKeys_append_absent {α β : Type} (l : List (α × β)) (k : α) (v : β)
    (hnd : (l.map Prod.fst).Nodup) (hk : k ∉ l.map Prod.fst) :
    ((l ++ [(k, v)]).map Prod.fst).Nodup := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  refine ⟨hnd, List.nodup_singleton _, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  rw [hab, hb] at ha
  exact hk ha

/-- `lastMatchInv`'s "off-end" branch says `key` is absent from the whole list. -/
theorem key_absent_of_lastMatchInv {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K)
    (idxv : Nat) (h : lastMatchInv l key idxv l.length) (hge : ¬ idxv < l.length) :
    key ∉ l.map Prod.fst := by
  have hidxlen : idxv = l.length := by
    rcases h with ⟨hlen, _⟩ | ⟨hlt, _, _⟩
    · exact hlen
    · omega
  rcases h with ⟨_, hno⟩ | ⟨hlt, _, _⟩
  · rw [List.mem_map]; rintro ⟨p, hp, hpk⟩
    obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
    exact hno k (by omega) p (by rw [List.getElem?_eq_getElem hk, hkp]) hpk
  · omega

/-- `lastMatchInv`'s "found" branch pins `idxv` as a `key`-keyed position. -/
theorem key_match_of_lastMatchInv {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K)
    (idxv : Nat) (h : lastMatchInv l key idxv l.length) (hlt : idxv < l.length) :
    (l[idxv]'hlt).1 = key := by
  rcases h with ⟨hlen, _⟩ | ⟨_, ⟨p, hp, hpk⟩, _⟩
  · omega
  · rw [List.getElem?_eq_getElem hlt] at hp; rw [Option.some_inj.mp hp]; exact hpk

/-! ## `VecMap.insert` preserves `vmNodupKeys` -/

theorem vecMapInsert_nodup {K V : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneV : core.clone.Clone V)
    (vm : collections.VecMap K V) (key : K) (val : V)
    (hcap : vm.entries.val.length < Usize.max) :
    collections.VecMap.insert cloneK eqK cloneV vm key val ⦃ vm' =>
      vmNodupKeys vm → vmNodupKeys vm' ⦄ := by
  unfold collections.VecMap.insert
  have hinv0 : lastMatchInv vm.entries.val key (alloc.vec.Vec.len vm.entries).val (0#usize).val := by
    left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (vecMapInsertLoop_spec eqK heq vm.entries key (alloc.vec.Vec.len vm.entries) 0#usize
      (by scalar_tac) hinv0)
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < vm.entries.val.length := by scalar_tac
    have hmatch := key_match_of_lastMatchInv vm.entries.val key idx1.val hlmi hidxlt
    step*
    intro hnd
    show ((_ : List (K × V)).map Prod.fst).Nodup
    rw [__post2, alloc.vec.Vec.set_val_eq, nodupKeys_set_sameKey _ _ key val hidxlt hmatch]
    exact hnd
  case isFalse hcond =>
    have hkabs := key_absent_of_lastMatchInv vm.entries.val key idx1.val hlmi (by scalar_tac)
    step*
    intro hnd
    show ((_ : List (K × V)).map Prod.fst).Nodup
    rw [v_post]
    exact nodupKeys_append_absent _ key val hnd hkabs

/-! ## `VecMapKVecSet.insert_into` preserves `vmNodupKeys` -/

theorem vecMapKVecSetInsertInto_nodup {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (key : K) (elem : T)
    (hcapE : self.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ self.entries.val, p.2.items.val.length < Usize.max) :
    collections.VecMapKVecSet.insert_into cloneK eqK cloneT eqT self key elem ⦃ vm' =>
      vmNodupKeys self → vmNodupKeys vm' ⦄ := by
  unfold collections.VecMapKVecSet.insert_into
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (insertIntoLoop_lastMatch_spec eqK heqK self.entries key (alloc.vec.Vec.len self.entries) 0#usize
      (by scalar_tac) (by left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩))
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < self.entries.val.length := by scalar_tac
    have hmatch := key_match_of_lastMatchInv self.entries.val key idx1.val hlmi hidxlt
    step as ⟨kk, vs0, hidx⟩
    have hmem0 : (kk, vs0) ∈ self.entries.val := by rw [hidx]; exact List.getElem_mem hidxlt
    rw [vecSetClone_spec cloneT hcloneT vs0]; simp only [bind_tc_ok]
    obtain ⟨s1, hs1Eq, _⟩ := spec_imp_exists
      (vecSetInsert_spec cloneT eqT heqT vs0 elem (hcapS (kk, vs0) hmem0))
    rw [hs1Eq]; simp only [bind_tc_ok]
    step*
    intro hnd
    show ((_ : List (K × collections.VecSet T)).map Prod.fst).Nodup
    rw [__post2, alloc.vec.Vec.set_val_eq, nodupKeys_set_sameKey _ _ key s1 hidxlt hmatch]
    exact hnd
  case isFalse hcond =>
    have hkabs := key_absent_of_lastMatchInv self.entries.val key idx1.val hlmi (by scalar_tac)
    simp only [collections.VecSet.new, bind_tc_ok]
    obtain ⟨s1, hs1Eq, _⟩ := spec_imp_exists
      (vecSetInsert_spec cloneT eqT heqT { items := alloc.vec.Vec.new T } elem (by scalar_tac))
    rw [hs1Eq]; simp only [bind_tc_ok]
    step*
    intro hnd
    show ((_ : List (K × collections.VecSet T)).map Prod.fst).Nodup
    rw [v_post]
    exact nodupKeys_append_absent _ key s1 hnd hkabs

/-! ## `VecMapKVecSet.extend_into` preserves `vmNodupKeys` -/

theorem extendInto_nodup {K T : Type} [DecidableEq K] [DecidableEq T]
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
      vmNodupKeys self → vmNodupKeys vm' ⦄ := by
  unfold collections.VecMapKVecSet.extend_into
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (extendIntoLoop_spec eqK heqK self.entries key (alloc.vec.Vec.len self.entries) 0#usize
      (by scalar_tac) (by left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩))
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < self.entries.val.length := by scalar_tac
    have hmatch := key_match_of_lastMatchInv self.entries.val key idx1.val hlmi hidxlt
    step as ⟨kk, vs0, hidx⟩
    have hmem0 : (kk, vs0) ∈ self.entries.val := by rw [hidx]; exact List.getElem_mem hidxlt
    rw [vecSetClone_spec cloneT hcloneT vs0]
    obtain ⟨s1, hs1Eq, _⟩ :=
      spec_imp_exists (vecSetUnionWith_spec cloneT eqT heqT hcloneT vs0 other
        (hcapS (kk, vs0) hmem0))
    rw [bind_tc_ok, hs1Eq]; simp only [bind_tc_ok]
    step*
    intro hnd
    show ((_ : List (K × collections.VecSet T)).map Prod.fst).Nodup
    rw [__post2, alloc.vec.Vec.set_val_eq, nodupKeys_set_sameKey _ _ key s1 hidxlt hmatch]
    exact hnd
  case isFalse hcond =>
    have hkabs := key_absent_of_lastMatchInv self.entries.val key idx1.val hlmi (by scalar_tac)
    obtain ⟨s0, hs0Eq, hs0Nil⟩ : ∃ s0, collections.VecSet.new cloneT eqT = Result.ok s0 ∧
        s0.items.val = [] := ⟨_, rfl, rfl⟩
    rw [hs0Eq]; simp only [bind_tc_ok]
    obtain ⟨s1, hs1Eq, _⟩ :=
      spec_imp_exists (vecSetUnionWith_spec cloneT eqT heqT hcloneT s0 other (by
        rw [hs0Nil]; simpa using hcapO))
    rw [hs1Eq]; simp only [bind_tc_ok]
    step*
    intro hnd
    show ((_ : List (K × collections.VecSet T)).map Prod.fst).Nodup
    rw [v_post]
    exact nodupKeys_append_absent _ key s1 hnd hkabs

/-! ## `VecMapKVecSet.remove_from` preserves `vmNodupKeys` -/

/-- `remove_from` removes an element from the live `key`-keyed set: it either overwrites the matched
    entry with the shrunk set (same key — key list unchanged) or leaves the map untouched (key absent).
    Either way the key list is preserved, so `vmNodupKeys` carries through. The `VecSet.remove`
    counterpart of `insert_into`'s nodup post; reuses the `removeFromLoop_spec` `lastMatchInv` machinery
    (the in-flight point-clear in `invoke_complete` / `invoke_start`). -/
theorem vecMapKVecSetRemoveFrom_nodup {K T : Type} [DecidableEq K] [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heqK : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (hcloneK : ∀ x : K, cloneK.clone x = .ok x)
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (hneT : ∀ a b : T, eqT.ne a b = .ok (decide (a ≠ b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (key : K) (elem : T) :
    collections.VecMapKVecSet.remove_from cloneK eqK cloneT eqT self key elem ⦃ vm' =>
      vmNodupKeys self → vmNodupKeys vm' ⦄ := by
  unfold collections.VecMapKVecSet.remove_from
  obtain ⟨idx1, hloopEq, hlmi⟩ := spec_imp_exists
    (removeFromLoop_spec eqK heqK self.entries key (alloc.vec.Vec.len self.entries) 0#usize
      (by scalar_tac) (by left; exact ⟨by scalar_tac, fun k hk => absurd hk (by scalar_tac)⟩))
  simp only [hloopEq, bind_tc_ok]
  split
  case isTrue hcond =>
    have hidxlt : idx1.val < self.entries.val.length := by scalar_tac
    step as ⟨kk, vs0, hidx⟩
    have hkkmatch : (self.entries.val[idx1.val]'hidxlt).1 = kk := by rw [← hidx]
    rw [hcloneK kk, bind_tc_ok, vecSetClone_spec cloneT hcloneT vs0, bind_tc_ok]
    obtain ⟨s1, hs1Eq, _⟩ := spec_imp_exists (vecSetRemove_spec cloneT eqT hneT hcloneT vs0 elem)
    rw [hs1Eq]; simp only [bind_tc_ok]
    step*
    intro hnd
    show ((_ : List (K × collections.VecSet T)).map Prod.fst).Nodup
    rw [__post2, alloc.vec.Vec.set_val_eq, nodupKeys_set_sameKey _ _ kk s1 hidxlt hkkmatch]
    exact hnd
  case isFalse hcond =>
    simp only [spec_ok]
    exact id

/-! ## `VecMap.remove` preserves `vmNodupKeys` -/

/-- `remove` key-filters the entries, so the key list is a sublist of the original and stays `Nodup`.
    Stated directly on the `filter (removeKept key)` shape the remove/clear specs expose. -/
theorem vmNodupKeys_filter {K V : Type} [DecidableEq K] (l : List (K × V)) (key : K)
    (hnd : (l.map Prod.fst).Nodup) :
    ((l.filter (removeKept key)).map Prod.fst).Nodup :=
  hnd.sublist (List.filter_sublist.map Prod.fst)

/-- `vmNodupKeys` carried through a `clear_agent_state` / `remove` key-filter, stated on the entry-list
    equation the inversion lemmas expose. -/
theorem vmNodupKeysFilter {K V : Type} [DecidableEq K] {vm' vm : collections.VecMap K V} {key : K}
    (heq : vm'.entries.val = vm.entries.val.filter (removeKept key)) (hnd : vmNodupKeys vm) :
    vmNodupKeys vm' := by
  unfold vmNodupKeys; rw [heq]; exact vmNodupKeys_filter vm.entries.val key hnd

end ArgusLean.Refinement
