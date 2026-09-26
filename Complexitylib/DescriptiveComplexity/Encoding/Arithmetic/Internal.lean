/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Correctness of arithmetic encoding addresses

Index a flattened list by the total length of preceding blocks plus an offset
within the selected block. Applied first to tuples and then to relation tables,
this identifies arithmetic addresses with the encoder's existing site positions.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem tupleIndex_eq_sum_internal (card : Nat) {k : Nat} (args : Fin k → Nat) :
    tupleIndex card args = ∑ i : Fin k, args i * card ^ i.val := by
  induction k with
  | zero => simp [tupleIndex]
  | succ k ih =>
    simp only [tupleIndex, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
      Fin.val_succ, pow_succ', ih, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl

theorem tupleDigits_eq_div_pow_internal (card k index : Nat) (i : Fin k) :
    tupleDigits card k index i = index / card ^ i.val % card := by
  induction k generalizing index with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [tupleDigits]
    · simp only [tupleDigits, Fin.cons_succ, ih, Fin.val_succ, pow_succ',
        Nat.div_div_eq_div_mul]

theorem getElem?_flatMap_offset_internal {α β : Type} (xs : List α) (f : α → List β)
    (i : Fin xs.length) (j : Nat) (hj : j < (f xs[i.val]).length) :
    (xs.flatMap f)[((xs.take i.val).map fun x => (f x).length).sum + j]? =
      (f xs[i.val])[j]? := by
  induction xs with
  | nil => exact i.elim0
  | cons x xs ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      simpa using List.getElem?_append_left (l₂ := xs.flatMap f) hj
    | succ i =>
      simp only [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [List.getElem?_append_right (by omega)]
      simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
      exact ih ⟨i, by simpa using hi⟩ hj

theorem tupleIndex_lt_internal {card k : Nat} (args : Fin k → Fin card) :
    tupleIndex card (fun i => (args i).val) < card ^ k := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    have htail := ih (fun i => args i.succ)
    have hhead := (args 0).isLt
    have hmul := Nat.mul_le_mul_left card (Nat.succ_le_of_lt htail)
    rw [Nat.mul_succ] at hmul
    simp only [tupleIndex, Nat.pow_succ, Nat.mul_comm (card ^ k) card]
    omega

theorem getElem?_allTuples_index_internal {card k : Nat} (args : Fin k → Fin card) :
    (allTuples card k)[tupleIndex card (fun i => (args i).val)]? = some args := by
  induction k with
  | zero =>
    have hargs : args = Fin.elim0 := by funext i; exact i.elim0
    simp [allTuples, tupleIndex, hargs]
  | succ k ih =>
    let tail := fun i : Fin k => args i.succ
    let pos := tupleIndex card (fun i => (tail i).val)
    have hpos : pos < (allTuples card k).length := by
      rw [allTuples_length]
      exact tupleIndex_lt_internal tail
    have htail : (allTuples card k)[pos] = tail := by
      have h := ih tail
      change (allTuples card k)[pos]? = some tail at h
      rw [List.getElem?_eq_getElem hpos] at h
      exact Option.some.inj h
    let blocks : (Fin k → Fin card) → List (Fin (k + 1) → Fin card) :=
      fun t => (List.finRange card).map (fun v => Fin.cons v t)
    have hblock : (args 0).val < (blocks ((allTuples card k)[pos])).length := by
      simpa only [blocks, List.length_map, List.length_finRange] using (args 0).isLt
    have h := getElem?_flatMap_offset_internal (allTuples card k) blocks
      ⟨pos, hpos⟩ (args 0).val hblock
    simp only [blocks, List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
      List.length_take, Nat.min_eq_left hpos.le, htail, List.getElem?_map] at h
    have hhead : (List.finRange card)[(args 0).val]? = some (args 0) := by
      simp [List.finRange]
    have hcons : Fin.cons (args 0) tail = args := Fin.cons_self_tail args
    rw [hhead, Option.map_some, hcons] at h
    simpa only [allTuples, tupleIndex, pos, tail, nsmul_eq_mul, Nat.cast_id,
      Nat.mul_comm, Nat.add_comm] using h

private theorem position_of_getElem? (V : Vocabulary) (card i : Nat)
    (site : InputSite V card) (h : (encodingTableSites V card)[i]? = some site) :
    encodingPosition V card site = card + 1 + i := by
  obtain ⟨hi, hsite⟩ := List.getElem?_eq_some_iff.mp h
  rw [encodingPosition, ← hsite, (encodingTableSites_nodup V card).idxOf_getElem]

theorem tupleDigits_lt_internal {card : Nat} (hcard : 0 < card) (k index : Nat)
    (i : Fin k) : tupleDigits card k index i < card := by
  induction k generalizing index with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.mod_lt _ hcard
    · exact ih (index / card) j

theorem tupleIndex_tupleDigits_internal {card : Nat} (hcard : 0 < card) (k index : Nat)
    (hi : index < card ^ k) : tupleIndex card (tupleDigits card k index) = index := by
  induction k generalizing index with
  | zero =>
    simp only [Nat.pow_zero] at hi
    have hi0 : index = 0 := by omega
    subst index
    rfl
  | succ k ih =>
    have hdiv : index / card < card ^ k :=
      (Nat.div_lt_iff_lt_mul hcard).mpr (by simpa only [Nat.pow_succ] using hi)
    simp only [tupleDigits, tupleIndex, Fin.cons_zero, Fin.cons_succ, ih _ hdiv]
    exact Nat.mod_add_div index card

theorem map_allTuples_eq_range_internal {α : Type} {card : Nat} (hcard : 0 < card)
    (k : Nat) (f : (Fin k → Nat) → α) :
    (allTuples card k).map (fun args => f (fun i => (args i).val)) =
      (List.range (card ^ k)).map (fun index => f (tupleDigits card k index)) := by
  apply List.ext_getElem (by simp only [List.length_map, allTuples_length, List.length_range])
  intro index hleft hright
  have hi : index < card ^ k := by simpa only [List.length_map, List.length_range] using hright
  let args : Fin k → Fin card := fun i =>
    ⟨tupleDigits card k index i, tupleDigits_lt_internal hcard k index i⟩
  have hlookup := getElem?_allTuples_index_internal args
  change (allTuples card k)[tupleIndex card (tupleDigits card k index)]? = some args at hlookup
  rw [tupleIndex_tupleDigits_internal hcard k index hi] at hlookup
  have hbound : index < (allTuples card k).length := by rwa [allTuples_length]
  rw [List.getElem?_eq_getElem hbound] at hlookup
  simp only [List.getElem_map, List.getElem_range, Option.some.inj hlookup]
  rfl

theorem encodingPosition_relation_internal (V : Vocabulary) (card : Nat)
    (r : Fin V.numRels) (args : Fin (V.relArity r) → Fin card) :
    encodingPosition V card (.inl ⟨r, args⟩) =
      relationAddress V card r (fun i => (args i).val) := by
  let blocks : Fin V.numRels → List (InputSite V card) := fun i =>
    (allTuples card (V.relArity i)).map fun t => .inl ⟨i, t⟩
  have hr : (List.finRange V.numRels)[r.val]'(by simp) = r := by simp
  have hj : tupleIndex card (fun i => (args i).val) <
      (blocks ((List.finRange V.numRels)[r.val])).length := by
    rw [hr]
    simpa only [blocks, List.length_map, allTuples_length] using tupleIndex_lt_internal args
  have h := getElem?_flatMap_offset_internal (List.finRange V.numRels) blocks
    ⟨r.val, by simp⟩ (tupleIndex card (fun i => (args i).val)) hj
  rw [hr] at h
  simp only [blocks, List.length_map, allTuples_length, List.getElem?_map,
    getElem?_allTuples_index_internal, Option.map_some] at h
  have hi := (List.getElem?_eq_some_iff.mp h).choose
  have hfull := (List.getElem?_append_left (l₂ :=
    (List.finRange V.numConsts).flatMap fun c =>
      (List.finRange card).map fun a => (Sum.inr (c, a) : InputSite V card)) hi).trans h
  have hp := position_of_getElem? V card _ (.inl ⟨r, args⟩) hfull
  simpa only [relationAddress, Nat.add_assoc] using hp

theorem encodingPosition_constant_internal (V : Vocabulary) (card : Nat)
    (c : Fin V.numConsts) (a : Fin card) :
    encodingPosition V card (.inr (c, a)) = constantAddress V card c a.val := by
  let blocks : Fin V.numConsts → List (InputSite V card) := fun c =>
    (List.finRange card).map fun a => .inr (c, a)
  have hc : (List.finRange V.numConsts)[c.val]'(by simp) = c := by simp
  have hj : a.val < (blocks ((List.finRange V.numConsts)[c.val])).length := by
    simpa only [blocks, List.length_map, List.length_finRange] using a.isLt
  have h := getElem?_flatMap_offset_internal (List.finRange V.numConsts) blocks
    ⟨c.val, by simp⟩ a.val hj
  rw [hc] at h
  simp only [blocks, List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
    List.length_take, Nat.min_eq_left c.isLt.le, List.getElem?_map] at h
  have ha : (List.finRange card)[a.val]? = some a := by simp [List.finRange]
  rw [ha, Option.map_some] at h
  let rels : List (InputSite V card) := (List.finRange V.numRels).flatMap fun i =>
    (allTuples card (V.relArity i)).map fun t => .inl ⟨i, t⟩
  have hlen : rels.length =
      ((List.finRange V.numRels).map (fun i => card ^ V.relArity i)).sum := by
    simp [rels, List.length_flatMap, allTuples_length]
  have hfull : (encodingTableSites V card)[rels.length + (c.val * card + a.val)]? =
      some (.inr (c, a)) := by
    change (rels ++ (List.finRange V.numConsts).flatMap blocks)[_]? = _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact h
  have hp := position_of_getElem? V card _ (.inr (c, a)) hfull
  simpa only [constantAddress, hlen, Nat.add_assoc] using hp

end Complexity.DescriptiveComplexity
