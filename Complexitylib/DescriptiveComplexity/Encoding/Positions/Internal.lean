/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Positions.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Correctness of encoded table positions

The site enumeration is complete, has the expected length, and reproduces the
existing encoder when mapped to table values. These facts justify direct reads.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem mem_encodingTableSites_internal (V : Vocabulary) (card : Nat)
    (site : InputSite V card) : site ∈ encodingTableSites V card := by
  rcases site with ⟨i, args⟩ | ⟨c, a⟩ <;> simp [encodingTableSites, mem_allTuples]

theorem encodingTableSites_length_internal (V : Vocabulary) (card : Nat) :
    (encodingTableSites V card).length =
      ((List.finRange V.numRels).map (fun i => card ^ V.relArity i)).sum +
        V.numConsts * card := by
  simp [encodingTableSites, List.length_flatMap, allTuples_length]

theorem map_encodingTableSites_internal {V : Vocabulary} (A : DecFinStruct V) :
    (encodingTableSites V A.card).map (inputSiteValue A) =
      encodeRelsC A ++ encodeConstsC A := by
  simp [encodingTableSites, List.map_flatMap, List.map_map, Function.comp_def,
    inputSiteValue, encodeRelsC, encodeRelC, encodeConstsC, encodeConstC, beq_eq_decide,
    eq_comm]

theorem encodingPosition_lt_internal (V : Vocabulary) (card : Nat)
    (site : InputSite V card) : encodingPosition V card site < encodingLength V card := by
  have h := List.idxOf_lt_length_of_mem (mem_encodingTableSites_internal V card site)
  rw [encodingTableSites_length_internal] at h
  unfold encodingPosition encodingLength
  omega

theorem getElem?_encodeStruct_position_internal {V : Vocabulary} (A : DecFinStruct V)
    (site : InputSite V A.card) :
    (encodeStruct A)[encodingPosition V A.card site]? = some (inputSiteValue A site) := by
  rw [encodeStruct, ← map_encodingTableSites_internal]
  rw [List.getElem?_append_right (by
    simp only [List.length_replicate]
    unfold encodingPosition
    omega)]
  simp [encodingPosition, Nat.add_assoc, Nat.one_add,
    List.getElem?_idxOf (mem_encodingTableSites_internal V A.card site)]

theorem encodingLength_strictMono_internal (V : Vocabulary) :
    StrictMono (encodingLength V) := by
  intro a b hab
  have hs : ((List.finRange V.numRels).map (fun i => a ^ V.relArity i)).sum ≤
      ((List.finRange V.numRels).map (fun i => b ^ V.relArity i)).sum := by
    generalize List.finRange V.numRels = indices
    induction indices with
    | nil => rfl
    | cons i indices ih =>
      simpa only [List.map_cons, List.sum_cons] using
        Nat.add_le_add (Nat.pow_le_pow_left hab.le (V.relArity i)) ih
  have hc := Nat.mul_le_mul_left V.numConsts hab.le
  unfold encodingLength
  omega

theorem encodingTableSites_nodup_internal (V : Vocabulary) (card : Nat) :
    (encodingTableSites V card).Nodup := by
  have hall : (encodingTableSites V card).toFinset = Finset.univ := by
    ext site
    simp [mem_encodingTableSites_internal]
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (encodingTableSites V card : Multiset (InputSite V card)))).mp
  change (encodingTableSites V card).toFinset.card = (encodingTableSites V card).length
  rw [hall, Finset.card_univ, encodingTableSites_length_internal]
  simp [Fintype.card_sigma, ← List.ofFn_eq_map, List.sum_ofFn]

theorem getElem?_encodeStruct_header_internal {V : Vocabulary} (A : DecFinStruct V)
    (i : Fin (A.card + 1)) :
    (encodeStruct A)[i.val]? = some (decide (i.val < A.card)) := by
  rw [encodeStruct]
  by_cases hi : i.val < A.card
  · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hi)]
    simp [hi]
  · have hi' : i.val = A.card := by have := i.isLt; omega
    simp [hi']

theorem encodeStruct_eq_of_values_internal {V : Vocabulary} (A : DecFinStruct V)
    (bits : List Bool) (hlen : bits.length = encodingLength V A.card)
    (hheader : ∀ i : Fin (A.card + 1), bits[i.val]? = some (decide (i.val < A.card)))
    (hsites : ∀ site, bits[encodingPosition V A.card site]? = some (inputSiteValue A site)) :
    encodeStruct A = bits := by
  apply List.ext_getElem (encodeStruct_length A |>.trans hlen.symm)
  intro i hi hj
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem hi, ← List.getElem?_eq_getElem hj]
  by_cases hprefix : i < A.card + 1
  · exact (getElem?_encodeStruct_header_internal A ⟨i, hprefix⟩).trans
      (hheader ⟨i, hprefix⟩).symm
  · have hbound : i - (A.card + 1) < (encodingTableSites V A.card).length := by
      rw [encodingTableSites_length_internal]
      rw [encodeStruct_length] at hi
      omega
    let site := (encodingTableSites V A.card)[i - (A.card + 1)]
    have hpos : encodingPosition V A.card site = i := by
      simp only [encodingPosition, site,
        (encodingTableSites_nodup_internal V A.card).idxOf_getElem]
      omega
    simpa only [hpos] using
      (getElem?_encodeStruct_position_internal A site).trans (hsites site).symm

end Complexity.DescriptiveComplexity
