/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Encoding.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Relation-certificate encoding proofs

Completeness and cardinality of the site enumeration give absence of duplicates.
Reading at a site's index then yields both directions of the encoding bijection.
-/

public section

namespace Complexity.DescriptiveComplexity.DecREnv

theorem mem_encodingSites_internal (card : Nat) (rctx : List Nat)
    (site : EncodingSite card rctx) : site ∈ encodingSites card rctx := by
  rcases site with ⟨r, args⟩
  simp [encodingSites, mem_allTuples]

theorem encodingSites_length_internal (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).length = encodingLength card rctx := by
  simp [encodingSites, List.length_flatMap, allTuples_length, encodingLength,
    ← List.ofFn_eq_map, List.get_eq_getElem]

theorem encodingSites_nodup_internal (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).Nodup := by
  have hall : (encodingSites card rctx).toFinset = Finset.univ := by
    ext site
    simp [mem_encodingSites_internal]
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (encodingSites card rctx : Multiset (EncodingSite card rctx)))).mp
  change (encodingSites card rctx).toFinset.card = (encodingSites card rctx).length
  rw [hall, Finset.card_univ, encodingSites_length_internal]
  simp [Fintype.card_sigma, encodingLength, ← List.sum_ofFn, List.get_eq_getElem]

theorem read_encode_internal {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    read card rctx (encode ρ) = ρ := by
  funext r args
  simp [read, encode, List.getElem?_idxOf (mem_encodingSites_internal card rctx ⟨r, args⟩)]

theorem encode_read_internal (card : Nat) (rctx : List Nat) (bits : List Bool)
    (h : bits.length = encodingLength card rctx) :
    encode (read card rctx bits) = bits := by
  have hlen : (encodingSites card rctx).length = bits.length :=
    (encodingSites_length_internal card rctx).trans h.symm
  apply List.ext_getElem (by simp [encode, hlen])
  intro i hi hj
  simp only [encode, List.getElem_map, read,
    (encodingSites_nodup_internal card rctx).idxOf_getElem]
  simp [List.getElem?_eq_getElem hj]

theorem encodingPolynomial_eval_internal (card : Nat) (rctx : List Nat) :
    (encodingPolynomial rctx).eval card = encodingLength card rctx := by
  induction rctx with
  | nil => simp [encodingPolynomial, encodingLength]
  | cons k rctx ih =>
    simpa [encodingPolynomial, encodingLength, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X] using congrArg (card ^ k + ·) ih

theorem encodingLength_mono_internal (rctx : List Nat) :
    Monotone (fun card => encodingLength card rctx) := by
  intro a b hab
  induction rctx with
  | nil => rfl
  | cons k rctx ih =>
    exact Nat.add_le_add (Nat.pow_le_pow_left hab k) ih

end Complexity.DescriptiveComplexity.DecREnv
