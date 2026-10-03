/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.BlockEval.Defs
public import Mathlib.Algebra.Polynomial.Div
import Complexitylib.Encoding.BitPolynomial
import Complexitylib.Encoding.BitPolynomial.Addition
import Complexitylib.Encoding.BitPolynomial.Remainder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Exact Horner semantics for a bounded block fold

A partial fold of length `n ≤ total` evaluates the blocks beginning at
`total-n`, with its first block at exponent zero. This invariant makes the
reverse traversal explicit and gives the full coefficient sum at `n=total`.
The width and zero-modulus statements hold even outside this partial-fold
semantic domain.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

open scoped BigOperators

private theorem horner_sum {R : Type*} [CommSemiring R] (c : Nat → R) (y : R)
    (start n : Nat) :
    (∑ j ∈ Finset.range (n + 1), c (start + j) * y ^ j) =
      c start + y * ∑ j ∈ Finset.range n, c (start + 1 + j) * y ^ j := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, pow_zero, mul_one]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show start + (j + 1) = start + 1 + j by lia, pow_succ]
  ring

private theorem horner_mod (c y p E : Polynomial (ZMod 2)) :
    (c + y * (p %ₘ E)) %ₘ E = (c + y * p) %ₘ E := by
  rw [Polynomial.add_modByMonic, Polynomial.add_modByMonic]
  congr 1
  by_cases monic : E.Monic
  · apply Polynomial.modByMonic_eq_of_dvd_sub monic
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right (Polynomial.dvd_modByMonic_sub p E) y
  · simp only [Polynomial.modByMonic_eq_of_not_monic _ monic]

private theorem zero_block_state (n : Nat) : ofBits (List.replicate n false) = 0 := by
  ext i
  simp only [BitPolynomial.ofBits_coeff, List.getElem?_replicate]
  split_ifs <;> rfl

theorem coefficientBlock_length_le (coeffs : List Bool) (width j : Nat) :
    (coefficientBlock coeffs width j).length ≤ width := by
  simp only [coefficientBlock, List.length_take]
  exact min_le_left _ _

theorem blockEvalStep_length (coefficient seed modulus state : List Bool) :
    (blockEvalStep coefficient seed modulus state).length = significantLength modulus - 1 := by
  unfold blockEvalStep
  split_ifs with zero
  · simp only [List.length_nil, zero, Nat.zero_sub]
  · rw [BitPolynomial.remainderBits_length, ite_eq_right zero]

theorem blockEvalScan_length (coeffs : List Bool) (width : Nat) (seed modulus : List Bool)
    (total : Nat) (count : List Bool) :
    (blockEvalScan coeffs width seed modulus total count).length =
      significantLength modulus - 1 := by
  cases count with
  | nil => simp only [blockEvalScan, List.length_replicate]
  | cons bit tail => exact blockEvalStep_length _ _ _ _

theorem blockEvalBits_length (coeffs : List Bool) (width : Nat) (seed modulus count : List Bool) :
    (blockEvalBits coeffs width seed modulus count).length = significantLength modulus - 1 :=
  blockEvalScan_length _ _ _ _ _ _

theorem blockEvalBits_length_le (coeffs : List Bool) (width : Nat)
    (seed modulus count : List Bool) :
    (blockEvalBits coeffs width seed modulus count).length ≤ modulus.length := by
  rw [blockEvalBits_length]
  exact (Nat.sub_le _ _).trans (BitPolynomial.significantLength_le modulus)

theorem blockEvalBits_of_modulus_zero (coeffs : List Bool) (width : Nat)
    (seed modulus count : List Bool) (zero : ofBits modulus = 0) :
    blockEvalBits coeffs width seed modulus count = [] := by
  have zeroWidth := (BitPolynomial.significantLength_eq_zero_iff modulus).mpr zero
  cases count <;> simp only [blockEvalBits, blockEvalScan, blockEvalStep, zeroWidth,
    Nat.zero_sub, List.replicate_zero, ite_true]

theorem ofBits_blockEvalStep (coefficient seed modulus state : List Bool)
    (nonzero : ofBits modulus ≠ 0) :
    ofBits (blockEvalStep coefficient seed modulus state) =
      (ofBits coefficient + ofBits seed * ofBits state) %ₘ ofBits modulus := by
  have width := (BitPolynomial.significantLength_eq_zero_iff modulus).not.mpr nonzero
  rw [blockEvalStep, ite_eq_right width, BitPolynomial.ofBits_remainderBits,
    BitPolynomial.ofBits_addBits, BitPolynomial.ofBits_mulBits]

theorem ofBits_blockEvalScan (coeffs : List Bool) (width : Nat) (seed modulus : List Bool)
    (total : Nat) (count : List Bool) (nonzero : ofBits modulus ≠ 0)
    (bound : count.length ≤ total) :
    ofBits (blockEvalScan coeffs width seed modulus total count) =
      (∑ j ∈ Finset.range count.length,
        ofBits (coefficientBlock coeffs width (total - count.length + j)) *
          ofBits seed ^ j) %ₘ ofBits modulus := by
  induction count with
  | nil => simp only [blockEvalScan, zero_block_state, List.length_nil,
      Finset.range_zero, Finset.sum_empty, Polynomial.zero_modByMonic]
  | cons bit tail ih =>
      simp only [List.length_cons] at bound
      have tailBound : tail.length ≤ total := by lia
      have shift : total - tail.length = total - (tail.length + 1) + 1 := by
        lia
      rw [blockEvalScan, ofBits_blockEvalStep _ _ _ _ nonzero, ih tailBound, horner_mod,
        List.length_cons, show total - tail.length - 1 = total - (tail.length + 1) by lia,
        shift]
      exact congrArg (fun p : Polynomial (ZMod 2) => p %ₘ ofBits modulus)
        (horner_sum (fun j => ofBits (coefficientBlock coeffs width j))
          (ofBits seed) (total - (tail.length + 1)) tail.length).symm

theorem ofBits_blockEvalBits (coeffs : List Bool) (width : Nat)
    (seed modulus count : List Bool) (nonzero : ofBits modulus ≠ 0) :
    ofBits (blockEvalBits coeffs width seed modulus count) =
      (∑ j ∈ Finset.range count.length,
        ofBits (coefficientBlock coeffs width j) * ofBits seed ^ j) %ₘ ofBits modulus := by
  simpa only [blockEvalBits, Nat.sub_self, Nat.zero_add] using
    ofBits_blockEvalScan coeffs width seed modulus count.length count nonzero le_rfl

theorem blockEval_pair (coeffs widthWord seed modulus count : List Bool) :
    blockEval (pair (pair (pair coeffs widthWord) (pair seed modulus)) count) =
      blockEvalBits coeffs widthWord.length seed modulus count := by
  simp only [blockEval, pairFst_pair, pairSnd_pair]

theorem blockEval_length_le (z : List Bool) : (blockEval z).length ≤ z.length :=
  (blockEvalBits_length_le _ _ _ _ _).trans
    ((pairSnd_length_le (pairSnd (pairFst z))).trans
      ((pairSnd_length_le (pairFst z)).trans (pairFst_length_le z)))

end BitPolynomial.Internal
end Complexity
