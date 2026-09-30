/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.FiniteBound
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Binomial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# Binary assignments and the public correlation bounds

The set-of-true-coordinates representation is equivalent to the ordinary
binary cube. Correlation is unchanged by this bijection.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {k m d : ℕ}

theorem correlation_comm {α : Type*} [Fintype α] (f g : α → ZMod 2) :
    correlation f g = correlation g f := by
  simp only [correlation, eq_comm]

theorem correlation_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f g : β → ZMod 2) :
    correlation (fun x => f (e x)) (fun x => g (e x)) = correlation f g := by
  classical
  simp only [correlation, Fintype.card_congr e,
    Equiv.sum_comp e (fun x => if f x = g x then (1 : ℝ) else -1)]

theorem bitsToBlocks_blockBits (x : BlockCube k m) : bitsToBlocks (blockBits x) = x := by
  ext i j
  simp [bitsToBlocks, blockBits]

theorem blockBits_bitsToBlocks (x : Fin k × Fin (2 * m + 1) → ZMod 2) :
    blockBits (bitsToBlocks x) = x := by
  funext ij
  simp only [blockBits, bitsToBlocks, mem_filter, mem_univ, true_and]
  split_ifs with h
  · exact h.symm
  · have hval := ZMod.val_lt (x ij)
    have hone : (x ij).val ≠ 1 := fun he => h (Fin.ext he)
    have hz : (x ij).val = 0 := by omega
    exact ((ZMod.val_eq_zero _).mp hz).symm

/-- The two Boolean input representations are in bijection. -/
def blockBitsEquiv : BlockCube k m ≃ (Fin k × Fin (2 * m + 1) → ZMod 2) where
  toFun := blockBits
  invFun := bitsToBlocks
  left_inv := bitsToBlocks_blockBits
  right_inv := blockBits_bitsToBlocks

theorem exceptional_card_eq (m d : ℕ) :
    Nat.card (ExceptionalAtom m d) = 2 * middleBandCount m d := by
  let e : ExceptionalAtom m d ≃
      {a : Finset (Fin (2 * m + 1)) // a.card ≤ m ∧ m < a.card + d} × Bool :=
    { toFun := fun a => (⟨a.val.1.val, a.val.1.property, a.property⟩, a.val.2)
      invFun := fun a => ⟨(⟨a.1.val, a.1.property.1⟩, a.2), a.1.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, middleBandCount, Nat.mul_comm]

theorem correlation_middleBand_bound
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    correlation xorMajority (polynomialEval p) ≤
      (2 * (middleBandCount m d : ℝ) / 2 ^ (2 * m + 1)) ^ k := by
  rw [correlation_comm]
  simpa only [exceptional_card_eq, Nat.cast_mul, Nat.cast_ofNat] using
    correlation_finite_bound p hp

theorem correlation_sqrt_bound
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    correlation xorMajority (polynomialEval p) ≤ (2 * d / Real.sqrt (2 * m + 1)) ^ k := by
  rw [correlation_comm]
  exact (correlation_finite_bound p hp).trans
    (pow_le_pow_left₀ (by positivity) (exceptional_fraction_le m d) k)

theorem correlation_bits_bound
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    correlation xorMajorityBits (fun x => MvPolynomial.eval x p) ≤
      (2 * d / Real.sqrt (2 * m + 1)) ^ k := by
  rw [← correlation_equiv blockBitsEquiv]
  change correlation (fun x : BlockCube k m => xorMajority (bitsToBlocks (blockBits x)))
    (polynomialEval p) ≤ _
  simpa only [bitsToBlocks_blockBits] using correlation_sqrt_bound p hp

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal
