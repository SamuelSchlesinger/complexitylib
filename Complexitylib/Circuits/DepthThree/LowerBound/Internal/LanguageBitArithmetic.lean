/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitConvolution
public import Mathlib.Algebra.Polynomial.Div
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: language bit arithmetic

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitArithmetic.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

open BinaryAlgebra
open Polynomial

/-- Freeze a bit-word representation for the arithmetic evaluator. -/
def wordFreeze {n : ℕ} (a : BitWord n) : BitWord n :=
  listWord n (wordList a)

@[simp] theorem wordFreeze_eq {n : ℕ} (a : BitWord n) : wordFreeze a = a :=
  listWord_wordList a

/-- Cancel one high coefficient using the shifted modulus. -/
def cancelStep {r m : ℕ} (p : BitWord r) (k : ℕ) (a : BitWord m) : BitWord m :=
  if h : r ≤ k ∧ k < m then
    if a ⟨k, h.2⟩ = true then
      wordFreeze (wordXor a (shiftModulus p (k - r)))
    else a
  else a

theorem cancelStep_above {r m : ℕ} (p : BitWord r) (k : ℕ)
    (a : BitWord m) (i : Fin m) (hi : k < i.val) :
    cancelStep p k a i = a i := by
  by_cases hk : r ≤ k ∧ k < m
  · by_cases ha : a ⟨k, hk.2⟩ = true
    · have hs : k - r + r < i.val := by omega
      simp [cancelStep, hk, ha, wordXor, shiftModulus_above p (k - r) i hs]
    · simp [cancelStep, hk, ha]
  · simp [cancelStep, hk]

theorem cancelStep_at {r m : ℕ} (p : BitWord r) (a : BitWord m)
    (i : Fin m) (hi : r ≤ i.val) : cancelStep p i.val a i = false := by
  have hk : r ≤ i.val ∧ i.val < m := ⟨hi, i.is_lt⟩
  have hs : i.val - r + r = i.val := by omega
  by_cases ha : a i = true
  · simp [cancelStep, hk, ha, wordXor, shiftModulus, hs]
  · have hf : a i = false := Bool.eq_false_of_not_eq_true ha
    simp [cancelStep, hk, ha]

theorem wordPoly_cancelStep_mod {r m : ℕ} (p : BitWord r)
    (k : ℕ) (a : BitWord m) :
    wordPoly (cancelStep p k a) %ₘ inputPolynomialBits p =
      wordPoly a %ₘ inputPolynomialBits p := by
  by_cases hk : r ≤ k ∧ k < m
  · by_cases ha : a ⟨k, hk.2⟩ = true
    · have hs : k - r + r < m := by omega
      simp only [cancelStep, dite_eq_left hk, ite_eq_left ha, wordFreeze_eq,
        wordPoly_xor, wordPoly_shiftModulus p (k - r) hs,
        Polynomial.add_modByMonic,
        Polynomial.mul_self_modByMonic (inputPolynomialBits_monic p), add_zero]
    · simp [cancelStep, hk, ha]
  · simp [cancelStep, hk]

/-- Iterate high-coefficient cancellation to compute a remainder. -/
def reduceLoop {r m : ℕ} (p : BitWord r) : ℕ → BitWord m → BitWord m
  | 0, a => a
  | k + 1, a => reduceLoop p k (cancelStep p k a)

theorem wordPoly_reduceLoop_mod {r m : ℕ} (p : BitWord r)
    (k : ℕ) (a : BitWord m) :
    wordPoly (reduceLoop p k a) %ₘ inputPolynomialBits p =
      wordPoly a %ₘ inputPolynomialBits p := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    exact (ih (cancelStep p k a)).trans (wordPoly_cancelStep_mod p k a)

theorem reduceLoop_tail_false {r m : ℕ} (p : BitWord r) (k : ℕ)
    (a : BitWord m)
    (ha : ∀ i : Fin m, r ≤ i.val → k ≤ i.val → a i = false) :
    ∀ i : Fin m, r ≤ i.val → reduceLoop p k a i = false := by
  induction k generalizing a with
  | zero =>
    intro i hi
    exact ha i hi (Nat.zero_le _)
  | succ k ih =>
    apply ih (cancelStep p k a)
    intro i hri hki
    by_cases hlt : k < i.val
    · rw [cancelStep_above p k a i hlt]
      exact ha i hri (by omega)
    · have he : k = i.val := by omega
      subst k
      exact cancelStep_at p a i hri

/-- Resize a bit word, truncating or padding with false bits. -/
def wordResize {m : ℕ} (r : ℕ) (a : BitWord m) : BitWord r :=
  fun i => wordGet a i.val

theorem wordPoly_resize_of_tail_false {r m : ℕ} (a : BitWord m)
    (ha : ∀ i : Fin m, r ≤ i.val → a i = false) :
    wordPoly (wordResize r a) = wordPoly a := by
  ext i
  rw [coeff_wordPoly, coeff_wordPoly]
  apply congrArg bitValue
  by_cases hi : i < r
  · simp [wordGet, wordResize, hi]
  · rw [wordGet_of_le _ (Nat.le_of_not_lt hi)]
    by_cases hm : i < m
    · rw [wordGet_of_lt a hm, ha ⟨i, hm⟩ (Nat.le_of_not_lt hi)]
    · rw [wordGet_of_le a (Nat.le_of_not_lt hm)]

/-- Reduce a bit-word polynomial modulo the monic modulus. -/
def wordReduce {r m : ℕ} (p : BitWord r) (a : BitWord m) : BitWord r :=
  wordFreeze (wordResize r (reduceLoop p m a))

theorem wordPoly_reduce {r m : ℕ} (p : BitWord r) (a : BitWord m) :
    wordPoly (wordReduce p a) = wordPoly a %ₘ inputPolynomialBits p := by
  have ht : ∀ i : Fin m, r ≤ i.val → reduceLoop p m a i = false :=
    reduceLoop_tail_false p m a (by
      intro i _ hi
      exact False.elim (Nat.not_le.mpr i.is_lt hi))
  have hd : (wordPoly (reduceLoop p m a)).degree <
      (inputPolynomialBits p).degree := by
    rw [inputPolynomialBits_degree]
    exact degree_wordPoly_lt_of_tail_false _ ht
  have hs := (Polynomial.modByMonic_eq_self_iff
    (inputPolynomialBits_monic p)).2 hd
  calc
    wordPoly (wordReduce p a) = wordPoly (reduceLoop p m a) := by
      simp only [wordReduce, wordFreeze_eq]
      exact wordPoly_resize_of_tail_false _ ht
    _ = wordPoly (reduceLoop p m a) %ₘ inputPolynomialBits p := hs.symm
    _ = wordPoly a %ₘ inputPolynomialBits p := wordPoly_reduceLoop_mod p m a

/-- Multiply bit-word polynomials and reduce modulo the modulus. -/
def wordMulMod {r : ℕ} (p a b : BitWord r) : BitWord r :=
  wordReduce p (wordConvolve a b)

theorem wordPoly_mulMod {r : ℕ} (p a b : BitWord r) :
    wordPoly (wordMulMod p a b) =
      (wordPoly a * wordPoly b) %ₘ inputPolynomialBits p := by
  rw [wordMulMod, wordPoly_reduce, wordPoly_convolve]

end DepthThreeLowerBound

end Complexity
