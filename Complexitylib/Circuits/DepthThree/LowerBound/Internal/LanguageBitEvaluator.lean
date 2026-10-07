/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitArithmetic
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Language
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: language bit evaluator

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitEvaluator.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

open scoped BigOperators
open BinaryAlgebra
open Polynomial

theorem mul_remainder_modByMonic (a b p : Polynomial (ZMod 2)) (hp : p.Monic) :
    (a * (b %ₘ p)) %ₘ p = (a * b) %ₘ p := by
  symm
  calc
    (a * b) %ₘ p = (a * (b %ₘ p + p * (b /ₘ p))) %ₘ p := by
      rw [Polynomial.modByMonic_add_div b p]
    _ = (a * (b %ₘ p)) %ₘ p := by
      rw [mul_add, Polynomial.add_modByMonic]
      have hz : (a * (p * (b /ₘ p))) %ₘ p = 0 := by
        rw [← mul_assoc, mul_comm a p, mul_assoc,
          Polynomial.self_mul_modByMonic hp]
      rw [hz, add_zero]

theorem wordPoly_mod_self {r : ℕ} (p a : BitWord r) :
    wordPoly a %ₘ inputPolynomialBits p = wordPoly a := by
  apply (Polynomial.modByMonic_eq_self_iff (inputPolynomialBits_monic p)).2
  rw [inputPolynomialBits_degree]
  exact degree_wordPoly_lt a

/-- Evaluate a coefficient sequence by Horner iteration on bit words. -/
def wordHorner {r : ℕ} (p h : BitWord r) :
    (t : ℕ) → (Fin t → BitWord r) → BitWord r
  | 0, _ => fun _ => false
  | t + 1, b => wordFreeze (wordXor (b 0)
      (wordMulMod p h (wordHorner p h t (fun i => b i.succ))))

theorem wordPoly_horner {r : ℕ} (p h : BitWord r) (t : ℕ)
    (b : Fin t → BitWord r) :
    wordPoly (wordHorner p h t b) =
      (∑ j : Fin t, wordPoly (b j) * wordPoly h ^ j.val) %ₘ
        inputPolynomialBits p := by
  induction t with
  | zero => simp [wordHorner]
  | succ t ih =>
    have hsum :
        (∑ j : Fin (t + 1), wordPoly (b j) * wordPoly h ^ j.val) =
          wordPoly (b 0) + wordPoly h *
            ∑ j : Fin t, wordPoly (b j.succ) * wordPoly h ^ j.val := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      apply congrArg (fun z : Polynomial (ZMod 2) => wordPoly (b 0) + z)
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [wordHorner, wordFreeze_eq, wordPoly_xor, wordPoly_mulMod,
      ih, mul_remainder_modByMonic _ _ _ (inputPolynomialBits_monic p),
      hsum, Polynomial.add_modByMonic, wordPoly_mod_self]

/-- Compute the binary hash in the bit-word representation. -/
def wordHash {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d) : BitWord r :=
  wordFreeze fun i =>
    xorBits (List.ofFn fun s : Fin d => u (BinaryHash.sumIndex i s) && x s)

theorem wordHash_eq {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d) :
    wordHash u x = BinaryHash.hashBool u x := by
  funext i
  apply bitValue_injective
  simp only [wordHash, wordFreeze_eq, bitValue_xorBits_ofFn, bitValue_and,
    BinaryHash.bitValue_hashBool, BinaryHash.hashF2]

/-- Multiply binary polynomials represented by bit lists. -/
def multiplyBitLists (r : ℕ) (p a b : List Bool) : List Bool :=
  wordList (wordMulMod (listWord r p) (listWord r a) (listWord r b))

@[simp] theorem multiplyBitLists_length (r : ℕ) (p a b : List Bool) :
    (multiplyBitLists r p a b).length = r := by
  simp [multiplyBitLists]

theorem multiplyBitLists_correct (r : ℕ) (p a b : List Bool) :
    wordPoly (listWord r (multiplyBitLists r p a b)) =
      (wordPoly (listWord r a) * wordPoly (listWord r b)) %ₘ
        inputPolynomialBits (listWord r p) := by
  simp only [multiplyBitLists, listWord_wordList, wordPoly_mulMod]

/-- Evaluate coefficient bit lists by Horner iteration. -/
def hornerBitLists (r : ℕ) (p h : List Bool) (b : List (List Bool)) : List Bool :=
  wordList (wordHorner (listWord r p) (listWord r h) b.length
    (fun j => listWord r (b.getD j.val [])))

@[simp] theorem hornerBitLists_length (r : ℕ) (p h : List Bool)
    (b : List (List Bool)) : (hornerBitLists r p h b).length = r := by
  simp [hornerBitLists]

theorem hornerBitLists_correct (r : ℕ) (p h : List Bool) (b : List (List Bool)) :
    wordPoly (listWord r (hornerBitLists r p h b)) =
      (∑ j : Fin b.length, wordPoly (listWord r (b.getD j.val [])) *
        wordPoly (listWord r h) ^ j.val) %ₘ inputPolynomialBits (listWord r p) := by
  simp only [hornerBitLists, listWord_wordList, wordPoly_horner]

namespace ParsedInput

/-- Compute the parsed evaluation remainder as bits. -/
def evaluationBits (q : ParsedInput) : BitWord q.ringDegree :=
  wordHorner q.polynomial (wordHash q.hashSeed q.data)
    q.coefficientCount q.coefficients

theorem wordPoly_evaluationBits (q : ParsedInput) :
    wordPoly q.evaluationBits = q.evaluationRemainder := by
  rw [evaluationBits, wordPoly_horner, wordHash_eq]
  rfl

/-- Read the acceptance bit from the bit-level evaluation. -/
def evaluateBits (q : ParsedInput) : Bool :=
  !(wordGet q.evaluationBits 0)

theorem evaluateBits_eq (q : ParsedInput) : q.evaluateBits = q.evaluate := by
  have hc : bitValue (wordGet q.evaluationBits 0) =
      q.evaluationRemainder.coeff 0 := by
    rw [← coeff_wordPoly, wordPoly_evaluationBits]
  apply Bool.eq_iff_iff.mpr
  rw [evaluate_eq_true_iff]
  unfold evaluateBits
  rw [← hc, bitValue_eq_zero_iff]
  cases wordGet q.evaluationBits 0 <;> decide

end ParsedInput

/-- The bit-level implementation of the explicit language. -/
def languageBits (w : List Bool) : Bool :=
  match parseInput w with
  | none => false
  | some q => q.evaluateBits

theorem languageBits_eq_language (w : List Bool) : languageBits w = language w := by
  unfold languageBits language
  cases parseInput w with
  | none => rfl
  | some q => exact q.evaluateBits_eq

end DepthThreeLowerBound

end Complexity
