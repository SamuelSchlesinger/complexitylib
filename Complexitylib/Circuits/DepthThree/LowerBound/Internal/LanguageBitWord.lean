/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraPolynomial

/-!
# Unrestricted depth-three lower bound: language bit word

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitWord.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

open BinaryAlgebra

/-- A finite Boolean coefficient vector. -/
abbrev BitWord (n : ℕ) := Fin n → Bool

/-- Interpret a finite bit word as a binary polynomial. -/
noncomputable def wordPoly {n : ℕ} (a : BitWord n) : Polynomial (ZMod 2) :=
  BinaryAlgebra.pack (fun i => BinaryAlgebra.bitValue (a i))

/-- Pointwise XOR of finite bit words. -/
def wordXor {n : ℕ} (a b : BitWord n) : BitWord n :=
  fun i => Bool.xor (a i) (b i)

/-- Read a bit-word entry with false as the out-of-range default. -/
def wordGet {n : ℕ} (a : BitWord n) (i : ℕ) : Bool :=
  if h : i < n then a ⟨i, h⟩ else false

/-- The coefficient word of the shifted modulus polynomial. -/
def shiftModulus {r m : ℕ} (p : BitWord r) (s : ℕ) : BitWord m :=
  fun i => if i.val = s + r then true
    else if h : s ≤ i.val ∧ i.val < s + r then
      p ⟨i.val - s, by omega⟩
    else false

@[simp] theorem wordGet_fin {n : ℕ} (a : BitWord n) (i : Fin n) :
    wordGet a i.val = a i := by
  simp [wordGet, i.is_lt]

theorem wordGet_of_lt {n : ℕ} (a : BitWord n) {i : ℕ} (hi : i < n) :
    wordGet a i = a ⟨i, hi⟩ := by
  simp [wordGet, hi]

theorem wordGet_of_le {n : ℕ} (a : BitWord n) {i : ℕ} (hi : n ≤ i) :
    wordGet a i = false := by
  simp [wordGet, Nat.not_lt.mpr hi]

@[simp] theorem wordGet_wordXor {n : ℕ} (a b : BitWord n) (i : ℕ) :
    wordGet (wordXor a b) i = Bool.xor (wordGet a i) (wordGet b i) := by
  by_cases hi : i < n <;> simp [wordGet, wordXor, hi]

theorem coeff_wordPoly {n : ℕ} (a : BitWord n) (i : ℕ) :
    (wordPoly a).coeff i = BinaryAlgebra.bitValue (wordGet a i) := by
  rw [wordPoly, BinaryAlgebra.coeff_pack_nat]
  by_cases hi : i < n <;> simp [wordGet, hi]

@[simp] theorem coeff_wordPoly_fin {n : ℕ} (a : BitWord n) (i : Fin n) :
    (wordPoly a).coeff i.val = BinaryAlgebra.bitValue (a i) := by
  rw [coeff_wordPoly, wordGet_fin]

theorem wordPoly_injective {n : ℕ} :
    Function.Injective (wordPoly : BitWord n → Polynomial (ZMod 2)) := by
  intro a b h
  funext i
  apply BinaryAlgebra.bitValue_injective
  simpa only [coeff_wordPoly_fin] using
    congrArg (fun f : Polynomial (ZMod 2) => f.coeff i.val) h

@[simp] theorem wordPoly_zero (n : ℕ) :
    wordPoly (fun _ : Fin n => false) = 0 := by
  change BinaryAlgebra.pack (0 : Fin n → ZMod 2) = 0
  exact BinaryAlgebra.pack_zero

theorem wordPoly_xor {n : ℕ} (a b : BitWord n) :
    wordPoly (wordXor a b) = wordPoly a + wordPoly b := by
  unfold wordPoly wordXor
  simp only [BinaryAlgebra.bitValue_xor]
  exact BinaryAlgebra.pack_add
    (fun i => BinaryAlgebra.bitValue (a i))
    (fun i => BinaryAlgebra.bitValue (b i))

theorem degree_wordPoly_lt {n : ℕ} (a : BitWord n) :
    (wordPoly a).degree < (n : WithBot ℕ) :=
  BinaryAlgebra.degree_pack_lt _

theorem degree_wordPoly_lt_of_zero_tail {n r : ℕ} (a : BitWord n)
    (h : ∀ i : ℕ, r ≤ i → wordGet a i = false) :
    (wordPoly a).degree < (r : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero (wordPoly a) r).2
  intro i hi
  rw [coeff_wordPoly, h i hi, BinaryAlgebra.bitValue_false]

theorem degree_wordPoly_lt_of_tail_false {n r : ℕ} (a : BitWord n)
    (h : ∀ i : Fin n, r ≤ i.val → a i = false) :
    (wordPoly a).degree < (r : WithBot ℕ) := by
  apply degree_wordPoly_lt_of_zero_tail
  intro i hi
  by_cases hin : i < n
  · rw [wordGet_of_lt a hin]
    exact h ⟨i, hin⟩ hi
  · exact wordGet_of_le a (Nat.le_of_not_lt hin)

theorem inputPolynomialBits_eq_wordPoly {r : ℕ} (p : BitWord r) :
    BinaryAlgebra.inputPolynomialBits p = Polynomial.X ^ r + wordPoly p := rfl

@[simp] theorem shiftModulus_top {r m : ℕ} (p : BitWord r) (s : ℕ)
    (h : s + r < m) :
    shiftModulus (m := m) p s ⟨s + r, h⟩ = true := by
  simp [shiftModulus]

theorem shiftModulus_above {r m : ℕ} (p : BitWord r) (s : ℕ)
    (i : Fin m) (h : s + r < i.val) :
    shiftModulus p s i = false := by
  have he : i.val ≠ s + r := by omega
  have hn : ¬ (s ≤ i.val ∧ i.val < s + r) := by omega
  simp [shiftModulus, he, hn]

theorem wordPoly_shiftModulus {r m : ℕ} (p : BitWord r) (s : ℕ)
    (hm : s + r < m) :
    wordPoly (shiftModulus (m := m) p s) =
      Polynomial.X ^ s * BinaryAlgebra.inputPolynomialBits p := by
  ext i
  rw [coeff_wordPoly, Polynomial.coeff_X_pow_mul']
  by_cases hs : s ≤ i
  · rw [ite_eq_left hs]
    by_cases he : i = s + r
    · subst i
      have hsub : s + r - s = r := by omega
      rw [hsub, BinaryAlgebra.inputPolynomialBits_coeff_leading]
      simp [wordGet, shiftModulus, hm]
    · by_cases hl : i < s + r
      · have hi : i < m := hl.trans hm
        have hsub : i - s < r := by omega
        have hc := BinaryAlgebra.inputPolynomialBits_coeff_lt p ⟨i - s, hsub⟩
        change (BinaryAlgebra.inputPolynomialBits p).coeff (i - s) = _ at hc
        rw [hc]
        simp [wordGet, shiftModulus, hi, he, hs, hl]
      · have hsub : r < i - s := by omega
        have hz : (BinaryAlgebra.inputPolynomialBits p).coeff (i - s) = 0 :=
          BinaryAlgebra.inputPolynomial_coeff_of_gt _ hsub
        rw [hz]
        by_cases hi : i < m
        · simp [wordGet, shiftModulus, hi, he, hl]
        · simp [wordGet, hi]
  · rw [ite_eq_right hs]
    have he : i ≠ s + r := by omega
    by_cases hi : i < m
    · simp [wordGet, shiftModulus, hi, he, hs]
    · simp [wordGet, hi]

end DepthThreeLowerBound

end Complexity
