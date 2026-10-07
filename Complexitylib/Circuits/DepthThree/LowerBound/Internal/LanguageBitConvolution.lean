/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitWord
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn

/-!
# Unrestricted depth-three lower bound: language bit convolution

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitConvolution.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

open scoped BigOperators

/-- Pointwise XOR of bit sequences. -/
def xorBits (xs : List Bool) : Bool := xs.foldr Bool.xor false

@[simp] theorem xorBits_nil : xorBits [] = false := rfl

@[simp] theorem xorBits_cons (x : Bool) (xs : List Bool) :
    xorBits (x :: xs) = Bool.xor x (xorBits xs) := rfl

theorem bitValue_xorBits (xs : List Bool) :
    BinaryAlgebra.bitValue (xorBits xs) = (xs.map BinaryAlgebra.bitValue).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change BinaryAlgebra.bitValue (Bool.xor x (xorBits xs)) =
        BinaryAlgebra.bitValue x + (xs.map BinaryAlgebra.bitValue).sum
      rw [BinaryAlgebra.bitValue_xor, ih]

theorem bitValue_xorBits_ofFn {n : ℕ} (f : Fin n → Bool) :
    BinaryAlgebra.bitValue (xorBits (List.ofFn f)) =
      ∑ i : Fin n, BinaryAlgebra.bitValue (f i) := by
  simp only [bitValue_xorBits, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

/-- Convolve bit words over the two-element field. -/
def wordConvolve {r s : ℕ} (a : BitWord r) (b : BitWord s) : BitWord (r + s) :=
  fun k => xorBits (List.ofFn fun i : Fin r =>
    xorBits (List.ofFn fun j : Fin s =>
      if i.val + j.val = k.val then a i && b j else false))

theorem coeff_wordPoly_mul {r s : ℕ} (a : BitWord r) (b : BitWord s) (k : ℕ) :
    (wordPoly a * wordPoly b).coeff k =
      ∑ i : Fin r, ∑ j : Fin s,
        if i.val + j.val = k then
          BinaryAlgebra.bitValue (a i) * BinaryAlgebra.bitValue (b j)
        else 0 := by
  classical
  simp only [wordPoly, BinaryAlgebra.pack, Finset.sum_mul_sum,
    Polynomial.monomial_mul_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]

theorem wordPoly_convolve {r s : ℕ} (a : BitWord r) (b : BitWord s) :
    wordPoly (wordConvolve a b) = wordPoly a * wordPoly b := by
  ext k
  rw [coeff_wordPoly, coeff_wordPoly_mul]
  by_cases hk : k < r + s
  · rw [wordGet_of_lt _ hk]
    simp only [wordConvolve, bitValue_xorBits_ofFn, apply_ite,
      BinaryAlgebra.bitValue_and, BinaryAlgebra.bitValue_false]
  · rw [wordGet_of_le _ (Nat.le_of_not_lt hk), BinaryAlgebra.bitValue_false]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hsum : i.val + j.val < r + s := Nat.add_lt_add i.is_lt j.is_lt
    have hne : i.val + j.val ≠ k := by omega
    simp [hne]

/-- Read a finite bit word as a list. -/
def wordList {n : ℕ} (a : BitWord n) : List Bool := List.ofFn a

/-- Read a bit list as a finite bit word. -/
def listWord (n : ℕ) (xs : List Bool) : BitWord n :=
  fun i => xs.getD i.val false

@[simp] theorem wordList_length {n : ℕ} (a : BitWord n) :
    (wordList a).length = n := List.length_ofFn

theorem wordList_getD {n : ℕ} (a : BitWord n) (i : ℕ) :
    (wordList a).getD i false = wordGet a i := by
  by_cases hi : i < n <;> simp [wordList, wordGet, hi]

@[simp] theorem listWord_wordList {n : ℕ} (a : BitWord n) :
    listWord n (wordList a) = a := by
  funext i
  change (wordList a).getD i.val false = a i
  rw [wordList_getD, wordGet_fin]

theorem wordList_listWord_length (xs : List Bool) :
    wordList (listWord xs.length xs) = xs := by
  apply List.ext_getElem
  · simp [wordList]
  · intro i _ hi
    simp [wordList, listWord, List.getElem?_eq_getElem hi]

theorem wordList_listWord {n : ℕ} (xs : List Bool) (h : xs.length = n) :
    wordList (listWord n xs) = xs := by
  subst n
  exact wordList_listWord_length xs

end DepthThreeLowerBound

end Complexity
