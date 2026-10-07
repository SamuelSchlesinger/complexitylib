/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraLanguage
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Circuit
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.InterpolationQuotient
public import Mathlib.Data.List.OfFn
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: language slice

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageSlice.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- Fix the parameter bits while leaving the data variables free. -/
def parameterSlice {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) : Fin n → Sum (Fin d) Bool :=
  fun i =>
    if hd : i.val < d then .inl ⟨i.val, hd⟩
    else if hu : i.val - d < d + r - 1 then .inr (u ⟨i.val - d, hu⟩)
    else if hp : i.val - (d + (d + r - 1)) < r then
      .inr (p ⟨i.val - (d + (d + r - 1)), hp⟩)
    else if hb : (i.val - (d + (d + r - 1) + r)) / r < t then
      if hi : (i.val - (d + (d + r - 1) + r)) % r < r then
        .inr (b ⟨(i.val - (d + (d + r - 1) + r)) / r, hb⟩
          ⟨(i.val - (d + (d + r - 1) + r)) % r, hi⟩)
      else .inr false
    else .inr false

theorem parameterSlice_data {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin d) (hn : i.val < n) :
    parameterSlice u p b ⟨i.val, hn⟩ = Sum.inl i := by
  simp [parameterSlice, i.is_lt]

theorem parameterSlice_hash {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin (d + r - 1))
    (hn : d + i.val < n) :
    parameterSlice u p b ⟨d + i.val, hn⟩ = Sum.inr (u i) := by
  have hd : ¬d + i.val < d := by omega
  simp [parameterSlice, hd, i.is_lt]

theorem parameterSlice_polynomial {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin r)
    (hn : d + (d + r - 1) + i.val < n) :
    parameterSlice u p b ⟨d + (d + r - 1) + i.val, hn⟩ = Sum.inr (p i) := by
  have hd : ¬d + (d + r - 1) + i.val < d := by omega
  have hu : ¬d + (d + r - 1) + i.val - d < d + r - 1 := by omega
  simp [parameterSlice, hd, hu, i.is_lt]

theorem parameterSlice_coefficient {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (j : Fin t) (i : Fin r)
    (hn : d + (d + r - 1) + r + j.val * r + i.val < n) :
    parameterSlice u p b
        ⟨d + (d + r - 1) + r + j.val * r + i.val, hn⟩ =
      Sum.inr (b j i) := by
  have hr : 0 < r := Nat.zero_lt_of_lt i.is_lt
  have hd : ¬d + (d + r - 1) + r + j.val * r + i.val < d := by omega
  have hu : ¬d + (d + r - 1) + r + j.val * r + i.val - d < d + r - 1 := by
    omega
  have hp : ¬d + (d + r - 1) + r + j.val * r + i.val -
      (d + (d + r - 1)) < r := by omega
  have hs : d + (d + r - 1) + r + j.val * r + i.val -
      (d + (d + r - 1) + r) = j.val * r + i.val := by omega
  have hdiv : (j.val * r + i.val) / r = j.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt i.is_lt,
      Nat.zero_add]
  have hmod : (j.val * r + i.val) % r = i.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.is_lt]
  simp [parameterSlice, hd, hu, hp, hs, hdiv, hmod, j.is_lt, i.is_lt]

theorem parameterSlice_suffix {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin n)
    (hi : d + (d + r - 1) + r + t * r ≤ i.val) :
    parameterSlice u p b i = Sum.inr false := by
  have hd : ¬i.val < d := by omega
  have hu : ¬i.val - d < d + r - 1 := by omega
  have hp : ¬i.val - (d + (d + r - 1)) < r := by omega
  by_cases hr : r = 0
  · simp only [parameterSlice, dite_eq_right hd, dite_eq_right hu, dite_eq_right hp]
    simp [hr]
  · have hr' : 0 < r := Nat.pos_of_ne_zero hr
    have hmul : t * r ≤ i.val - (d + (d + r - 1) + r) := by omega
    have hdiv : t ≤ (i.val - (d + (d + r - 1) + r)) / r :=
      (Nat.le_div_iff_mul_le hr').2 hmul
    simp [parameterSlice, hd, hu, hp, Nat.not_lt.mpr hdiv]

/-- The parsed input obtained from a fixed-parameter slice. -/
def sliceParsedInput (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool)
    (x : Fin (dataDimension n) → Bool) : ParsedInput where
  dataSize := dataDimension n
  ringDegree := hashDimension (dataDimension n)
  coefficientCount := independenceOrder (dataDimension n)
  data := x
  hashSeed := u
  polynomial := p
  coefficients := b

/-- The canonical input substitution fixing a chosen parameter tuple. -/
def canonicalSlice (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool) :
    Fin n → Sum (Fin (dataDimension n)) Bool := parameterSlice u p b

/-- Encode a data assignment as a word in the canonical slice. -/
def canonicalSliceWord (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool)
    (x : Fin (dataDimension n) → Bool) : List Bool :=
  List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)

@[simp] theorem canonicalSliceWord_length (n : ℕ) (u p b x) :
    (canonicalSliceWord n u p b x).length = n := List.length_ofFn

theorem canonicalSlice_first (n : ℕ) (u p b) (i : Fin (dataDimension n)) :
    canonicalSlice n u p b
      ⟨i.val, i.is_lt.trans_le (Nat.div_le_self n 5)⟩ = Sum.inl i :=
  parameterSlice_data u p b i _

theorem canonicalSlice_unused (n : ℕ) (u p b) (i : Fin n)
    (hi : blockLen (dataDimension n) ≤ i.val) :
    canonicalSlice n u p b i = Sum.inr false := by
  apply parameterSlice_suffix
  simpa only [blockLen_eq_sum] using hi

private theorem getD_ofFn_at {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, List.length_ofFn, hi]

theorem canonicalSliceWord_fits (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    InputFits (canonicalSliceWord n u p b x) := by
  simpa only [InputFits, canonicalSliceWord_length] using And.intro hd (And.intro ht hlen)

theorem decodeInput_canonicalSliceWord (n : ℕ) (u p b x)
    (_hd : 0 < dataDimension n)
    (_ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    decodeInput (canonicalSliceWord n u p b x) = sliceParsedInput n u p b x := by
  let readAtLength (m : ℕ) : ParsedInput :=
    { dataSize := dataDimension m
      ringDegree := hashDimension (dataDimension m)
      coefficientCount := independenceOrder (dataDimension m)
      data := fun i => (canonicalSliceWord n u p b x).getD i.val false
      hashSeed := fun i => (canonicalSliceWord n u p b x).getD
        (hashOffset (dataDimension m) + i.val) false
      polynomial := fun i => (canonicalSliceWord n u p b x).getD
        (polynomialOffset (dataDimension m) + i.val) false
      coefficients := fun j i => (canonicalSliceWord n u p b x).getD
        (coefficientOffset (dataDimension m) j.val + i.val) false }
  change readAtLength (canonicalSliceWord n u p b x).length = _
  rw [canonicalSliceWord_length]
  dsimp only [readAtLength, sliceParsedInput]
  congr 1
  · funext i
    have hi : i.val < n := i.is_lt.trans_le (Nat.div_le_self n 5)
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    simp [GateInput.assignment, canonicalSlice_first]
  · funext i
    have hi : hashOffset (dataDimension n) + i.val < n := by
      exact (Nat.add_lt_add_left i.is_lt _).trans_le
        ((polynomialOffset_le_coefficientsOffset _).trans
          ((coefficientsOffset_le_blockLen _).trans hlen))
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    have hi' : dataDimension n + i.val < n := by
      simpa only [hashOffset] using hi
    change GateInput.assignment (parameterSlice u p b) x
      ⟨dataDimension n + i.val, hi'⟩ = u i
    rw [GateInput.assignment, parameterSlice_hash]
  · funext i
    have hi : polynomialOffset (dataDimension n) + i.val < n := by
      exact (polynomial_index_lt i.is_lt).trans_le
        ((coefficientsOffset_le_blockLen _).trans hlen)
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    have hi' : dataDimension n +
        (dataDimension n + hashDimension (dataDimension n) - 1) + i.val < n := by
      simpa only [polynomialOffset_eq] using hi
    change GateInput.assignment (parameterSlice u p b) x
      ⟨dataDimension n + (dataDimension n + hashDimension (dataDimension n) - 1) +
        i.val, hi'⟩ = p i
    rw [GateInput.assignment, parameterSlice_polynomial]
  · funext j i
    have hi : coefficientOffset (dataDimension n) j.val + i.val < n := by
      exact (coefficient_index_lt j.is_lt i.is_lt).trans_le hlen
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    have hi' : dataDimension n +
        (dataDimension n + hashDimension (dataDimension n) - 1) +
        hashDimension (dataDimension n) + j.val * hashDimension (dataDimension n) +
        i.val < n := by
      simpa only [coefficientOffset, coefficientsOffset_eq] using hi
    change GateInput.assignment (parameterSlice u p b) x
      ⟨dataDimension n + (dataDimension n + hashDimension (dataDimension n) - 1) +
        hashDimension (dataDimension n) + j.val * hashDimension (dataDimension n) +
        i.val, hi'⟩ = b j i
    rw [GateInput.assignment, parameterSlice_coefficient]

theorem language_canonicalSliceWord (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (canonicalSliceWord n u p b x) = (sliceParsedInput n u p b x).evaluate := by
  rw [language_of_fits (canonicalSliceWord_fits n u p b x hd ht hlen),
    decodeInput_canonicalSliceWord n u p b x hd ht hlen]

theorem language_ofFn_canonicalSlice (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)) =
      (sliceParsedInput n u p b x).evaluate :=
  language_canonicalSliceWord n u p b x hd ht hlen

theorem language_canonicalSlice_quotient (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)) = true ↔
      BinaryAlgebra.degreeZero (sliceParsedInput n u p b x).modulus_monic
        (sliceParsedInput n u p b x).quotientEvaluation = 0 := by
  rw [language_ofFn_canonicalSlice n u p b x hd ht hlen,
    ParsedInput.evaluate_eq_true_iff_degreeZero]

theorem language_canonicalSlice_acceptEval (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool)
    (x : Fin (dataDimension n) → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)) =
      Interpolation.acceptEval
        (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p))
        (independenceOrder (dataDimension n))
        (fun y : Fin (dataDimension n) → Bool =>
          BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
            (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool u y i)))
        (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
          (fun i => BinaryAlgebra.bitValue (b j i))) x := by
  apply Bool.eq_iff_iff.mpr
  exact (language_canonicalSlice_quotient n u p b x hd ht hlen).trans
    (Interpolation.acceptEval_eq_true
      (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p))
      (independenceOrder (dataDimension n))
      (fun y : Fin (dataDimension n) → Bool =>
        BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
          (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool u y i)))
      (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
        (fun i => BinaryAlgebra.bitValue (b j i))) x).symm

end DepthThreeLowerBound

end Complexity
