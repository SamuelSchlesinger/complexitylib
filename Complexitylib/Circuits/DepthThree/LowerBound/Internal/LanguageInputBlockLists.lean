/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageParser
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.DeriveFintype

/-!
# Unrestricted depth-three lower bound: language input block lists

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageInputBlockLists.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- Kinds of parameter and data blocks in the encoded input. -/
inductive InputBlockKind where
  | data
  | hash
  | polynomial
  | coefficients
  deriving DecidableEq

instance : Fintype InputBlockKind where
  elems := {.data, .hash, .polynomial, .coefficients}
  complete := by
    intro kind
    cases kind <;> simp

/-- The starting position of the selected input block. -/
def inputBlockOffset (n : ℕ) : InputBlockKind → ℕ
  | .data => 0
  | .hash => hashOffset (dataDimension n)
  | .polynomial => polynomialOffset (dataDimension n)
  | .coefficients => coefficientsOffset (dataDimension n)

/-- The length of the selected input block. -/
def inputBlockLength (n : ℕ) : InputBlockKind → ℕ
  | .data => dataDimension n
  | .hash => hashBlockLength (dataDimension n)
  | .polynomial => hashDimension (dataDimension n)
  | .coefficients => independenceOrder (dataDimension n) * hashDimension (dataDimension n)

/-- Extract the selected block from the input word. -/
def inputBlockData (w : List Bool) (kind : InputBlockKind) : List Bool :=
  (w.drop (inputBlockOffset w.length kind)).take (inputBlockLength w.length kind)

theorem inputBlock_end_le {w : List Bool} (h : InputFits w) (kind : InputBlockKind) :
    inputBlockOffset w.length kind + inputBlockLength w.length kind ≤ w.length := by
  cases kind with
  | data =>
    simpa only [inputBlockOffset, inputBlockLength, Nat.zero_add, dataDimension] using
      Nat.div_le_self w.length 5
  | hash =>
    change polynomialOffset (dataDimension w.length) ≤ w.length
    exact (polynomialOffset_le_coefficientsOffset _).trans
      ((coefficientsOffset_le_blockLen _).trans h.2.2)
  | polynomial =>
    change coefficientsOffset (dataDimension w.length) ≤ w.length
    exact (coefficientsOffset_le_blockLen _).trans h.2.2
  | coefficients =>
    exact h.2.2

theorem inputBlock_offset_le {w : List Bool} (h : InputFits w) (kind : InputBlockKind) :
    inputBlockOffset w.length kind ≤ w.length := by
  have hb := inputBlock_end_le h kind
  omega

theorem inputBlock_prefix_length {w : List Bool} (h : InputFits w)
    (kind : InputBlockKind) :
    (w.take (inputBlockOffset w.length kind)).length = inputBlockOffset w.length kind :=
  List.length_take_of_le (inputBlock_offset_le h kind)

theorem inputBlockData_length {w : List Bool} (h : InputFits w) (kind : InputBlockKind) :
    (inputBlockData w kind).length = inputBlockLength w.length kind := by
  unfold inputBlockData
  rw [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  have hb := inputBlock_end_le h kind
  omega

theorem inputBlock_reconstruct (w : List Bool) (kind : InputBlockKind) :
    w = w.take (inputBlockOffset w.length kind) ++ inputBlockData w kind ++
      w.drop (inputBlockOffset w.length kind + inputBlockLength w.length kind) := by
  calc
    w = w.take (inputBlockOffset w.length kind) ++
        w.drop (inputBlockOffset w.length kind) :=
      (List.take_append_drop _ _).symm
    _ = w.take (inputBlockOffset w.length kind) ++
        ((w.drop (inputBlockOffset w.length kind)).take (inputBlockLength w.length kind) ++
          (w.drop (inputBlockOffset w.length kind)).drop (inputBlockLength w.length kind)) :=
      congrArg (fun tail => w.take (inputBlockOffset w.length kind) ++ tail)
        (List.take_append_drop _ _).symm
    _ = _ := by simp only [inputBlockData, List.drop_drop, List.append_assoc]

theorem inputBlockData_getD (w : List Bool) (kind : InputBlockKind) {i : ℕ}
    (hi : i < inputBlockLength w.length kind) :
    (inputBlockData w kind).getD i false =
      w.getD (inputBlockOffset w.length kind + i) false := by
  simp only [inputBlockData, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem inputBlockData_data_nat (w : List Bool) {i : ℕ}
    (hi : i < dataDimension w.length) :
    (inputBlockData w .data).getD i false = (decodeInput w).data ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, Nat.zero_add, decodeInput] using
    inputBlockData_getD w .data hi

theorem inputBlockData_data (w : List Bool) (i : Fin (dataDimension w.length)) :
    (inputBlockData w .data).getD i.val false = (decodeInput w).data i :=
  inputBlockData_data_nat w i.isLt

theorem inputBlockData_hash_nat (w : List Bool) {i : ℕ}
    (hi : i < hashBlockLength (dataDimension w.length)) :
    (inputBlockData w .hash).getD i false = (decodeInput w).hashSeed ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, decodeInput] using inputBlockData_getD w .hash hi

theorem inputBlockData_hash (w : List Bool)
    (i : Fin (hashBlockLength (dataDimension w.length))) :
    (inputBlockData w .hash).getD i.val false = (decodeInput w).hashSeed i :=
  inputBlockData_hash_nat w i.isLt

theorem inputBlockData_polynomial_nat (w : List Bool) {i : ℕ}
    (hi : i < hashDimension (dataDimension w.length)) :
    (inputBlockData w .polynomial).getD i false = (decodeInput w).polynomial ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, decodeInput] using inputBlockData_getD w .polynomial hi

theorem inputBlockData_polynomial (w : List Bool)
    (i : Fin (hashDimension (dataDimension w.length))) :
    (inputBlockData w .polynomial).getD i.val false = (decodeInput w).polynomial i :=
  inputBlockData_polynomial_nat w i.isLt

theorem inputBlock_coefficient_index_lt {n j i : ℕ}
    (hj : j < independenceOrder (dataDimension n))
    (hi : i < hashDimension (dataDimension n)) :
    j * hashDimension (dataDimension n) + i < inputBlockLength n .coefficients := by
  have hmul := Nat.mul_le_mul_right (hashDimension (dataDimension n))
    (Nat.succ_le_of_lt hj)
  simp only [Nat.succ_mul] at hmul
  change j * hashDimension (dataDimension n) + i <
    independenceOrder (dataDimension n) * hashDimension (dataDimension n)
  omega

theorem inputBlockData_coefficients_nat (w : List Bool) {j i : ℕ}
    (hj : j < independenceOrder (dataDimension w.length))
    (hi : i < hashDimension (dataDimension w.length)) :
    (inputBlockData w .coefficients).getD
        (j * hashDimension (dataDimension w.length) + i) false =
      (decodeInput w).coefficients ⟨j, hj⟩ ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, decodeInput, coefficientOffset, Nat.add_assoc] using
    inputBlockData_getD w .coefficients (inputBlock_coefficient_index_lt hj hi)

theorem inputBlockData_coefficients (w : List Bool)
    (j : Fin (independenceOrder (dataDimension w.length)))
    (i : Fin (hashDimension (dataDimension w.length))) :
    (inputBlockData w .coefficients).getD
        (j.val * hashDimension (dataDimension w.length) + i.val) false =
      (decodeInput w).coefficients j i :=
  inputBlockData_coefficients_nat w j.isLt i.isLt

end DepthThreeLowerBound

end Complexity
