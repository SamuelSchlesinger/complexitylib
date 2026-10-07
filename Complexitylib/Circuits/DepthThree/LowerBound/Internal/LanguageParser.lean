/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageParameters
public import Mathlib.Data.List.GetD

/-!
# Unrestricted depth-three lower bound: language parser

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageParser.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- The data, hash seed, modulus bits, and coefficients parsed from an input word. -/
structure ParsedInput where
  /-- Number of data bits. -/
  dataSize : ℕ
  /-- Degree of the monic modulus polynomial. -/
  ringDegree : ℕ
  /-- Number of coefficient blocks. -/
  coefficientCount : ℕ
  /-- The input data bits. -/
  data : Fin dataSize → Bool
  /-- The seed bits for the linear hash. -/
  hashSeed : Fin (dataSize + ringDegree - 1) → Bool
  /-- The lower coefficients of the monic modulus. -/
  polynomial : Fin ringDegree → Bool
  /-- The coefficient blocks of the evaluation polynomial. -/
  coefficients : Fin coefficientCount → Fin ringDegree → Bool

/-- Extract the parameter blocks and data from an input word. -/
def decodeInput (w : List Bool) : ParsedInput where
  dataSize := dataDimension w.length
  ringDegree := hashDimension (dataDimension w.length)
  coefficientCount := independenceOrder (dataDimension w.length)
  data i := w.getD i.val false
  hashSeed i := w.getD (hashOffset (dataDimension w.length) + i.val) false
  polynomial i := w.getD (polynomialOffset (dataDimension w.length) + i.val) false
  coefficients j i :=
    w.getD (coefficientOffset (dataDimension w.length) j.val + i.val) false

/-- The input has sufficient length for all blocks specified by its parameters. -/
def InputFits (w : List Bool) : Prop :=
  0 < dataDimension w.length ∧
    2 ≤ independenceOrder (dataDimension w.length) ∧
      blockLen (dataDimension w.length) ≤ w.length

instance (w : List Bool) : Decidable (InputFits w) := by
  unfold InputFits
  infer_instance

/-- Parse an input when its parameter blocks fit, rejecting otherwise. -/
def parseInput (w : List Bool) : Option ParsedInput :=
  if InputFits w then some (decodeInput w) else none

theorem parseInput_of_fits {w : List Bool} (h : InputFits w) :
    parseInput w = some (decodeInput w) := by
  simp only [parseInput, ite_eq_left h]

theorem parseInput_of_not_fits {w : List Bool} (h : ¬InputFits w) :
    parseInput w = none := by
  simp only [parseInput, ite_eq_right h]

theorem parseInput_eq_some_iff (w : List Bool) (q : ParsedInput) :
    parseInput w = some q ↔ InputFits w ∧ decodeInput w = q := by
  by_cases h : InputFits w
  · simp [parseInput, h]
  · simp [parseInput, h]

theorem parseInput_eq_none_iff (w : List Bool) :
    parseInput w = none ↔ ¬InputFits w := by
  by_cases h : InputFits w
  · simp [parseInput, h]
  · simp [parseInput, h]

theorem decodeInput_dataSize (w : List Bool) :
    (decodeInput w).dataSize = dataDimension w.length := rfl

theorem decodeInput_ringDegree (w : List Bool) :
    (decodeInput w).ringDegree = hashDimension (dataDimension w.length) := rfl

theorem decodeInput_coefficientCount (w : List Bool) :
    (decodeInput w).coefficientCount = independenceOrder (dataDimension w.length) := rfl

theorem data_read_lt (w : List Bool) (i : Fin (dataDimension w.length)) :
    i.val < w.length :=
  Nat.lt_of_lt_of_le i.isLt (Nat.div_le_self w.length 5)

theorem hash_read_lt {w : List Bool} (h : InputFits w)
    (i : Fin (dataDimension w.length + hashDimension (dataDimension w.length) - 1)) :
    hashOffset (dataDimension w.length) + i.val < w.length := by
  have hi : hashOffset (dataDimension w.length) + i.val <
      polynomialOffset (dataDimension w.length) :=
    Nat.add_lt_add_left i.isLt _
  exact Nat.lt_of_lt_of_le hi (Nat.le_trans (polynomialOffset_le_coefficientsOffset _)
    (Nat.le_trans (coefficientsOffset_le_blockLen _) h.2.2))

theorem polynomial_read_lt {w : List Bool} (h : InputFits w)
    (i : Fin (hashDimension (dataDimension w.length))) :
    polynomialOffset (dataDimension w.length) + i.val < w.length :=
  Nat.lt_of_lt_of_le (polynomial_index_lt i.isLt)
    (Nat.le_trans (coefficientsOffset_le_blockLen _) h.2.2)

theorem coefficient_read_lt {w : List Bool} (h : InputFits w)
    (j : Fin (independenceOrder (dataDimension w.length)))
    (i : Fin (hashDimension (dataDimension w.length))) :
    coefficientOffset (dataDimension w.length) j.val + i.val < w.length :=
  Nat.lt_of_lt_of_le (coefficient_index_lt j.isLt i.isLt) h.2.2

theorem decoded_ringDegree_pos {w : List Bool} (h : InputFits w) :
    0 < (decodeInput w).ringDegree :=
  hashDimension_pos h.1

theorem decoded_coefficientCount_two_le {w : List Bool} (h : InputFits w) :
    2 ≤ (decodeInput w).coefficientCount :=
  h.2.1

end DepthThreeLowerBound

end Complexity
