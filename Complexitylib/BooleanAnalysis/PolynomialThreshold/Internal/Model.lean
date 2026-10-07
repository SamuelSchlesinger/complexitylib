/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum

/-!
# Gotsman--Linial: Model

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/Model.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Polynomial thresholds and average sensitivity

The Boolean cube encodes the sign cube `{−1,1}^n`:
`false` represents `−1` and `true` represents `1`. The public statement
quantifies directly over real multilinear polynomials and uses uniform counting
probability, the convention `sign(0) = 1`, and the exact constant `8`.

`GotsmanLinialStatement` is a proposition definition, not a proof of the bound.
-/

open scoped BigOperators

namespace BooleanAnalysis.PolynomialThreshold.Internal

/-- The sign cube `{−1,1}^n`, with Boolean coordinates encoding the signs. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Interpret a Boolean cube coordinate as the corresponding real sign. -/
def cubeCoord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

/-- Reverse one coordinate of a cube vertex. -/
def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

/-- The threshold convention assigns `1` at zero. -/
noncomputable def thresholdSign (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 else -1

/-- Vertices at which reversing coordinate `i` changes the function. -/
noncomputable def sensitiveVertices {n : ℕ} (f : Cube n → ℝ) (i : Fin n) :
    Finset (Cube n) := by
  classical
  exact Finset.univ.filter fun x => f x ≠ f (flip i x)

/-- Number of ordered sensitive edges, indexed by their initial vertex and direction. -/
noncomputable def sensitiveEdgeCount {n : ℕ} (f : Cube n → ℝ) : ℕ :=
  ∑ i : Fin n, (sensitiveVertices f i).card

/-- Sum of the uniform probabilities that a coordinate flip changes `f`. -/
noncomputable def averageSensitivity {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  ∑ i : Fin n, ((sensitiveVertices f i).card : ℝ) / (2 : ℝ) ^ n

/-- Every exponent in every supported monomial is at most one. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i : Fin n, m i ≤ 1

/-- Evaluate a real polynomial at the signs represented by a cube vertex. -/
noncomputable def polynomialValue {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Cube n) : ℝ :=
  MvPolynomial.eval (cubeCoord x) p

/-- The polynomial threshold function with the nonnegative-at-zero convention. -/
noncomputable def polynomialThreshold {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Cube n → ℝ :=
  fun x => thresholdSign (polynomialValue p x)

/-- The average-sensitivity bound for positive dimension and degree at most the dimension. -/
def GotsmanLinialStatement : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → d ≤ n →
    ∀ p : MvPolynomial (Fin n) ℝ,
      IsMultilinear p → p.totalDegree ≤ d →
        averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ)

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
