/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.PolynomialDegree
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.CoordinateMultipliers
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Walsh

/-!
# Gotsman--Linial: CoordinateDegree

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/CoordinateDegree.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Coordinate multiplication raises the Fourier degree by at most one

The unweighted polynomial degree bound is transported to the actual diagonal matrices
and continuous linear operators
on the counting-inner-product Euclidean space, including the shifted flag used
by the weighted grading construction.
-/

noncomputable section

open scoped Matrix

namespace BooleanAnalysis.PolynomialThreshold.Internal

variable {n k : ℕ}

/-- The actual coordinate-sign matrix raises the unweighted degree by at most one. -/
theorem coordinateSignMatrix_mem_fourierSpace (i : Fin n) {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n k) :
    coordinateSignMatrix i *ᵥ a ∈ fourierSpace n (k + 1) := by
  change (fun x => (coordinateSignMatrix i *ᵥ a) x) ∈ fourierSpace n (k + 1)
  simpa only [coordinateSignMatrix_mulVec] using cubeCoord_mul_mem_fourierSpace ha i

/-- The continuous coordinate multiplier has the same degree shift in Euclidean space. -/
theorem coordinateMultiplier_mem_fourierEuclideanSpace (i : Fin n)
    {a : EuclideanSpace ℂ (Cube n)} (ha : a ∈ fourierEuclideanSpace n k) :
    coordinateMultiplier i a ∈ fourierEuclideanSpace n (k + 1) := by
  apply (mem_fourierEuclideanSpace _).2
  simpa only [coordinateMultiplier_apply] using
    cubeCoord_mul_mem_fourierSpace ((mem_fourierEuclideanSpace _).1 ha) i

/-- Submodule-map form of the Euclidean coordinate-degree shift. -/
theorem coordinateMultiplier_map_fourierEuclideanSpace_le (i : Fin n) :
    (fourierEuclideanSpace n k).map (coordinateMultiplier i).toLinearMap ≤
      fourierEuclideanSpace n (k + 1) := by
  rintro a ⟨b, hb, rfl⟩
  exact coordinateMultiplier_mem_fourierEuclideanSpace i hb

/-- The shifted flag also has a one-step coordinate shift, including its bottom term. -/
theorem coordinateMultiplier_fourierFlag_shift (i : Fin n) :
    ∀ k (a : EuclideanSpace ℂ (Cube n)), a ∈ fourierFlag n k →
      coordinateMultiplier i a ∈ fourierFlag n (k + 1) := by
  intro k a ha
  cases k with
  | zero =>
      have ha0 : a = 0 := by simpa using ha
      simp [ha0]
  | succ k =>
      exact coordinateMultiplier_mem_fourierEuclideanSpace i ha

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity
