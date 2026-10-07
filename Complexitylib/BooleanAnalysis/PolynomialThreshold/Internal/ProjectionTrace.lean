/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace

/-!
# Gotsman--Linial: ProjectionTrace

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/ProjectionTrace.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Traces of actual orthogonal projections

The trace calculation uses the algebraic theorem for a projection onto a
submodule. In particular, no spectral decomposition or matrix norm instance
is needed. Matrix transport is valid in every basis, and hence in the
orthonormal basis used for the weighted grading.
-/

noncomputable section

namespace BooleanAnalysis.PolynomialThreshold.Internal

section General

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The actual orthogonal projection is algebraically a projection onto its
specified submodule. -/
theorem starProjection_isProj (K : Submodule 𝕜 E) :
    LinearMap.IsProj K K.starProjection.toLinearMap where
  map_mem := K.starProjection_apply_mem
  map_id := fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx

/-- The trace of the actual orthogonal projection is the dimension of its range. -/
theorem trace_starProjection (K : Submodule 𝕜 E) :
    LinearMap.trace 𝕜 E K.starProjection.toLinearMap = (Module.finrank 𝕜 K : 𝕜) :=
  (starProjection_isProj K).trace

variable [Fintype ι] [DecidableEq ι]

/-- The matrix trace of an orthogonal projection is independent of the chosen basis. -/
theorem trace_toMatrix_starProjection (b : Module.Basis ι 𝕜 E) (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrix b b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) := by
  rw [← LinearMap.trace_eq_matrix_trace 𝕜 b, trace_starProjection]

/-- The orthonormal matrix representation used by the grading has the correct trace. -/
theorem trace_toMatrixOrthonormal_starProjection (b : OrthonormalBasis ι 𝕜 E)
    (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) :=
  trace_toMatrix_starProjection b.toBasis K

end General

section Complex

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

/-- The real trace required by Hilbert--Schmidt block-mass computations. -/
theorem re_trace_toMatrixOrthonormal_starProjection (b : OrthonormalBasis ι ℂ E)
    (K : Submodule ℂ E) :
    (Matrix.trace (LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap)).re =
      (Module.finrank ℂ K : ℝ) := by
  rw [trace_toMatrixOrthonormal_starProjection]
  simp

end Complex

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity
