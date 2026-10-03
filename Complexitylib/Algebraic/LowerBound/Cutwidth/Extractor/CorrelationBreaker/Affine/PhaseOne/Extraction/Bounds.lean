/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Bounds.Internal

/-!
# Finite source reserves for the first affine phase

The initial source threshold and the final threshold with both observed
output lengths suffice for the actual pairwise error bound. Three extra
bits in every local error exponent pay for all five error contributions.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Explicit original-source reserves give the requested complete first-phase error. -/
theorem affinePhaseOneError_dyadic_le (t h L₀ L₁ target k : Nat) {mass : ℝ}
    (initial : 2 ^ 142 * L₀ + (target + 3) ≤ k)
    (final : 2 ^ (2 * h + 14) * L₁ + matchedBlockOutputBits h L₁ +
      (t + 1) * matchedBlockOutputBits 64 L₀ + (target + 3) ≤ k)
    (source : mass ≤ ((2 : ℝ) ^ k)⁻¹) :
    affinePhaseOneError t h L₀ (target + 3) L₁ (target + 3) (target + 3) mass ≤
      ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affinePhaseOneError_dyadic_le t h L₀ L₁ target k initial final source

end Algebraic.Cutwidth.Extractor
