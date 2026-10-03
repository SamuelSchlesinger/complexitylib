/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Extraction.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Extraction.Bounds.Internal

/-!
# A dyadic budget for the actual affine round

Explicit reserves for the original sources and the old long row bound each
of the four source charges by one local error. Together with the four
extractor calls, one round contributes at most eight local errors in
addition to its two previous-row discrepancies.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Four finite reserves bound a round by its old errors plus eight local extractor errors. -/
theorem affineRoundError_dyadic_le (t h L e s u kx ky : Nat)
    (ρS ρT : ℝ) {leftMass rightMass : ℝ}
    (first : 2 ^ 62 * L + (s + t + 1) * matchedBlockSeedBits L + e ≤ ky)
    (merge : 2 ^ 62 * L + (s + t + 1) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits h L)
    (recover : 2 ^ 62 * L + (u + 3 * (t + 1)) * matchedBlockSeedBits L + e ≤ ky)
    (final : 2 ^ (2 * h + 14) * L + u * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L + e ≤ kx)
    (left : leftMass ≤ ((2 : ℝ) ^ kx)⁻¹)
    (right : rightMass ≤ ((2 : ℝ) ^ ky)⁻¹) :
    affineRoundError t h L e s u ρS ρT leftMass rightMass ≤
      ρS + ρT + 8 * ((2 : ℝ) ^ e)⁻¹ :=
  Internal.affineRoundError_dyadic_le
    t h L e s u kx ky ρS ρT first merge recover final left right

end Algebraic.Cutwidth.Extractor
