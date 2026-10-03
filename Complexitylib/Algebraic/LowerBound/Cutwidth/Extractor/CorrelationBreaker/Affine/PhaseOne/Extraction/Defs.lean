/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Defs

/-!
# The finite error budget of the actual first affine phase

The first extraction, advice call, and final extraction each contribute
their own dyadic error. Original-source mass pays the initial threshold
and the final threshold together with the observed first-output family
and one tampered final output. This records the actual three-call bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The complete pairwise error from the three actual calls and the original left-source mass. -/
noncomputable def affinePhaseOneError (t h L₀ e₀ L₁ target er : Nat) (mass : ℝ) : ℝ :=
  ((2 : ℝ) ^ er)⁻¹ +
    (((2 : ℝ) ^ e₀)⁻¹ + (2 : ℝ) ^ (2 ^ 142 * L₀) * mass + ((2 : ℝ) ^ target)⁻¹) +
    (2 : ℝ) ^ (2 ^ (2 * h + 14) * L₁ + matchedBlockOutputBits h L₁ +
      (t + 1) * matchedBlockOutputBits 64 L₀) * mass

end Algebraic.Cutwidth.Extractor
