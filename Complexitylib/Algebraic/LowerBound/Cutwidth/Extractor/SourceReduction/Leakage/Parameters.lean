/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parameters.Internal

/-!
# Explicit entropy accounting for leakage-resilient affine calls

The complete source reserve is polynomial in the tampering count, advice
length, target exponent, and logarithm of the original input length. The
extra leakage cost is paid for every honest and tampered seed.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual complete source reserve, including leakage, obeys a finite cubic-base bound. -/
theorem affineLeakageSourceEntropy_le (n t a target : Nat) :
    affineLeakageSourceEntropy n t a target ≤
      2 ^ 258 * (t + 1) ^ 2 * (a + 1) *
        affinePhaseOneBase n t a (affineIterationTarget t target) ^ 3 :=
  Internal.affineLeakageSourceEntropy_le n t a target

end Algebraic.Cutwidth.Extractor
