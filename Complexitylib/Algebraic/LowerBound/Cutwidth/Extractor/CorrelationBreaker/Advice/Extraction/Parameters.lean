/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Parameters.Internal

/-!
# The actual advice program at selected finite parameters

The total chooser fixes the right-source length and left-source entropy
reserve `m`, common scale `L`, and local error exponent `e`. For unequal
advice strings of the same chosen length, the actual program returns the
requested `out` bits with error at most `2^(-target)`, retaining the entire
original right state and the actual truncated tampered output.

Inputs are independent conditional on the shared tag. The honest right
input is uniform on every row; the honest left input has the stated average
joint point-mass envelope. These original-source hypotheses govern whether
the entropy reserve is feasible; the chooser does not assert that it fits
every left-input width. No program guard, primitive extractor certificate,
intermediate security witness, or field instance is supplied by the caller.

The construction follows Chattopadhyay--Goyal--Li Algorithm 2,
<https://arxiv.org/abs/1505.00107>, with an additional final extraction from
the original left source. The explicit constants and conservative finite
error accounting are checked deductions of this library. A uniform
evaluator for these selected parameters is a separate runtime layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- The explicit finite chooser gives the requested actual output width and dyadic error. -/
theorem adviceTruncatedCorrelationBreaker_parameters_dist_le (n a target out : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (y y' : Z → B → Fin (adviceSourceEntropy n a target out) → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (y z) (r z) =
      uniformWeight (Fin (adviceSourceEntropy n a target out) → Bool))
    (length : advice.length = a) (length' : advice'.length = a)
    (different : advice ≠ advice')
    (left : (∑ z, μ z) ≤ ((2 : ℝ) ^ adviceSourceEntropy n a target out)⁻¹) :
    let m := adviceSourceEntropy n a target out
    let L := adviceScale n a target out
    let e := adviceErrorExponent a target
    let actual := adviceTruncatedCorrelationBreakerWeight n m L e out
      w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ :=
  Internal.adviceTruncatedCorrelationBreaker_parameters_dist_le n a target out
    w l r x x' y y' advice advice' μ hw hl hr nonnegative cap uniform length length' different left

end Algebraic.Cutwidth.Extractor
