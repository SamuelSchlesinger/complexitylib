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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation

/-!
# Discharging the finite advice-program parameter premises

The explicit chooser supplies every fixed-depth guard, refreshed-state
width, and entropy reserve of the dyadic advice-chain theorem. Balanced
output truncation then gives the requested number of actual output bits.
Only the original factored source hypotheses remain.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

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
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ := by
  have whole := adviceCorrelationBreaker_dyadic_dist_le n
    (adviceSourceEntropy n a target out) (adviceScale n a target out) target
    w l r x x' y y' advice advice' μ
    (by simpa only [length] using adviceParameters_sizeGuard n a target out)
    (adviceParameters_stateWidth_le n a target out)
    hw hl hr nonnegative cap uniform (length.trans length'.symm) different
    (by simpa only [length, adviceSourceEntropy] using left)
    (by rw [length]; exact le_rfl)
  have shorter := adviceTruncatedCorrelationBreakerWeight_dist_le n
    (adviceSourceEntropy n a target out) (adviceScale n a target out)
    (adviceErrorExponent a target) out w l r x x' y y' advice advice'
    (adviceParameters_output_le n a target out)
  apply shorter.trans
  simpa only [length] using whole

end Algebraic.Cutwidth.Extractor.Internal
