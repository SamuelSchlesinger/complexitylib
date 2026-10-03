/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Perturbed.Internal

/-!
# Advice correlation breaking with an approximately uniform right input

The complete actual program retains the full original right state and
actual tampered output. Its error increases by only the original joint
right-input discrepancy from uniform. The source and tampered program keep
their full joint law during a constructed coordinate repair; no repair
certificate or worst-case conditional uniformity assumption is supplied.

This is the standard-correlation-breaker input step of Chattopadhyay--Liao,
Theorem 6.1, <https://arxiv.org/abs/2110.12652>. In its affine application the
right input here is an earlier extracted value and the left source is the
original uniform seed after transcript observations. The theorem itself
uses the concrete advice program and its checked finite bounds.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- The actual advice program pays the original right-input discrepancy once. -/
theorem adviceCorrelationBreaker_perturbed_dist_le (n m L e : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e) (size : matchedBlockOutputBits 64 L ≤ m)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ ρ)
    (length : advice.length = advice'.length) (different : advice ≠ advice') :
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤
      ρ + adviceCorrelationBreakerError m L e advice.length (∑ z, μ z) :=
  Internal.adviceCorrelationBreaker_perturbed_dist_le n m L e guard size w l r x x' y y' advice advice' μ
    hw hl hr nonnegative cap seed length different

/-- The dyadic guarantee tolerates joint seed error while retaining the actual marginal. -/
theorem adviceCorrelationBreaker_perturbed_dyadic_dist_le (n m L target : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ) {ρ : ℝ}
    (guard : FlipFlopSizeGuard n m L (adviceErrorExponent advice.length target))
    (size : matchedBlockOutputBits 64 L ≤ m)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ ρ)
    (length : advice.length = advice'.length) (different : advice ≠ advice')
    (left : (∑ z, μ z) ≤ ((2 : ℝ) ^ (2 ^ 150 * (advice.length + 1) * L))⁻¹)
    (right : 2 ^ 150 * (advice.length + 1) * L ≤ m) :
    let e := adviceErrorExponent advice.length target
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤ ρ + ((2 : ℝ) ^ target)⁻¹ :=
  Internal.adviceCorrelationBreaker_perturbed_dyadic_dist_le n m L target w l r x x' y y' advice advice' μ guard size
    hw hl hr nonnegative cap seed length different left right

end Algebraic.Cutwidth.Extractor
