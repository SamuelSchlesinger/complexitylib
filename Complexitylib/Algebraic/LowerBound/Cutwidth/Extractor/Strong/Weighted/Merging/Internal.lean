/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Distance
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Expectation
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Leakage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extraction after two-sided finite leakage

The uniform-seed source retains a joint-mass envelope enlarged only by the
extra leak's alphabet. Both actual and ideal seed laws average the same
bounded discrepancy statistic. The bounded-statistic distance inequality
charges the seed error once while preserving the actual retained marginal.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {Z A B X Seed Out U V W : Type*}
variable [Fintype Z] [Fintype A] [Fintype B] [Fintype X]
variable [Fintype Seed] [Fintype Out] [Fintype U] [Fintype V] [Fintype W]
variable [Nonempty Seed] [Nonempty Out]

theorem weightedStrongSeededExtractor_two_sided_leakage_dist_le
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (μ : Z × U → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ z u₀ x₀,
      w z * mapWeight (fun a => (u z a, x z a)) (l z) (u₀, x₀) ≤ μ (z, u₀))
    (seed : weightDist (observedSeedWeight w r v y)
      (uniformSecondWeight (observedSeedWeight w r v y)) ≤ δ) :
    weightDist (twoSidedExtractionWeight w l r x y u v leak E)
      (uniformSecondWeight (twoSidedExtractionWeight w l r x y u v leak E)) ≤
        ε + δ + (K : ℝ) * Fintype.card W * ∑ t, μ t := by
  have probability := observedSeedWeight_probability w r v y hw hr
  have uniform_probability := probability.uniformSecond
  have range := mergingDistance_range l x u leak E hl
  have shift := weightExpectation_sub_le_dist
    (observedSeedWeight w r v y) (uniformSecondWeight (observedSeedWeight w r v y))
    (mergingDistance l x u leak E)
    (probability.2.trans uniform_probability.2.symm) (fun p => (range p).1)
    (fun p => (range p).2)
  have average := extract.leakage_dist_le error
    (leakageSourceWeight w l r x u v leak)
    (leakageSourceWeight_probability w l r x u v leak hw hl hr)
    (mergingEnvelope r v μ) (mergingEnvelope_nonnegative r v μ hr nonnegative)
    (leakageSourceWeight_cap w l r x u v leak μ hw hl hr cap)
  rw [leakageSourceWeight_dist_eq w l r x y u v leak E hw hr,
    mergingEnvelope_sum r v μ hr] at average
  rw [twoSidedExtractionWeight_dist_eq w l r x y u v leak E hw hr]
  have comparison := (le_abs_self _).trans (shift.trans seed)
  nlinarith only [comparison, average]

theorem weightedStrongSeededExtractor_two_sided_leakage_dist_le_of_budget
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (μ : Z × U → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ z u₀ x₀,
      w z * mapWeight (fun a => (u z a, x z a)) (l z) (u₀, x₀) ≤ μ (z, u₀))
    (seed : weightDist (observedSeedWeight w r v y)
      (uniformSecondWeight (observedSeedWeight w r v y)) ≤ δ)
    (budget : (K : ℝ) * Fintype.card W * ∑ t, μ t ≤ ρ) :
    weightDist (twoSidedExtractionWeight w l r x y u v leak E)
      (uniformSecondWeight (twoSidedExtractionWeight w l r x y u v leak E)) ≤
        ε + δ + ρ :=
  (weightedStrongSeededExtractor_two_sided_leakage_dist_le extract error
    w l r x y u v leak μ hw hl hr nonnegative cap seed).trans
      (add_le_add le_rfl budget)

end Algebraic.Cutwidth.Extractor.Internal
