/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-round extraction after repairing a nearly uniform right state

The right coordinate is repaired inside its full correlated state; the left
law and all original right marginals are kept. The generic look-ahead theorem
then has an exact uniform state envelope and an exact uniform initial seed.
Deterministic continuation and comparison with the actual retained marginal
charge twice the original repair distance. The program itself is unchanged.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_lookAhead_uniformState_dist_le
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K J : Nat} {ε η ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt J η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    weightDist (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)) ≤
        2 * ε + η + 2 * ρ + (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
          (J : ℝ) * Fintype.card (Seed × Seed) / Fintype.card Q := by
  obtain ⟨r', hr', _, uniform, repair⟩ :=
    exists_factored_uniform_right_repair w l r q hw hl hr
  let ν : Z → ℝ := fun z => w z * (Fintype.card Q : ℝ)⁻¹
  have sumν : ∑ z, ν z = (Fintype.card Q : ℝ)⁻¹ := by
    simp only [ν, ← Finset.sum_mul, hw.2, one_mul]
  have right_cap : ∀ z u, w z * mapWeight Prod.snd (r' z) u ≤ ν z := by
    intro z u
    exact (uniform z u).le
  have seed := retainedSeedWeight_uniform_image_dist w r' (fun _ => Prod.snd)
    initialSeed balanced uniform
  have extracted := first.lookAhead_dist_le first_error second second_error w l r'
    x x' (fun _ => Prod.snd) (fun z bq => q' z bq.1) initialSeed μ ν hw hl hr'
    nonnegative (fun z => mul_nonneg (hw.1 z) (by positivity)) cap right_cap seed.le
  let project : ((Z × (B × Q)) × (Mid × Mid)) → ((Z × B) × (Mid × Mid)) :=
    fun t => ((t.1.1, t.1.2.1), t.2)
  let evaluate : ((Z × (B × Q)) × A) → (((Z × B) × (Mid × Mid)) × Mid) :=
    fun p =>
      let r₁ := W (x p.1.1 p.2) (initialSeed p.1.2.2)
      let r₁' := W (x' p.1.1 p.2) (initialSeed (q' p.1.1 p.1.2.1))
      (((p.1.1, p.1.2.1), (r₁, r₁')),
        W (x p.1.1 p.2) (QExt p.1.2.2 r₁))
  have original : mapWeight evaluate (factoredWeight w l (rightCoordinateLift r q)) =
      lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt := by
    rw [factoredWeight_rightCoordinateLift, mapWeight_comp]
    rfl
  have repaired : mapWeight evaluate (factoredWeight w l r') =
      mapWeight (fun t => (project t.1, t.2))
        (lookAheadExtractionWeight w l r' x x' (fun _ => Prod.snd)
          (fun z bq => q' z bq.1) initialSeed W QExt) := by
    rw [lookAheadExtractionWeight, mapWeight_comp]
  have near := (weightDist_map_le (factoredWeight w l (rightCoordinateLift r q))
    (factoredWeight w l r') evaluate).trans (repair.le.trans state)
  rw [original, repaired] at near
  have projected := (weightDist_uniformSecond_map_first_le
    (lookAheadExtractionWeight w l r' x x' (fun _ => Prod.snd)
      (fun z bq => q' z bq.1) initialSeed W QExt) project).trans extracted
  have bound := weightDist_uniformSecond_le_of_dist near projected
  rw [sumν] at bound
  calc
    _ ≤ 2 * ρ + (2 * ε + η + 0 +
        (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (J : ℝ) * Fintype.card (Seed × Seed) * (Fintype.card Q : ℝ)⁻¹) := bound
    _ = _ := by rw [div_eq_mul_inv]; ring

end Algebraic.Cutwidth.Extractor.Internal
