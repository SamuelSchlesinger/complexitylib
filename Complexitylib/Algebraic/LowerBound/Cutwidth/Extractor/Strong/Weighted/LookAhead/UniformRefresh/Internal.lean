/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Internal.Extract
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selected refresh after a correlated uniform-coordinate repair

Repair only the honest state coordinate inside the full right state. The
left source and original right-source envelopes are unchanged. Apply the
common selected-refresh estimate with an exact uniform state envelope,
then transfer to the actual retained transcript at twice the repair cost.
No independence between the repaired coordinate and original right state
is used.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_lookAhead_uniformRefresh_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {R : Y → Mid → Out}
    {K L J : Nat} {ε η θ ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (refresh : WeightedStrongSeededExtractor R J θ) (refresh_error : 0 ≤ θ)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (y : Z → B → Y) (μ ξ : Z → ℝ) (chooseSecond : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    weightDist
        (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R chooseSecond)
        (uniformSecondWeight
          (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R chooseSecond)) ≤
      θ + 2 * ε + η + 2 * ρ +
        (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) / Fintype.card Q +
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z := by
  obtain ⟨r', hr', same, uniform, repair⟩ :=
    exists_factored_uniform_right_repair w l r q hw hl hr
  let ν : Z → ℝ := fun z => w z * (Fintype.card Q : ℝ)⁻¹
  have sumν : ∑ z, ν z = (Fintype.card Q : ℝ)⁻¹ := by
    simp only [ν, ← Finset.sum_mul, hw.2, one_mul]
  have right_cap' : ∀ z u, w z * mapWeight Prod.snd (r' z) u ≤ ν z := by
    intro z u
    exact (uniform z u).le
  have refresh_cap : ∀ z y₀, w z * mapWeight (fun bq => y z bq.1) (r' z) y₀ ≤ ξ z := by
    intro z y₀
    rw [rightCoordinateRepair_source_eq w r r' same y z y₀]
    exact right_cap z y₀
  have seed := retainedSeedWeight_uniform_image_dist w r' (fun _ => Prod.snd)
    initialSeed balanced uniform
  have extracted := weightedStrongSeededExtractor_lookAhead_selectedRefresh_dist_le
    first first_error second second_error refresh refresh_error w l r' x x'
    (fun _ => Prod.snd) (fun z bq => q' z bq.1) initialSeed (fun z bq => y z bq.1)
    μ ν ξ chooseSecond hw hl hr' left_nonnegative
    (fun z => mul_nonneg (hw.1 z) (by positivity)) right_nonnegative
    left_cap right_cap' refresh_cap seed.le
  let evaluate : ((Z × (B × Q)) × A) → (LookAheadBaseTranscript Z Q Mid × A) × Out :=
    fun p =>
      let zq := (p.1.1, (p.1.2.2, q' p.1.1 p.1.2.1))
      let messages := lookAheadBaseMessage x x' initialSeed W QExt zq p.2
      (((zq, messages), p.2), R (y p.1.1 p.1.2.1)
        (if chooseSecond then messages.1.2 else messages.1.1))
  have original : mapWeight evaluate (factoredWeight w l (rightCoordinateLift r q)) =
      lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R chooseSecond := by
    rw [factoredWeight_rightCoordinateLift, mapWeight_comp]
    rfl
  have repaired : mapWeight evaluate (factoredWeight w l r') =
      lookAheadSelectedRefreshWeight w l r' x x' (fun _ => Prod.snd)
        (fun z bq => q' z bq.1) initialSeed W QExt (fun z bq => y z bq.1) R chooseSecond := rfl
  have near := (weightDist_map_le (factoredWeight w l (rightCoordinateLift r q))
    (factoredWeight w l r') evaluate).trans (repair.le.trans state)
  rw [original, repaired] at near
  have bound := weightDist_uniformSecond_le_of_dist near extracted
  rw [sumν] at bound
  calc
    _ ≤ 2 * ρ + (θ + (2 * ε + η + 0 +
        (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) * (Fintype.card Q : ℝ)⁻¹) +
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z) := bound
    _ = _ := by rw [div_eq_mul_inv]; ring

end Algebraic.Cutwidth.Extractor.Internal
