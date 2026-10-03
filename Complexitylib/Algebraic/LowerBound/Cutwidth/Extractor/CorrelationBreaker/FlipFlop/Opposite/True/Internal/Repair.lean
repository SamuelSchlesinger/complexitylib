/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Ring

/-!
# Repair before the terminal fixed-tampering refresh

The repaired coordinate is uniform given the transcript and may remain correlated
with the retained original right state. Both original source envelopes are preserved.
Returning to the actual retained marginal costs twice the repair distance.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem fixedTampering_after_repair
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {R : Y → Mid → Out} {K J : Nat} {ε η ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (refresh : WeightedStrongSeededExtractor R J η) (refresh_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed) (μ ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    weightDist (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)
      (uniformSecondWeight
        (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)) ≤
      2 * ρ + η + ε + (K : ℝ) * Fintype.card Mid * (∑ z, μ z) +
        (J : ℝ) * Fintype.card Q * Fintype.card Out * ∑ z, ξ z := by
  obtain ⟨r', hr', same, uniform, repair⟩ :=
    exists_factored_uniform_right_repair w l r q hw hl hr
  have preserved : ∀ z y₀, w z * mapWeight (fun bq => y z bq.1) (r' z) y₀ ≤ ξ z := by
    intro z y₀
    rw [rightCoordinateRepair_source_eq w r r' same y]
    exact right_cap z y₀
  have seed := retainedSeedWeight_uniform_image_dist w r' (fun _ => Prod.snd)
    initialSeed balanced uniform
  have extracted := first.fixedTampering_dist_le first_error refresh refresh_error
    w l r' x (fun _ => Prod.snd) (fun z bq => y z bq.1) (fun z bq => y' z bq.1)
    leak initialSeed μ ξ hw hl hr' left_nonnegative right_nonnegative
    left_cap preserved seed.le
  let evaluate : ((Z × (B × Q)) × A) →
      (FixedTamperingTranscript Z Q Mid Out × A) × Out := fun p =>
    ((fixedTamperingTranscriptValue x (fun _ => Prod.snd)
        (fun z bq => y' z bq.1) leak initialSeed W R p.1.1 p.2 p.1.2, p.2),
      R (y p.1.1 p.1.2.1) (W (x p.1.1 p.2) (initialSeed p.1.2.2)))
  have original : mapWeight evaluate (factoredWeight w l (rightCoordinateLift r q)) =
      fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R := by
    rw [factoredWeight_rightCoordinateLift, mapWeight_comp]
    rfl
  have near := (weightDist_map_le (factoredWeight w l (rightCoordinateLift r q))
    (factoredWeight w l r') evaluate).trans (repair.le.trans state)
  rw [original] at near
  have result := weightDist_uniformSecond_le_of_dist near extracted
  convert result using 1
  ring

end Algebraic.Cutwidth.Extractor.Internal
