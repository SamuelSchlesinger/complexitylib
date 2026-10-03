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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Mathlib.Tactic.Ring

/-!
# Refreshing after a left-only tampered seed

Two-sided leakage bounds the actual first output while retaining the full
right state and the left leak. The opposite source envelope is preserved
in total by observing this left message. Observing the right input and
its tampered refresh then costs their product alphabet size. Alternating
extraction supplies the final honest output with all messages retained.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem retained_left_leak_dist_le
    {Z A B X Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed] [Fintype Mid]
    [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor W K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (seedMap : Z → B → Seed) (leak : Z → A → Mid) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r seedMap)
      (uniformSecondWeight (retainedSeedWeight w r seedMap)) ≤ δ) :
    weightDist (twoSidedExtractionWeight w l r x seedMap
      (fun _ _ => ()) (fun _ _ => ()) (fun z _ a => leak z a) W)
      (uniformSecondWeight (twoSidedExtractionWeight w l r x seedMap
        (fun _ _ => ()) (fun _ _ => ()) (fun z _ a => leak z a) W)) ≤
          ε + δ + (K : ℝ) * Fintype.card Mid * ∑ z, μ z := by
  have unit_seed : observedSeedWeight w r (fun _ _ => ()) seedMap =
      mapWeight (fun p : Z × Seed => ((p.1, ()), p.2))
        (retainedSeedWeight w r seedMap) := by
    unfold observedSeedWeight retainedSeedWeight
    rw [mapWeight_comp]
  have projected := weightDist_uniformSecond_map_first_le
    (retainedSeedWeight w r seedMap) (fun z => (z, ()))
  rw [← unit_seed] at projected
  have unit_cap (z : Z) (u : Unit) (x₀ : X) :
      w z * mapWeight (fun a => ((), x z a)) (l z) (u, x₀) ≤ μ z := by
    cases u
    simpa only [mapWeight, Prod.mk.injEq, true_and] using cap z x₀
  have bound := extract.two_sided_leakage_dist_le error w l r x seedMap
    (fun _ _ => ()) (fun _ _ => ()) (fun z _ a => leak z a) (fun zu => μ zu.1)
    hw hl hr (fun zu => nonnegative zu.1) unit_cap (projected.trans seed)
  simpa only [Fintype.sum_prod_type, Fintype.sum_unique] using bound

theorem weightedStrongSeededExtractor_fixedTampering_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {R : Y → Mid → Out} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (refresh : WeightedStrongSeededExtractor R L η) (refresh_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)
      (uniformSecondWeight
        (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)) ≤
          η + ε + δ + (K : ℝ) * Fintype.card Mid * (∑ z, μ z) +
            (L : ℝ) * Fintype.card Q * Fintype.card Out * ∑ z, ν z := by
  have first_bound := retained_left_leak_dist_le first first_error w l r x
    (fun z b => initialSeed (q z b)) leak μ hw hl hr left_nonnegative left_cap seed
  have projected := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight w l r x (fun z b => initialSeed (q z b))
      (fun _ _ => ()) (fun _ _ => ()) (fun z _ a => leak z a) W)
    (fun p : (Z × B) × (Unit × Mid) =>
      ((p.1.1, p.2.2), fixedTamperingRightMessage q y' R (p.1.1, p.2.2) p.1.2))
  rw [← fixedTampering_seed_eq_map w l r x q y' leak initialSeed W R hl] at projected
  have cap := observedTranscript_right_envelope w r l y leak ν
    (fun z => (hl z).1) right_cap
  have bound := refresh.alternating_dist_le refresh_error
    (observedTranscriptWeight w l leak) (observedTranscriptKernel l leak) (fun zm => r zm.1)
    (fixedTamperingRightMessage q y' R) (fixedTamperingHonestMessage x initialSeed W)
    (fun zm => y zm.1) (observedTranscriptWeight ν l leak)
    (observedTranscriptWeight_probability w l leak hw hl)
    (observedTranscriptKernel_probability l leak hl) (fun zm => hr zm.1)
    (observedTranscriptWeight_nonnegative ν l leak right_nonnegative (fun z => (hl z).1))
    cap (projected.trans first_bound)
  have final_projected := weightDist_uniformSecond_map_first_le
    (alternatingExtractionWeight (observedTranscriptWeight w l leak)
      (observedTranscriptKernel l leak) (fun zm => r zm.1)
      (fixedTamperingRightMessage q y' R) (fixedTamperingHonestMessage x initialSeed W)
      (fun zm => y zm.1) R)
    (fun p : ((Z × Mid) × (Q × Out)) × A =>
      ((p.1, fixedTamperingHonestMessage x initialSeed W p.1 p.2), p.2))
  rw [← fixedTamperingRefreshWeight_eq_alternating_map w l r x q y y' leak initialSeed W R hl]
    at final_projected
  have result := final_projected.trans bound
  rw [observedTranscript_right_envelope_sum ν l leak (fun z => (hl z).2),
    Fintype.card_prod, Nat.cast_mul] at result
  convert result using 1
  ring

theorem weightedStrongSeededExtractor_fixedTampering_dist_le_of_budget
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {R : Y → Mid → Out} {K L : Nat} {ε η δ ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (refresh : WeightedStrongSeededExtractor R L η) (refresh_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ)
    (budget : (K : ℝ) * Fintype.card Mid * (∑ z, μ z) +
      (L : ℝ) * Fintype.card Q * Fintype.card Out * (∑ z, ν z) ≤ ρ) :
    weightDist (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)
      (uniformSecondWeight
        (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)) ≤
          η + ε + δ + ρ := by
  have bound := weightedStrongSeededExtractor_fixedTampering_dist_le
    first first_error refresh refresh_error w l r x q y y' leak initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed
  have total := add_le_add_left budget (η + ε + δ)
  apply bound.trans
  convert total using 1 <;> ring

end Algebraic.Cutwidth.Extractor.Internal
