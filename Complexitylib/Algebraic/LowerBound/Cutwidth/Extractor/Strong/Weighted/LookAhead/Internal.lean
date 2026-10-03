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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Mathlib.Tactic.Ring

/-!
# Two-round extraction with a tampered transcript

The first retained extraction supplies the next honest seed. Revealing the
two initial seeds preserves the left source envelope in total. The second
left extraction reveals both first outputs, paying their alphabet size.
All seed discrepancies follow from the actual preceding calls.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem lookAheadSeedWeight_probability {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadSeedWeight w l r x q q' initialSeed W QExt) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem lookAheadExtractionWeight_probability {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem weightedStrongSeededExtractor_lookAhead_seed_dist_le
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadSeedWeight w l r x q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadSeedWeight w l r x q q' initialSeed W QExt)) ≤
        η + (ε + δ + (K : ℝ) * ∑ z, μ z) +
          (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z := by
  have first_bound := first.retained_dist_le first_error w l r x
    (fun z b => initialSeed (q z b)) μ hw hl hr left_nonnegative left_cap seed
  have projected := weightDist_uniformSecond_map_first_le
    (retainedExtractionWeight w l r x (fun z b => initialSeed (q z b)) W)
    (fun zb => (zb.1, (initialSeed (q zb.1 zb.2), initialSeed (q' zb.1 zb.2))))
  rw [← lookAhead_first_seed_eq_map w l r x q q' initialSeed W] at projected
  rw [lookAheadSeedWeight_eq_alternating]
  exact second.alternating_dist_le second_error w l r
    (fun z b => (initialSeed (q z b), initialSeed (q' z b)))
    (fun zv a => W (x zv.1 a) zv.2.1) q ν hw hl hr
    right_nonnegative right_cap (projected.trans first_bound)

theorem weightedStrongSeededExtractor_lookAhead_dist_le
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)) ≤
        2 * ε + η + δ + (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
          (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z := by
  have seed_bound := weightedStrongSeededExtractor_lookAhead_seed_dist_le
    first first_error second second_error w l r x q q' initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed
  have projected := weightDist_uniformSecond_map_first_le
    (lookAheadSeedWeight w l r x q q' initialSeed W QExt)
    (fun p : (Z × (Seed × Seed)) × A =>
      (p.1, (W (x p.1.1 p.2) p.1.2.1, W (x' p.1.1 p.2) p.1.2.2)))
  rw [← lookAhead_second_seed_eq_map w l r x x' q q' initialSeed W QExt hr] at projected
  have cap := observedTranscript_right_envelope w l r x
    (fun z b => (initialSeed (q z b), initialSeed (q' z b))) μ
    (fun z => (hr z).1) left_cap
  have bound := first.alternating_dist_le first_error
    (observedTranscriptWeight w r
      (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
    (observedTranscriptKernel r
      (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
    (fun zv => l zv.1)
    (fun zv a => (W (x zv.1 a) zv.2.1, W (x' zv.1 a) zv.2.2))
    (fun zvr b => QExt (q zvr.1.1 b) zvr.2.1) (fun zv => x zv.1)
    (observedTranscriptWeight μ r
      (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
    (observedTranscriptWeight_probability w r _ hw hr)
    (observedTranscriptKernel_probability r _ hr) (fun zv => hl zv.1)
    (observedTranscriptWeight_nonnegative μ r _ left_nonnegative (fun z => (hr z).1))
    cap (projected.trans seed_bound)
  have final_projected := weightDist_uniformSecond_map_first_le
    (alternatingExtractionWeight
      (observedTranscriptWeight w r
        (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
      (observedTranscriptKernel r
        (fun z b => (initialSeed (q z b), initialSeed (q' z b))))
      (fun zv => l zv.1)
      (fun zv a => (W (x zv.1 a) zv.2.1, W (x' zv.1 a) zv.2.2))
      (fun zvr b => QExt (q zvr.1.1 b) zvr.2.1) (fun zv => x zv.1) W)
    (fun p : ((Z × (Seed × Seed)) × (Mid × Mid)) × B =>
      ((p.1.1.1, p.2), p.1.2))
  rw [← lookAheadExtractionWeight_eq_map w l r x x' q q' initialSeed W QExt hr]
    at final_projected
  have result := final_projected.trans bound
  rw [observedTranscript_right_envelope_sum μ r _ (fun z => (hr z).2)] at result
  convert result using 1
  ring

theorem weightedStrongSeededExtractor_lookAhead_dist_le_of_budget
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K L : Nat} {ε η δ ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ)
    (budget : (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
      (L : ℝ) * Fintype.card (Seed × Seed) * (∑ z, ν z) ≤ ρ) :
    weightDist (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)) ≤
        2 * ε + η + δ + ρ := by
  have bound := weightedStrongSeededExtractor_lookAhead_dist_le
    first first_error second second_error w l r x x' q q' initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed
  have total := add_le_add_left budget (2 * ε + η + δ)
  apply bound.trans
  convert total using 1 <;> ring

end Algebraic.Cutwidth.Extractor.Internal
