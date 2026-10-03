/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Second.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Internal.Mask
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual second seed supplies pairwise final extraction

Project the preceding second-seed law to all first outputs, then apply the
two-sided leakage theorem to one tampered final output. Reconstruct the
complete transcript from the retained original right state. Finally use
tag-dependent XOR bijections and deterministic tag processing to recover
the actual masked output pair without an additional statistical error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem observedSeedWeight_eq_factored {Z A B V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (y : Z → B → Seed) (hl : ∀ z, IsProbabilityWeight (l z)) :
    observedSeedWeight w r v y =
      mapWeight (fun p : (Z × B) × A =>
        ((p.1.1, v p.1.1 p.1.2), y p.1.1 p.1.2)) (factoredWeight w l r) := by
  have marginal : mapWeight Prod.fst (factoredWeight w l r) =
      fun zb => w zb.1 * r zb.1 zb.2 := by
    rw [mapWeight_fst]
    funext zb
    simp only [firstWeight, factoredWeight, ← Finset.mul_sum, (hl _).2, mul_one]
  unfold observedSeedWeight
  rw [← marginal, mapWeight_comp]

private def secondSeedTag (n t L₀ e₀ L₁ : Nat) {Z A : Type*}
    (x : Z → A → Fin n → Bool)
    (p : (AffinePhaseOneRightTranscript Z t L₀ × A) ×
      (Fin (matchedBlockSeedBits L₁) → Bool)) :
    AffinePhaseOneLeftTranscript Z t L₀ × (Fin (matchedBlockSeedBits L₁) → Bool) :=
  ((p.1.1, affinePhaseOneFirstLeft n t L₀ e₀ x p.1.1 p.1.2), p.2)

private theorem second_seed_project (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z b, 0 ≤ r z b) :
    observedSeedWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
      (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
      (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b (some i))
      (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b none) =
    mapWeight (fun p => (secondSeedTag n t L₀ e₀ L₁ x p.1, p.2))
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i) := by
  have hl₁ : ∀ z, IsProbabilityWeight (affinePhaseOneLeftKernel n t L₀ e₀ l x z) :=
    observedTranscriptKernel_probability _ _ (fun z => hl z.1)
  rw [observedSeedWeight_eq_factored _ (affinePhaseOneLeftKernel n t L₀ e₀ l x)
    _ _ _ hl₁, ← affinePhaseOneLeft_factored n d t L₀ e₀ w l r x mask ys
    (fun z => (hl z).1) hr, mapWeight_comp]
  unfold affinePhaseOneSecondSeedWeight
  rw [mapWeight_comp]
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [secondSeedTag]
  simp only [affinePhaseOneFirstLeft_eq, affinePhaseOneSecondRight_eq]
  dsimp only [affinePhaseOneTranscript, affinePhaseOneLeftTranscript]

private def finalPairTag (d t h L₀ L₁ e₁ : Nat) {Z B : Type*}
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (AffinePhaseOneLeftTranscript Z t L₀ × B) ×
      (Unit × (Fin (matchedBlockOutputBits h L₁) → Bool))) :
    (AffinePhaseOneTranscript Z t L₀ L₁ × B) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool) :=
  (((p.1.1, affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice p.1.1 p.1.2), p.1.2), p.2.2)

private theorem left_pair_project (n d t h L₀ e₀ L₁ e₁ er : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p => (finalPairTag d t h L₀ L₁ e₁ ys advice p.1, p.2))
      (twoSidedExtractionWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
        (affinePhaseOneLeftKernel n t L₀ e₀ l x)
        (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
        (fun z => x z.1.1)
        (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b none)
        (fun _ _ => ())
        (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b (some i))
        (fun z seed a => matchedBlockExtractor n h L₁ er (x z.1.1 a) seed)
        (matchedBlockExtractor n h L₁ er)) =
      affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i := by
  rw [twoSidedExtractionWeight_eq_map,
    ← affinePhaseOneLeft_factored n d t L₀ e₀ w l r x mask ys hl hr,
    mapWeight_comp, mapWeight_comp]
  unfold affinePhaseOneLeftPairWeight
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [finalPairTag]
  rw [affinePhaseOneSecondRight_eq]
  unfold affinePhaseOneOutputLeft
  dsimp only [affinePhaseOneTranscript, affinePhaseOneLeftTranscript,
    affinePhaseOneRightTranscript]

theorem affinePhaseOneLeftPairWeight_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem affinePhaseOnePairWeight_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i) :=
  (factoredWeight_probability w l r hw hl hr).map _

private theorem left_pair_dist_le (n d t h L₀ e₀ L₁ e₁ er K : Nat) {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor (matchedBlockExtractor n h L₁ er) K ε)
    (error : 0 ≤ ε) {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)) ≤ δ) :
    weightDist
      (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) ≤
      ε + δ + (K : ℝ) * Fintype.card (Fin (matchedBlockOutputBits h L₁) → Bool) *
        Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) * ∑ z, μ z := by
  classical
  obtain ⟨hw₁, hl₁, hr₁⟩ := affinePhaseOneLeft_probability n d t L₀ e₀
    w l r x mask ys hw hl hr
  have observed : weightDist
      (observedSeedWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
        (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
        (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b (some i))
        (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b none))
      (uniformSecondWeight
        (observedSeedWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
          (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
          (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b (some i))
          (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b none))) ≤ δ := by
    rw [second_seed_project n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i hl
      (fun z => (hr z).1)]
    exact (weightDist_uniformSecond_map_first_le _
      (secondSeedTag n t L₀ e₀ L₁ x)).trans seed
  have jointCap (z : AffinePhaseOneLeftTranscript Z t L₀) (u : Unit) (x₀ : Fin n → Bool) :
      affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys z *
        mapWeight (fun a => (((), x z.1.1 a) : Unit × (Fin n → Bool)))
          (affinePhaseOneLeftKernel n t L₀ e₀ l x z) (u, x₀) ≤
        affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys z := by
    cases u
    have joint : mapWeight (fun a => (((), x z.1.1 a) : Unit × (Fin n → Bool)))
        (affinePhaseOneLeftKernel n t L₀ e₀ l x z) ((), x₀) =
        mapWeight (x z.1.1) (affinePhaseOneLeftKernel n t L₀ e₀ l x z) x₀ := by
      unfold mapWeight
      apply Finset.sum_congr rfl
      intro a _
      by_cases same : x z.1.1 a = x₀ <;> simp [same]
    rw [joint]
    exact affinePhaseOneLeft_left_envelope n d t L₀ e₀ w l r x mask ys μ hw hl hr cap z x₀
  have bound := extract.two_sided_leakage_dist_le error
    (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
    (affinePhaseOneLeftKernel n t L₀ e₀ l x)
    (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) (fun z => x z.1.1)
    (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b none)
    (fun _ _ => ())
    (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b (some i))
    (fun z seed a => matchedBlockExtractor n h L₁ er (x z.1.1 a) seed)
    (fun zu : AffinePhaseOneLeftTranscript Z t L₀ × Unit =>
      affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys zu.1) hw₁ hl₁ hr₁
    (fun zu => affinePhaseOneLeftEnvelope_nonnegative n d t L₀ e₀ μ r mask ys
      nonnegative (fun z => (hr z).1) zu.1) jointCap observed
  have projected := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
      (affinePhaseOneLeftKernel n t L₀ e₀ l x)
      (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) (fun z => x z.1.1)
      (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b none)
      (fun _ _ => ())
      (fun z b => affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice z b (some i))
      (fun z seed a => matchedBlockExtractor n h L₁ er (x z.1.1 a) seed)
      (matchedBlockExtractor n h L₁ er)) (finalPairTag d t h L₀ L₁ e₁ ys advice)
  rw [left_pair_project n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i
    (fun z => (hl z).1) (fun z => (hr z).1)] at projected
  apply projected.trans
  simpa only [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
    affinePhaseOneLeftEnvelope_sum n d t L₀ e₀ μ r mask ys (fun z => (hr z).2),
    mul_assoc] using bound

theorem affinePhaseOneLeftPair_dist_le (n d t h L₀ e₀ L₁ e₁ er : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L₁) (error : er + h + 2 ≤ L₁)
    (budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)) ≤ δ) :
    weightDist
      (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) ≤
      ((2 : ℝ) ^ er)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L₁) *
        Fintype.card (Fin (matchedBlockOutputBits h L₁) → Bool) *
        Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) * ∑ z, μ z := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    left_pair_dist_le n d t h L₀ e₀ L₁ e₁ er _
      (matchedBlockExtractor_growing n h L₁ er length error budget) (by positivity)
      w l r x mask ys advice i μ hw hl hr nonnegative cap seed

theorem affinePhaseOnePair_dist_le (n d t h L₀ e₀ L₁ e₁ er : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L₁) (error : er + h + 2 ≤ L₁)
    (budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)) ≤ δ) :
    weightDist
      (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) ≤
      ((2 : ℝ) ^ er)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L₁) *
        Fintype.card (Fin (matchedBlockOutputBits h L₁) → Bool) *
        Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) * ∑ z, μ z :=
  (affinePhaseOnePair_dist_le_left n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i).trans
    (affinePhaseOneLeftPair_dist_le n d t h L₀ e₀ L₁ e₁ er length error budget
      w l r x mask ys advice i μ hw hl hr nonnegative cap seed)

end Algebraic.Cutwidth.Extractor.Internal
