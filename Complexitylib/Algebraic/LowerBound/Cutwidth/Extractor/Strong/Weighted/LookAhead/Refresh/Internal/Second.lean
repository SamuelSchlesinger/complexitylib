/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional

/-!
# Refreshing the second output while retaining the tampered first refresh

The right inputs and first left outputs form an exact observed transcript.
The two-round theorem supplies the honest seed error. Revealing the tampered
refresh costs its output alphabet only in the original right-source envelope.
The other left outputs are appended after extraction, using the retained left
state; they are not treated as independent messages or as uniform seeds.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_lookAhead_tampered_refresh_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {R : Y → Mid → Out}
    {K L J : Nat} {ε η θ δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (refresh : WeightedStrongSeededExtractor R J θ) (refresh_error : 0 ≤ θ)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (y y' : Z → B → Y) (μ ν ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (refresh_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (refresh_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R)
      (uniformSecondWeight
        (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R)) ≤
      θ + (2 * ε + η + δ + (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z) +
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z := by
  let g : Z → B → Q × Q := fun z b => (q z b, q' z b)
  let f : Z × (Q × Q) → A → Mid × Mid := fun zq a =>
    (W (x zq.1 a) (initialSeed zq.2.1), W (x' zq.1 a) (initialSeed zq.2.2))
  let w₁ := observedTranscriptWeight w r g
  let l₁ : Z × (Q × Q) → A → ℝ := fun zq => l zq.1
  let r₁ := observedTranscriptKernel r g
  let w₂ := observedTranscriptWeight w₁ l₁ f
  let l₂ := observedTranscriptKernel l₁ f
  let r₂ : (Z × (Q × Q)) × (Mid × Mid) → B → ℝ := fun t => r₁ t.1
  let v : (Z × (Q × Q)) × (Mid × Mid) → B → Out :=
    fun t b => R (y' t.1.1 b) t.2.2
  let s : ((Z × (Q × Q)) × (Mid × Mid)) × Out → A → Mid :=
    fun t a => W (x t.1.1.1 a) (QExt t.1.1.2.1 t.1.2.1)
  have hw₁ : IsProbabilityWeight w₁ := observedTranscriptWeight_probability w r g hw hr
  have hl₁ : ∀ zq, IsProbabilityWeight (l₁ zq) := fun zq => hl zq.1
  have hr₁ : ∀ zq, IsProbabilityWeight (r₁ zq) :=
    observedTranscriptKernel_probability r g hr
  have hw₂ : IsProbabilityWeight w₂ :=
    observedTranscriptWeight_probability w₁ l₁ f hw₁ hl₁
  have hl₂ : ∀ t, IsProbabilityWeight (l₂ t) :=
    observedTranscriptKernel_probability l₁ f hl₁
  have hr₂ : ∀ t, IsProbabilityWeight (r₂ t) := fun t => hr₁ t.1
  have factor := factoredWeight_observe_right_left w l r g f
    (fun z => (hl z).1) (fun z => (hr z).1)
  change mapWeight _ (factoredWeight w l r) = factoredWeight w₂ l₂ r₂ at factor
  let π : (Z × B) × (Mid × Mid) →
      ((Z × (Q × Q)) × (Mid × Mid)) × Out :=
    fun p => (((p.1.1, g p.1.1 p.1.2), p.2), R (y' p.1.1 p.1.2) p.2.2)
  have seed_eq : alternatingSeedWeight w₂ l₂ r₂ v s =
      mapWeight (fun p => (π p.1, p.2))
        (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt) := by
    unfold alternatingSeedWeight lookAheadExtractionWeight
    rw [← factor, mapWeight_comp, mapWeight_comp]
  have seed_bound := first.lookAhead_dist_le first_error second second_error
    w l r x x' q q' initialSeed μ ν hw hl hr left_nonnegative right_nonnegative
    left_cap right_cap seed
  have seed_projected := weightDist_uniformSecond_map_first_le
    (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt) π
  rw [← seed_eq] at seed_projected
  let ξ₁ : Z × (Q × Q) → ℝ := fun zq => ξ zq.1
  let ξ₂ := observedTranscriptWeight ξ₁ l₁ f
  have hξ₂ : ∀ t, 0 ≤ ξ₂ t :=
    observedTranscriptWeight_nonnegative ξ₁ l₁ f (fun zq => refresh_nonnegative zq.1)
      (fun zq => (hl₁ zq).1)
  have cap₁ : ∀ zq y₀, w₁ zq * mapWeight (y zq.1) (r₁ zq) y₀ ≤ ξ₁ zq :=
    observedTranscript_left_envelope w r y g ξ hw.1 (fun z => (hr z).1) refresh_cap
  have cap₂ : ∀ t y₀, w₂ t * mapWeight (y t.1.1) (r₂ t) y₀ ≤ ξ₂ t :=
    observedTranscript_right_envelope w₁ r₁ l₁ (fun zq => y zq.1) f ξ₁
      (fun zq => (hl₁ zq).1) cap₁
  have sum_ξ₂ : (∑ t, ξ₂ t) = (Fintype.card (Q × Q) : ℝ) * ∑ z, ξ z := by
    rw [show (∑ t, ξ₂ t) = ∑ zq, ξ₁ zq from
      observedTranscript_right_envelope_sum ξ₁ l₁ f (fun zq => (hl₁ zq).2)]
    exact observedTranscript_left_envelope_sum ξ
  have bound := refresh.alternating_dist_le refresh_error w₂ l₂ r₂ v s
    (fun t => y t.1.1) ξ₂ hw₂ hl₂ hr₂ hξ₂ cap₂ (seed_projected.trans seed_bound)
  let ψ : (((Z × (Q × Q)) × (Mid × Mid)) × Out) × A →
      (LookAheadBaseTranscript Z Q Mid × Out) × A := fun p =>
    (((p.1.1.1, lookAheadBaseMessage x x' initialSeed W QExt p.1.1.1 p.2), p.1.2), p.2)
  have output_eq : lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R =
      mapWeight (fun p => (ψ p.1, p.2))
        (alternatingExtractionWeight w₂ l₂ r₂ v s (fun t => y t.1.1) R) := by
    unfold lookAheadTamperedRefreshWeight alternatingExtractionWeight
    rw [← factor, mapWeight_comp, mapWeight_comp]
    rfl
  have projected := weightDist_uniformSecond_map_first_le
    (alternatingExtractionWeight w₂ l₂ r₂ v s (fun t => y t.1.1) R) ψ
  rw [← output_eq] at projected
  have result := projected.trans bound
  rw [sum_ξ₂] at result
  convert result using 1
  ring

end Algebraic.Cutwidth.Extractor.Internal
