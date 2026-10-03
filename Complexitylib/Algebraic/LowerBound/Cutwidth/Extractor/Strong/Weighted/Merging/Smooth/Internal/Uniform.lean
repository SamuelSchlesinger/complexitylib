/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Basic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Mathlib.Tactic.Positivity

/-!
# Extracting from a uniform coordinate after an actual finite prefix

Uniformity is only required before observing the prefix. Each observed
joint source mass is bounded by the old transcript weight divided by the
source alphabet size. Summing over prefix values pays exactly that
alphabet's cardinality. This lemma will consume a constructed coordinate
repair, rather than assume the original smooth source has a pointwise cap.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem smoothPrefixExtractionWeight_uniform_dist_le
    {Z A B X Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype V] [Fintype W] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → A → Q) (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (leak : Z × Q → V → A → W)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (uniform : ∀ z, mapWeight (x z) (l z) = uniformWeight X)
    (seed : weightDist (smoothPrefixSeedWeight w l r q v y)
      (uniformSecondWeight (smoothPrefixSeedWeight w l r q v y)) ≤ δ) :
    weightDist (smoothPrefixExtractionWeight w l r x q v y leak E)
      (uniformSecondWeight (smoothPrefixExtractionWeight w l r x q v y leak E)) ≤
        ε + δ + (K : ℝ) * Fintype.card W * Fintype.card Q / Fintype.card X := by
  let wq := observedTranscriptWeight w l q
  let lq := observedTranscriptKernel l q
  let rq : Z × Q → B → ℝ := fun zq => r zq.1
  let μ : (Z × Q) × Unit → ℝ := fun t => w t.1.1 / Fintype.card X
  have hq := observedTranscriptWeight_probability w l q hw hl
  have hlq := observedTranscriptKernel_probability l q hl
  have cap (zq : Z × Q) (u₀ : Unit) (x₀ : X) :
      wq zq * mapWeight (fun a => (u₀, x zq.1 a)) (lq zq) (u₀, x₀) ≤ μ (zq, u₀) := by
    have bound := observedTranscript_left_envelope w l x q
      (fun z => w z / Fintype.card X) hw.1 (fun z => (hl z).1)
      (fun z x₀ => by rw [uniform]; exact le_of_eq (by rfl)) zq x₀
    have same : mapWeight (fun a => (u₀, x zq.1 a)) (lq zq) (u₀, x₀) =
        mapWeight (x zq.1) (lq zq) x₀ := by
      unfold mapWeight
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact propext (by simp only [Prod.mk.injEq, true_and])
    rw [same]
    exact bound
  have seed' : weightDist (observedSeedWeight wq rq v y)
      (uniformSecondWeight (observedSeedWeight wq rq v y)) ≤ δ := by
    rw [← smoothPrefixSeedWeight_eq_observed w l r q v y hl]
    exact seed
  have bound := extract.two_sided_leakage_dist_le error wq lq rq
    (fun zq => x zq.1) y (fun _ _ => ()) v leak μ hq hlq (fun zq => hr zq.1)
    (fun t => div_nonneg (hw.1 _) (Nat.cast_nonneg _)) (fun zq _ x₀ => cap zq () x₀) seed'
  let project : ((Z × Q) × B) × (Unit × W) → ((Z × Q) × B) × W :=
    fun t => (t.1, t.2.2)
  have projected := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight wq lq rq (fun zq => x zq.1) y
      (fun _ _ => ()) v leak E) project
  have actual : mapWeight (fun p => (project p.1, p.2))
      (twoSidedExtractionWeight wq lq rq (fun zq => x zq.1) y
        (fun _ _ => ()) v leak E) = smoothPrefixExtractionWeight w l r x q v y leak E := by
    rw [twoSidedExtractionWeight_eq_map]
    change mapWeight _ (mapWeight _
      (factoredWeight (observedTranscriptWeight w l q) (observedTranscriptKernel l q)
        (fun zq => r zq.1))) = _
    rw [← factoredWeight_observe_left w l r q (fun z => (hl z).1),
      mapWeight_comp, mapWeight_comp]
    rfl
  rw [actual] at projected
  have total : (∑ t, μ t) = (Fintype.card Q : ℝ) / Fintype.card X := by
    simp only [μ, Fintype.sum_prod_type, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv, Fintype.card_unit, Nat.cast_one, one_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hw.2, one_mul]
  simpa only [total, div_eq_mul_inv, mul_assoc] using projected.trans bound

end Algebraic.Cutwidth.Extractor.Internal
