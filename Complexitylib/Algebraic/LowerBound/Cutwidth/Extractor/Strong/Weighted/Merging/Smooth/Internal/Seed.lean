/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Basic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic

/-!
# Averaging seed error after an independent left observation

If the right seed and its right observation use only the actual prefix,
retaining additional original left observations does not change their
averaged distance from uniform. No individual transcript row is assumed
close to uniform, and null rows contribute zero automatically.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem smooth_observedSeedWeight_dist_eq {Z B V Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype V] [Fintype Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (v : Z → B → V) (y : Z → B → Seed)
    (nonnegative : ∀ z, 0 ≤ w z) :
    weightDist (observedSeedWeight w r v y)
      (uniformSecondWeight (observedSeedWeight w r v y)) =
        ∑ z, w z * weightDist (mapWeight (fun b => (v z b, y z b)) (r z))
          (uniformSecondWeight (mapWeight (fun b => (v z b, y z b)) (r z))) := by
  have actual : observedSeedWeight w r v y = fun t : (Z × V) × Seed =>
      w t.1.1 * mapWeight (fun b => (v t.1.1 b, y t.1.1 b)) (r t.1.1)
        (t.1.2, t.2) := by
    funext ⟨⟨z, v₀⟩, seed⟩
    have mapped := congrFun (mapWeight_tagged (fun z b => (v z b, y z b)) w r)
      (z, (v₀, seed))
    apply Eq.trans ?_ mapped
    simp only [observedSeedWeight, mapWeight, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z' _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    exact propext (by simp only [Prod.mk.injEq, and_assoc])
  rw [actual]
  exact weightDist_uniformSecond_tagged w
    (fun z => mapWeight (fun b => (v z b, y z b)) (r z)) nonnegative

theorem smoothPrefixSeedWeight_dist_eq {Z A B Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype V] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → A → Q)
    (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z, IsProbabilityWeight (l z)) :
    weightDist (smoothPrefixSeedWeight w l r q v y)
      (uniformSecondWeight (smoothPrefixSeedWeight w l r q v y)) =
        ∑ z, w z * ∑ a, l z a *
          weightDist (mapWeight (fun b => (v (z, q z a) b, y (z, q z a) b)) (r z))
            (uniformSecondWeight
              (mapWeight (fun b => (v (z, q z a) b, y (z, q z a) b)) (r z))) := by
  rw [smoothPrefixSeedWeight_eq_observed w l r q v y hl,
    smooth_observedSeedWeight_dist_eq _ _ _ _
      (observedTranscriptWeight_nonnegative w l q hw (fun z => (hl z).1))]
  simp only [Fintype.sum_prod_type, observedTranscriptWeight, mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  exact merging_sum_mapWeight_mul (l z) (q z) _

theorem smooth_observed_average {Z A U : Type*}
    [Fintype Z] [Fintype A] [Fintype U]
    (w : Z → ℝ) (l : Z → A → ℝ) (u : Z → A → U) (g : Z → A → ℝ)
    (hl : ∀ z a, 0 ≤ l z a) :
    ∑ zu, observedTranscriptWeight w l u zu *
        ∑ a, observedTranscriptKernel l u zu a * g zu.1 a =
      ∑ z, w z * ∑ a, l z a * g z a := by
  classical
  simp only [Fintype.sum_prod_type, Finset.mul_sum, ← mul_assoc,
    observedTranscriptWeight_mul_kernel w l u hl]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem smoothMergingSeedWeight_prefix_dist {Z A B U Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (u : Z → A → U) (q : Z → A → Q)
    (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z, IsProbabilityWeight (l z)) :
    weightDist (smoothMergingSeedWeight w l r u q
      (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)))
      (uniformSecondWeight (smoothMergingSeedWeight w l r u q
        (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)))) =
      weightDist (observedSeedWeight (observedTranscriptWeight w l q)
        (fun zq => r zq.1) v y)
        (uniformSecondWeight (observedSeedWeight (observedTranscriptWeight w l q)
          (fun zq => r zq.1) v y)) := by
  rw [← smoothPrefixSeedWeight_eq_observed w l r q v y hl,
    smoothMergingSeedWeight_eq_prefix w l r u q _ _ (fun z => (hl z).1),
    smoothPrefixSeedWeight_dist_eq _ _ _ _ _ _
      (observedTranscriptWeight_nonnegative w l u hw (fun z => (hl z).1))
      (observedTranscriptKernel_probability l u hl),
    smoothPrefixSeedWeight_dist_eq w l r q v y hw hl]
  exact smooth_observed_average w l u (fun z a =>
    weightDist (mapWeight (fun b => (v (z, q z a) b, y (z, q z a) b)) (r z))
      (uniformSecondWeight
        (mapWeight (fun b => (v (z, q z a) b, y (z, q z a) b)) (r z))))
    (fun z => (hl z).1)

end Algebraic.Cutwidth.Extractor.Internal
