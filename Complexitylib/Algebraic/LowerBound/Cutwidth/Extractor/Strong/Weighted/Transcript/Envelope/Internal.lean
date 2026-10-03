/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic
import Mathlib.Tactic.Ring

/-!
# Source envelopes after finite transcript updates

The exact conditional-row factorization restricts the old source mass to
the observed message. Refinement bounds then charge a left message by its
alphabet size. A right message scales the envelope by its own probability
and preserves the total envelope when the right kernel has total mass one.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem observedTranscriptWeight_nonnegative {Z A U : Type*} [Fintype A]
    (w : Z → ℝ) (p : Z → A → ℝ) (f : Z → A → U)
    (hw : ∀ z, 0 ≤ w z) (hp : ∀ z a, 0 ≤ p z a) (zu : Z × U) :
    0 ≤ observedTranscriptWeight w p f zu := by
  apply mul_nonneg (hw _)
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> first | exact hp _ _ | exact le_rfl

theorem observedTranscript_left_source_eq {Z A X U : Type*} [Fintype A]
    (w : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → X) (f : Z → A → U)
    (hl : ∀ z a, 0 ≤ l z a) (zu : Z × U) (x₀ : X) :
    observedTranscriptWeight w l f zu *
        mapWeight (x zu.1) (observedTranscriptKernel l f zu) x₀ =
      w zu.1 * mapWeight (fun a => (f zu.1 a, x zu.1 a)) (l zu.1) (zu.2, x₀) := by
  simp only [mapWeight, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [observedTranscriptWeight_mul_kernel w l f hl zu a]
  by_cases hf : f zu.1 a = zu.2 <;> by_cases hx : x zu.1 a = x₀ <;>
    simp [hf, hx]

theorem observedTranscript_left_envelope {Z A X U : Type*} [Fintype A]
    (w : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → X) (f : Z → A → U)
    (μ : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (zu : Z × U) (x₀ : X) :
    observedTranscriptWeight w l f zu *
      mapWeight (x zu.1) (observedTranscriptKernel l f zu) x₀ ≤ μ zu.1 := by
  rw [observedTranscript_left_source_eq w l x f hl zu x₀]
  have refinement := merging_map_refinement_le (l zu.1) (hl zu.1)
    (fun _ => ()) (f zu.1) (x zu.1) () zu.2 x₀
  have coarse : mapWeight (fun a => (f zu.1 a, x zu.1 a)) (l zu.1) (zu.2, x₀) ≤
      mapWeight (x zu.1) (l zu.1) x₀ := by
    simpa only [mapWeight, Prod.mk.injEq, true_and] using refinement
  exact (mul_le_mul_of_nonneg_left coarse (hw _)).trans (cap _ _)

theorem observedTranscript_left_envelope_sum {Z U : Type*} [Fintype Z] [Fintype U]
    (μ : Z → ℝ) :
    (∑ zu : Z × U, μ zu.1) = (Fintype.card U : ℝ) * ∑ z, μ z := by
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.mul_sum]

theorem observedTranscript_right_envelope {Z A B X V : Type*} [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (g : Z → B → V) (μ : Z → ℝ)
    (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (zv : Z × V) (x₀ : X) :
    observedTranscriptWeight w r g zv * mapWeight (x zv.1) (l zv.1) x₀ ≤
      observedTranscriptWeight μ r g zv := by
  have nonnegative : 0 ≤ mapWeight (g zv.1) (r zv.1) zv.2 := by
    apply Finset.sum_nonneg
    intro b _
    split_ifs <;> first | exact hr _ _ | exact le_rfl
  have scaled := mul_le_mul_of_nonneg_right (cap zv.1 x₀) nonnegative
  simpa only [observedTranscriptWeight, mul_assoc, mul_comm, mul_left_comm] using scaled

theorem observedTranscript_right_envelope_sum {Z B V : Type*}
    [Fintype Z] [Fintype B] [Fintype V]
    (μ : Z → ℝ) (r : Z → B → ℝ) (g : Z → B → V)
    (mass : ∀ z, ∑ b, r z b = 1) :
    (∑ zv, observedTranscriptWeight μ r g zv) = ∑ z, μ z := by
  have image_mass (z : Z) : ∑ v, mapWeight (g z) (r z) v = 1 := by
    simpa [mapWeight, Finset.sum_comm] using mass z
  simp only [observedTranscriptWeight, Fintype.sum_prod_type, ← Finset.mul_sum,
    image_mass, mul_one]

theorem observedTranscript_left_right_envelope {Z A B X U V : Type*}
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (f : Z → A → U) (g : Z × U → B → V) (μ : Z → ℝ)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (zuv : (Z × U) × V) (x₀ : X) :
    observedTranscriptWeight (observedTranscriptWeight w l f) (fun zu => r zu.1) g zuv *
        mapWeight (x zuv.1.1) (observedTranscriptKernel l f zuv.1) x₀ ≤
      observedTranscriptWeight (fun zu : Z × U => μ zu.1) (fun zu => r zu.1) g zuv :=
  observedTranscript_right_envelope (observedTranscriptWeight w l f)
    (observedTranscriptKernel l f) (fun zu => r zu.1) (fun zu => x zu.1) g
    (fun zu => μ zu.1) (fun zu b => hr zu.1 b)
    (observedTranscript_left_envelope w l x f μ hw hl cap) zuv x₀

theorem observedTranscript_left_right_envelope_sum {Z B U V : Type*}
    [Fintype Z] [Fintype B] [Fintype U] [Fintype V]
    (μ : Z → ℝ) (r : Z → B → ℝ) (g : Z × U → B → V)
    (mass : ∀ z, ∑ b, r z b = 1) :
    (∑ zuv, observedTranscriptWeight (fun zu : Z × U => μ zu.1)
      (fun zu => r zu.1) g zuv) = (Fintype.card U : ℝ) * ∑ z, μ z := by
  rw [observedTranscript_right_envelope_sum _ _ g (fun zu => mass zu.1),
    observedTranscript_left_envelope_sum]

end Algebraic.Cutwidth.Extractor.Internal
