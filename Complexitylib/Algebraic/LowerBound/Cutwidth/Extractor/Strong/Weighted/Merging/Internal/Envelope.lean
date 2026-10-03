/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Ring

/-!
# Joint-mass envelopes under finite two-sided observations

Refining a left event cannot increase its joint source mass. Averaging over
the right observation preserves the total envelope, while an additional
finite leak multiplies that total by its alphabet size. No conditional
entropy hypothesis is imposed on an individual transcript fiber.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {Z A B X U V W : Type*}
variable [Fintype Z] [Fintype A] [Fintype B] [Fintype X]
variable [Fintype U] [Fintype V] [Fintype W]

/-- The refined joint envelope weights each old row by its right observation probability. -/
@[expose] noncomputable def mergingEnvelope (r : Z → B → ℝ) (v : Z → B → V)
    (μ : Z × U → ℝ) (t : (Z × V) × (U × W)) : ℝ :=
  mapWeight (v t.1.1) (r t.1.1) t.1.2 * μ (t.1.1, t.2.1)

omit [Fintype Z] [Fintype U] [Fintype W] in
theorem mergingEnvelope_nonnegative (r : Z → B → ℝ) (v : Z → B → V)
    (μ : Z × U → ℝ) (hr : ∀ z, IsProbabilityWeight (r z))
    (hμ : ∀ t, 0 ≤ μ t) (t : (Z × V) × (U × W)) :
    0 ≤ mergingEnvelope r v μ t :=
  mul_nonneg (((hr t.1.1).map (v t.1.1)).1 t.1.2) (hμ _)

omit [Fintype X] [Fintype U] [Fintype W] in
theorem leakageSourceWeight_cap (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (μ : Z × U → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z u₀ x₀,
      w z * mapWeight (fun a => (u z a, x z a)) (l z) (u₀, x₀) ≤ μ (z, u₀))
    (t : (Z × V) × (U × W)) (x₀ : X) :
    leakageSourceWeight w l r x u v leak (t, x₀) ≤ mergingEnvelope r v μ t := by
  rcases t with ⟨⟨z, v₀⟩, u₀, w₀⟩
  have refinement := merging_map_refinement_le (l z) (hl z).1
    (u z) (leak z v₀) (x z) u₀ w₀ x₀
  have upper := (mul_le_mul_of_nonneg_left refinement (hw.1 z)).trans (cap z u₀ x₀)
  have scaled := mul_le_mul_of_nonneg_left upper (((hr z).map (v z)).1 v₀)
  simpa only [leakageSourceWeight, mergingEnvelope, mul_assoc, mul_left_comm]
    using scaled

theorem mergingEnvelope_sum (r : Z → B → ℝ) (v : Z → B → V)
    (μ : Z × U → ℝ) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ t : (Z × V) × (U × W), mergingEnvelope r v μ t) =
      (Fintype.card W : ℝ) * ∑ t : Z × U, μ t := by
  have mass (z : Z) : ∑ v₀, mapWeight (v z) (r z) v₀ = 1 := ((hr z).map (v z)).2
  simp only [mergingEnvelope, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_comm]
  simp_rw [show ∀ v₀ u₀,
    (Fintype.card W : ℝ) * (mapWeight (v z) (r z) v₀ * μ (z, u₀)) =
      ((Fintype.card W : ℝ) * μ (z, u₀)) * mapWeight (v z) (r z) v₀ by
        intros; ring]
  simp only [← Finset.mul_sum, mass, mul_one]

end Algebraic.Cutwidth.Extractor.Internal
