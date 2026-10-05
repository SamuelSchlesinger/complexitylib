/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Collisions
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Field

/-!
# Differential and affine-residual collision bounds for inversion

In characteristic two, every nonzero derivative of inversion has fibres of size
at most four. The existing reciprocal ternary identity proves this directly.
Adding an arbitrary additive map and a constant therefore leaves at most
`q + 4 * (q - 1)` ordered collisions on a field of size `q`.

The differential uniformity of inversion is classical; see Claude Carlet,
"Vectorial Boolean Functions for Cryptography", Section 3.1.7.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

open scoped Classical
open Cutwidth.Aggregate.Geometry.Entropy

variable {K : Type*} [Field K] [CharP K 2]

/-- Every nonzero derivative of binary-field inversion has fibres of size at most four. -/
theorem card_le_four_of_inverse_derivative (S : Finset K) {d b : K} (hd : d ≠ 0)
    (derivative : ∀ x ∈ S, (x + d)⁻¹ + x⁻¹ = b) : S.card ≤ 4 := by
  by_cases exceptional : ∀ x ∈ S, x = 0 ∨ x = d
  · have sub : S ⊆ {0, d} := by
      intro x hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using exceptional x hx
    exact (Finset.card_le_card sub).trans (Finset.card_le_two.trans (by decide))
  push Not at exceptional
  obtain ⟨a, ha, azero, ad⟩ := exceptional
  have adzero : a + d ≠ 0 := fun h => ad (CharTwo.add_eq_zero.mp h)
  have aad : a ≠ a + d := by
    intro h
    exact hd (add_left_cancel (show a + d = a + 0 by simpa using h.symm))
  have sub : S ⊆ {0, d, a, a + d} := by
    intro x hx
    by_cases xzero : x = 0
    · simp [xzero]
    by_cases xd : x = d
    · simp [xd]
    have sum : a + (a + d) + x = x + d := by
      calc
        a + (a + d) + x = (a + a) + (x + d) := by ac_rfl
        _ = x + d := by rw [CharTwo.add_self_eq_zero, zero_add]
    have nonzero : a + (a + d) + x ≠ 0 := by
      rw [sum]
      exact fun h => xd (CharTwo.add_eq_zero.mp h)
    have identity : (a + (a + d) + x)⁻¹ = a⁻¹ + (a + d)⁻¹ + x⁻¹ := by
      rw [sum]
      have same := (derivative x hx).trans (derivative a ha).symm
      exact (CharTwo.add_eq_iff_eq_add.mp same).trans (by ac_rfl)
    rcases eq_of_inverse_three azero adzero xzero nonzero identity with h | h | h
    · exact (aad h).elim
    · simp [h.symm]
    · simp [h.symm]
  exact (Finset.card_le_card sub).trans Finset.card_le_four

/-- Affine input terms do not evade inversion's ordered-collision bound. -/
theorem collisionCount_inverse_add_affine_le [Fintype K] (A : K →+ K) (a : K) :
    collisionCount (fun x => x⁻¹ + A x + a) ≤
      Fintype.card K + 4 * (Fintype.card K - 1) := by
  apply collisionCount_le_of_differences
  intro d hd
  apply card_le_four_of_inverse_derivative (d := d) (b := A d) _ hd
  intro x hx
  have same := (Finset.mem_filter.mp hx).2
  have cancel : (x + d)⁻¹ + A d = x⁻¹ := by
    apply add_right_cancel (b := A x)
    calc
      (x + d)⁻¹ + A d + A x = (x + d)⁻¹ + A (x + d) := by
        rw [map_add]
        ac_rfl
      _ = x⁻¹ + A x := add_right_cancel same
  apply CharTwo.add_eq_iff_eq_add.mpr
  exact (CharTwo.add_eq_iff_eq_add.mp cancel).trans (add_comm _ _)

/-- The coarser average collision budget of five is independent of the field size. -/
theorem collisionCount_inverse_add_affine_le_five_mul [Fintype K] (A : K →+ K) (a : K) :
    collisionCount (fun x => x⁻¹ + A x + a) ≤ 5 * Fintype.card K := by
  have bound := collisionCount_inverse_add_affine_le A a
  omega

/-- Any Boolean feature representation of an affine residual of inversion pays for biased bits. -/
theorem log_card_le_of_inverse_features_and_bias [Fintype K]
    {ι : Type*} [Fintype ι] (key : K → (ι → Bool)) (decode : (ι → Bool) → K)
    (A : K →+ K) (a : K)
    (represents : ∀ x, x⁻¹ + A x + a = decode (key x))
    (biased : Finset ι) (rare : ι → Bool)
    (bias : ∀ i ∈ biased,
      4 * (Finset.univ.filter fun x => key x i = rare i).card ≤ Fintype.card K) :
    Real.log (Fintype.card K) ≤ Real.log 5 + Fintype.card ι * Real.log 2 -
      biased.card * biasSaving := by
  have refines := collisionCount_le_of_refines key (fun x => x⁻¹ + A x + a)
    (fun x y h => by rw [represents x, represents y, h])
  have bound := refines.trans (collisionCount_inverse_add_affine_le_five_mul A a)
  apply log_card_le_of_collisions_and_bias key biased rare (by norm_num) _ bias
  have realBound : (collisionCount key : ℝ) ≤ 5 * Fintype.card K := by
    exact_mod_cast bound
  simpa only [mul_comm] using realBound

end Algebraic.Aggregate.Geometry.Inversion
