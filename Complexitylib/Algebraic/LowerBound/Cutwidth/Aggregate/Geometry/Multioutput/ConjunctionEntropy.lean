/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.RestrictionRank

/-!
# Conjunction counts in the permutation entropy bound

For a permutation with nonliteral outputs and affine-output flats of at most `2^r`
points, distinct outputs give `n + h ≤ g + o`, biased primary messages give
`n ≤ g - o - c h₂`, and affine pairing gives `2n ≤ g + h₂ + 2r`. Here `g` counts gates,
`h` conjunction gates, `o` conjunction outputs, `h₂` multiple-primary conjunctions,
and `c = 1 - H₂(1/4)`. Eliminating `o` and `h₂` leaves
`(2 + c)g ≥ (2 + 2c)n + h - 2rc`. Any lower bound on `h` therefore improves the
total gate bound; the restriction–rank bound supplies `h ≥ 2n - D`.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Cutwidth.Aggregate.Geometry

/-- Output counting, biased messages, and affine pairing leave the conjunction count as
a free summand in the permutation bound. -/
theorem conjunctionCount_entropy_mul_size_lower_bound {n r : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    (2 + 2 * Entropy.bitSaving) * n + conjunctionCount c.program -
        2 * r * Entropy.bitSaving ≤ (2 + Entropy.bitSaving) * c.size := by
  have outputs := input_add_conjunctionCount_le_size_add_outputConjunctionCount c bijective
    (by intro i j; simpa using nonliteral i j false)
  have information := input_le_size_sub_outputConjunctionCount_sub_bias c bijective nonliteral
  have pairing := two_mul_input_le_size_add_multi_of_affine_restrictions c small
  have counts : (n : ℝ) + conjunctionCount c.program ≤
      c.size + outputConjunctionCount c := by exact_mod_cast outputs
  have pairs : 2 * (n : ℝ) ≤ c.size + multiCount c.program + 2 * r := by
    exact_mod_cast pairing
  have weighted := mul_le_mul_of_nonneg_left pairs Entropy.bitSaving_pos.le
  linarith

/-- If no nonzero output component is affine on a flat of `2^D` points, the
restriction–rank bound turns the conjunction summand into `2n - D`. -/
theorem restriction_entropy_mul_size_lower_bound {n r D : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (rigid : NonaffineOnFlats (c.eval interpretation) D) (positive : 0 < n)
    (dimension : D ≤ n)
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    (4 + 2 * Entropy.bitSaving) * n - D - 2 * r * Entropy.bitSaving ≤
      (2 + Entropy.bitSaving) * c.size := by
  have bound := conjunctionCount_entropy_mul_size_lower_bound c bijective nonliteral small
  have rank := rigid.output_add_input_le_conjunctionCount_add positive dimension
  have ranks : (n : ℝ) + n ≤ conjunctionCount c.program + D := by exact_mod_cast rank
  linarith

end Algebraic.Aggregate.Geometry
