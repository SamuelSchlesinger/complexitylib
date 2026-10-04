/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Entropy
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank

/-!
# Combining output rank, message information, and affine restrictions

Nonaffine independent output components require enough conjunction generators.
Balanced outputs save primary-message bits, and affine pairing gives a second
constraint on the multiple-primary gate count. Eliminating that count improves
the three-halves coefficient.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Cutwidth.Aggregate.Geometry

/-- Output rank and message bias improve the permutation bound beyond three halves. -/
theorem entropy_mul_size_lower_bound {n r : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation))
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    (3 + 2 * Entropy.bitSaving) * n - 2 * r * Entropy.bitSaving ≤
      (2 + Entropy.bitSaving) * c.size := by
  have rank := independent.output_le_conjunctionCount
  have outputs := input_add_conjunctionCount_le_size_add_outputConjunctionCount c bijective
    (by intro i j; simpa using nonliteral i j false)
  have information := input_le_size_sub_outputConjunctionCount_sub_bias c bijective nonliteral
  have pairing := two_mul_input_le_size_add_multi_of_affine_restrictions c small
  have ranks : (n : ℝ) ≤ conjunctionCount c.program := by exact_mod_cast rank
  have counts : (n : ℝ) + conjunctionCount c.program ≤
      c.size + outputConjunctionCount c := by exact_mod_cast outputs
  have pairs : 2 * (n : ℝ) ≤ c.size + multiCount c.program + 2 * r := by
    exact_mod_cast pairing
  have positive := Entropy.bitSaving_pos
  nlinarith [mul_nonneg positive.le (sub_nonneg.mpr pairs)]

end Algebraic.Aggregate.Geometry
