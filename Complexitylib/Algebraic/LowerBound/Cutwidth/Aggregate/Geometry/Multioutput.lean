/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Counting

/-!
# Multioutput lower bounds for permutations

Balanced distinct outputs occupy gates outside the multiple-primary conjunction
class. Combining this output count with affine pairing gives a coefficient of
three halves whenever the computed permutation has only small affine restrictions.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- Small simultaneous affine restrictions force the paired gate charge. -/
theorem two_mul_input_le_size_add_multi_of_affine_restrictions {n m r : ℕ}
    (c : Circuit signature n m)
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    2 * n ≤ c.size + multiCount c.program + 2 * r := by
  obtain ⟨S, d, affine, cardinal, charge⟩ := exists_affine_restriction c.program
  have upper := small S fun i => affineOn_wire c.program affine (c.outputs i)
  have powers : 2 ^ n ≤ 2 ^ (d + r) := by
    rw [← cardinal, Nat.pow_add]
    exact Nat.mul_le_mul_left _ upper
  have exponent : n ≤ d + r := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp powers
  have count := constantCount_le c.program S
  lia

/-- A permutation with nonprojection coordinates and affine flats of size at most
`2^r` requires at least `(3n-2r)/2` signed unbounded AND/OR/XOR gates. -/
theorem three_mul_input_le_two_mul_size {n r : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j)
    (small : ∀ S : AffineFlat n,
      (∀ i, AffineOn S (c.outputFunction interpretation i)) → S.carrier.card ≤ 2 ^ r) :
    3 * n ≤ 2 * c.size + 2 * r := by
  have outputs := input_add_multiCount_le_size c bijective nonprojection
  have paired := two_mul_input_le_size_add_multi_of_affine_restrictions c small
  lia

end Algebraic.Aggregate.Geometry
