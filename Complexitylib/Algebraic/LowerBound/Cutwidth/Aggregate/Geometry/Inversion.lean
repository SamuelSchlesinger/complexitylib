/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Collisions
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Components
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Features
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.LowerBound

/-!
# Gate lower bounds for finite-field inversion

For every binary field and every linear coordinate basis, computing all bits of
inversion requires at least `3n/2 - 2` signed unbounded AND/OR/XOR gates. The only
size restriction is `n ≥ 3`; the permutation, nonprojection, and affine-restriction
properties are proved for inversion itself, not assumed as hardness hypotheses.
The entropy and output-rank refinement has leading coefficient
`(3 + 2c)/(2 + c)`, approximately 1.543112, where `c = 1 - H₂(1/4)`.
The actual nonlinear-feature budget further gives leading coefficient
`(3 + 4c)/(2 + 2c)`, approximately 1.579380, with its explicit additive penalty.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

/-- Computing all coordinates of binary-field inversion costs at least `3n/2 - 2`
gates, at arbitrary depth and with unrestricted fan-in and fanout. -/
theorem three_mul_input_le_two_mul_size {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (c : Circuit signature n n)
    (computes : c.Computes interpretation (inverseFunction e)) :
    3 * n ≤ 2 * c.size + 4 := by
  have out (i : Fin n) : c.outputFunction interpretation i = fun x => inverseFunction e x i := by
    funext x
    exact congrFun (computes x) i
  have bijective : Function.Bijective (c.eval interpretation) := by
    have same : c.eval interpretation = inverseFunction e := funext computes
    rw [same]
    exact inverseFunction_bijective e
  have bound := Geometry.three_mul_input_le_two_mul_size (r := 2) c bijective
    (by intro i j; rw [out]; exact inverseFunction_nonprojection e dimension i j)
    (by
      intro S affine
      exact card_flat_le_four e S (fun i => by simpa only [out i] using affine i))
  exact bound

/-- Output rank and biased messages strengthen the inversion coefficient above three halves. -/
theorem entropy_mul_size_lower_bound {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (c : Circuit signature n n)
    (computes : c.Computes interpretation (inverseFunction e)) :
    (3 + 2 * Cutwidth.Aggregate.Geometry.Entropy.bitSaving) * n -
        4 * Cutwidth.Aggregate.Geometry.Entropy.bitSaving ≤
      (2 + Cutwidth.Aggregate.Geometry.Entropy.bitSaving) * c.size := by
  have out (i : Fin n) : c.outputFunction interpretation i = fun x => inverseFunction e x i := by
    funext x
    exact congrFun (computes x) i
  have same : c.eval interpretation = inverseFunction e := funext computes
  have bijective : Function.Bijective (c.eval interpretation) := by
    rw [same]
    exact inverseFunction_bijective e
  have bound := Geometry.entropy_mul_size_lower_bound (r := 2) c bijective
    (by intro i j b; rw [out]; exact inverseFunction_nonliteral e dimension i j b)
    (by rw [same]; exact inverseFunction_nonaffineComponents e dimension)
    (by
      intro S affine
      exact card_flat_le_four e S (fun i => by simpa only [out i] using affine i))
  norm_num only [Nat.cast_ofNat, mul_one] at bound
  exact bound

/-- Every supplied binary-field coordinate basis has the same improved inversion gate bound. -/
theorem gateCoefficient_mul_sub_constantPenalty_le_size {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (c : Circuit signature n n)
    (computes : c.Computes interpretation (inverseFunction e)) :
    gateCoefficient * n - constantPenalty ≤ c.size := by
  have bound := entropy_mul_size_lower_bound e dimension c computes
  have positive : 0 < 2 + Cutwidth.Aggregate.Geometry.Entropy.bitSaving := by
    linarith [Cutwidth.Aggregate.Geometry.Entropy.bitSaving_pos]
  unfold gateCoefficient constantPenalty
  rw [div_mul_eq_mul_div, ← sub_div]
  exact (div_le_iff₀ positive).mpr (by simpa only [mul_comm] using bound)

end Algebraic.Aggregate.Geometry.Inversion
