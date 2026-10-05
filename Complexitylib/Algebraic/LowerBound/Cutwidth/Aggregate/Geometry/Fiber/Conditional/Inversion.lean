/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion

/-!
# Conditional-majority lower bound for binary-field inversion

For every supplied binary field and linear coordinate basis, all coordinates of
inversion require at least `C * n - P` gates for `n ≥ 3`, where
`C ≈ 1.5659486596` and `P ≈ 0.6016050397`. The exact constants combine majority
fibers with residual entropy, both original entropy bounds, and affine geometry.
Fan-in, fanout, depth, and literal repetitions remain unrestricted.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

open Cutwidth.Aggregate.Geometry

/-- Large majority fibers improve the gate bound for every binary-field coordinate basis. -/
theorem conditionalFiberCoefficient_mul_sub_penalty_le_size {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (c : Circuit signature n n)
    (computes : c.Computes interpretation (inverseFunction e)) :
    Fiber.Conditional.inversionCoefficient * n - Fiber.Conditional.inversionPenalty ≤ c.size := by
  have out (i : Fin n) : c.outputFunction interpretation i = fun x => inverseFunction e x i := by
    funext x
    exact congrFun (computes x) i
  have same : c.eval interpretation = inverseFunction e := funext computes
  have bijective : Function.Bijective (c.eval interpretation) := by
    rw [same]
    exact inverseFunction_bijective e
  have bound := Fiber.Conditional.inversionCoefficient_mul_sub_le_size (r := 2) c bijective
    (by intro i j b; rw [out]; exact inverseFunction_nonliteral e dimension i j b)
    (by rw [same]; exact inverseFunction_nonaffineComponents e dimension)
    (by
      intro S affine
      exact card_flat_le_four e S (fun i => by simpa only [out i] using affine i))
  norm_num only [Nat.cast_ofNat] at bound
  convert bound using 1
  unfold Fiber.Conditional.inversionPenalty
  ring

end Algebraic.Aggregate.Geometry.Inversion
