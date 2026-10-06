/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.FieldMul.Internal

/-!
# Conjunction gates for binary-field multiplication

Let `K` be a binary field of degree `n ≥ 1` with any basis `b`. Every signed unbounded
AND/OR/XOR circuit computing all `n` coordinates of `x * y` from the `2n` coordinates of
`x` and `y` has at least `2n - 1` conjunction gates. XOR gates of every fan-in are free in
this count, so it also bounds the number of unbounded-fan-in AND/OR gates in circuits with
free XOR; fan-in, fanout, depth, and nonlinear reuse are unrestricted.

The proof applies the restriction–rank bound: every nonzero component `ℓ(xy)` is a
quadratic form whose polar form `ℓ(xy' + x'y)` is nondegenerate on the `2n`-dimensional
input space, so the component is affine only on flats of dimension at most `n`.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.FieldMul

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {n : ℕ}

/-- No nonzero linear component of binary-field multiplication is affine on a flat with
`2^(n+1)` points. -/
theorem boolFieldMul_nonaffineOnFlats (b : Module.Basis (Fin n) (ZMod 2) K) :
    NonaffineOnFlats (boolFieldMul b) (n + 1) :=
  nonaffineOnFlats_boolFieldMul b

/-- Computing multiplication in a binary field of degree `n ≥ 1`, in any basis, requires
at least `2n - 1` conjunction gates. -/
theorem two_mul_input_le_conjunctionCount_add_one (b : Module.Basis (Fin n) (ZMod 2) K)
    (positive : 0 < n) (c : Circuit signature (n + n) n)
    (computes : c.Computes interpretation (boolFieldMul b)) :
    2 * n ≤ conjunctionCount c.program + 1 := by
  have same : c.eval interpretation = boolFieldMul b := funext computes
  have rigid : NonaffineOnFlats (c.eval interpretation) (n + 1) := by
    rw [same]
    exact boolFieldMul_nonaffineOnFlats b
  have bound := rigid.output_add_input_le_conjunctionCount_add positive (by omega)
  omega

end Algebraic.Aggregate.Geometry.FieldMul
