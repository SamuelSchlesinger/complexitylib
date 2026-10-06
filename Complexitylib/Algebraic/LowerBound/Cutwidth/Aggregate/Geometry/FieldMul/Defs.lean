/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.FieldMul.Defs

/-!
# Binary-field multiplication on Boolean inputs

For a binary field `K` with a basis `b` over the two-element field, multiplication in
coordinates is `MultiOutput.fieldMul b`. Reading its `2n` prime-field inputs and `n`
outputs as Boolean bits gives a Boolean map on `2n` inputs: the first `n` bits are the
coordinates of `x`, the last `n` those of `y`, and the outputs are the coordinates of
`x * y`.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.FieldMul

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {n : ℕ}

/-- Multiplication in a binary field with basis `b`, on `2n` Boolean input bits. -/
noncomputable def boolFieldMul (b : Module.Basis (Fin n) (ZMod 2) K)
    (z : Fin (n + n) → Bool) : Fin n → Bool :=
  fun i => decide (Cutwidth.MultiOutput.fieldMul b (bitVector z) i = 1)

end Algebraic.Aggregate.Geometry.FieldMul
