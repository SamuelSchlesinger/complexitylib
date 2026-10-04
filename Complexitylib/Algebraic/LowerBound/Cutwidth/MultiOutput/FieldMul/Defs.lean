/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Multiplication in coordinates: definition

Let `K` be an algebra over `F` with a basis `b = (b 0, …, b (n - 1))`. Multiplication in `K`,
written in coordinates, is the map `fieldMul b : F ^ (n + n) → F ^ n` sending the coordinates
`x` and `y` of two elements to the coordinates of their product:
`fieldMul b (x, y) = b.repr ((∑ i, x i • b i) * ∑ j, y j • b j)`. The first `n` inputs
(`Fin.castAdd n i`) are the coordinates of the first factor and the last `n` inputs
(`Fin.natAdd n j`) those of the second; `Fin.append x y` is the input `(x, y)`. For a finite
field `K` of degree `n` over `F` this is multiplication in the extension of degree `n`, for
example in `GF(2 ^ n)` over `GF(2)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

variable {n : Nat}

/-- **Multiplication in coordinates.** For a basis `b` of `K` over `F` indexed by `Fin n`, the
map sending the coordinates of `x` (the first `n` inputs) and of `y` (the last `n` inputs) to
the coordinates of `x * y`. -/
noncomputable def fieldMul {F K : Type*} [CommSemiring F] [Semiring K] [Algebra F K]
    (b : Module.Basis (Fin n) F K) (z : Fin (n + n) → F) : Fin n → F :=
  fun i => b.repr ((∑ j, z (Fin.castAdd n j) • b j) * ∑ j, z (Fin.natAdd n j) • b j) i

end Algebraic.Cutwidth.MultiOutput
