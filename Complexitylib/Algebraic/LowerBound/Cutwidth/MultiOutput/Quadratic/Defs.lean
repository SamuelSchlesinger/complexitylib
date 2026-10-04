/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs

/-!
# Quadratic forms: definitions

* `quadForm M x`: the quadratic form `x ↦ xᵀ M x` of a square matrix `M`.
* `hankelCauchyZMod q N`: the `N × N` matrix over `ZMod q` with entries `1 / (i + j + 2)`. It is
  the Cauchy matrix `cauchy x y` with nodes `x i = i + 1` and `y j = -(j + 1)`, and it is
  symmetric.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open Matrix

/-- The quadratic form `x ↦ xᵀ M x` of a square matrix `M`. -/
def quadForm {F : Type*} [CommRing F] {N : Nat} (M : Matrix (Fin N) (Fin N) F) (x : Fin N → F) :
    F :=
  x ⬝ᵥ (M *ᵥ x)

/-- The `N × N` Hankel Cauchy matrix over `ZMod q` with entries `1 / (i + j + 2)` for
`0 ≤ i, j < N`. For a prime `q > 2 N` it is the Cauchy matrix with nodes `x i = i + 1` and
`y j = -(j + 1)`. -/
def hankelCauchyZMod (q N : Nat) : Matrix (Fin N) (Fin N) (ZMod q) :=
  Matrix.of fun i j => (((i : Nat) + j + 2 : Nat) : ZMod q)⁻¹

end Algebraic.Cutwidth.MultiOutput
