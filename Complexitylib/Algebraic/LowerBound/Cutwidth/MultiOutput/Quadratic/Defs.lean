/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Quadratic forms: definitions

* `quadForm M x`: the quadratic form `x ↦ xᵀ M x` of a square matrix `M`, and
  `quadFormPolynomial M`, the same form as a polynomial `∑ᵢ ∑ⱼ M i j Xᵢ Xⱼ`.
* `hankelCauchyZMod q N`: the `N × N` matrix over `ZMod q` with entries `1 / (i + j + 2)`. It is
  the Cauchy matrix `cauchy x y` with nodes `x i = i + 1` and `y j = -(j + 1)`, and it is
  symmetric.
* `hankelCauchyCharZero F N`: the matrix with the same entries `1 / (i + j + 2)` over a field
  `F`, totally regular when `F` has characteristic zero.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open Matrix

/-- The quadratic form `x ↦ xᵀ M x` of a square matrix `M`. -/
def quadForm {F : Type*} [CommRing F] {N : Nat} (M : Matrix (Fin N) (Fin N) F) (x : Fin N → F) :
    F :=
  x ⬝ᵥ (M *ᵥ x)

/-- The quadratic form of `M` as a polynomial, `∑ᵢ ∑ⱼ M i j Xᵢ Xⱼ`. -/
noncomputable def quadFormPolynomial {K : Type*} [CommSemiring K] {N : Nat}
    (M : Matrix (Fin N) (Fin N) K) : MvPolynomial (Fin N) K :=
  ∑ i, ∑ j, MvPolynomial.C (M i j) * (MvPolynomial.X i * MvPolynomial.X j)

/-- The `N × N` Hankel Cauchy matrix over `ZMod q` with entries `1 / (i + j + 2)` for
`0 ≤ i, j < N`. For a prime `q > 2 N` it is the Cauchy matrix with nodes `x i = i + 1` and
`y j = -(j + 1)`. -/
def hankelCauchyZMod (q N : Nat) : Matrix (Fin N) (Fin N) (ZMod q) :=
  Matrix.of fun i j => (((i : Nat) + j + 2 : Nat) : ZMod q)⁻¹

/-- The `N × N` Hankel Cauchy matrix over a field `F`, with entries `1 / (i + j + 2)` for
`0 ≤ i, j < N`. In characteristic zero it is the Cauchy matrix with nodes `x i = i + 1` and
`y j = -(j + 1)`. -/
def hankelCauchyCharZero (F : Type*) [Field F] (N : Nat) : Matrix (Fin N) (Fin N) F :=
  Matrix.of fun i j => (((i : Nat) + j + 2 : Nat) : F)⁻¹

end Algebraic.Cutwidth.MultiOutput
