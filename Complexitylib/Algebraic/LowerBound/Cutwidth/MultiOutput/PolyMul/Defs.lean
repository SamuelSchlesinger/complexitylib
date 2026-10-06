/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Polynomial multiplication: definitions

The inputs of polynomial multiplication `polyMul n` are the coefficients of two polynomials of
degree below `n`: the first `n` inputs (`Fin.castAdd n i`) are the coefficients `x₀, …, x_{n-1}`
of `x(t) = ∑ᵢ xᵢ tⁱ` and the last `n` inputs (`Fin.natAdd n j`) the coefficients
`y₀, …, y_{n-1}` of `y(t)`. Output `m`, for `0 ≤ m ≤ 2n - 2`, is the coefficient
`z_m = ∑_{i + j = m} xᵢ yⱼ` of `t ^ m` in the product `x(t) y(t)`.

* `polyMul n`: polynomial multiplication as a function over a commutative semiring.
* `polyMulPolynomial K n m`: the output `z_m` as a polynomial in the `2n` inputs.
* `hankel n μ`: the `n × n` Hankel matrix `(μ (i + j))`.
* `crossMatrix Λ`: the `2n × 2n` symmetric block matrix `[[0, Λ], [Λᵀ, 0]]`, with the first
  `n` rows and columns for the inputs `x` and the last `n` for the inputs `y`. The Hessian of
  `∑ₘ μₘ z_m` is `crossMatrix (hankel n μ)`.
* `firstIn X` and `secondIn X`: the coefficients of `x` and of `y` whose inputs lie in `X`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open Matrix

variable {n : ℕ}

/-- **Polynomial multiplication.** Output `m` is `∑_{i + j = m} xᵢ yⱼ`, the coefficient of
`t ^ m` in `(∑ᵢ xᵢ tⁱ) (∑ⱼ yⱼ tʲ)`, where `xᵢ` is input `Fin.castAdd n i` and `yⱼ` is input
`Fin.natAdd n j`. -/
def polyMul {R : Type*} [CommSemiring R] (n : ℕ) (z : Fin (n + n) → R) (m : Fin (2 * n - 1)) :
    R :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) + j = m then z (Fin.castAdd n i) * z (Fin.natAdd n j) else 0

/-- Output `m` of polynomial multiplication as a polynomial in the inputs. -/
noncomputable def polyMulPolynomial (K : Type*) [CommSemiring K] (n : ℕ) (m : Fin (2 * n - 1)) :
    MvPolynomial (Fin (n + n)) K :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) + j = m then
      MvPolynomial.X (Fin.castAdd n i) * MvPolynomial.X (Fin.natAdd n j)
    else 0

/-- The `n × n` Hankel matrix with entries `μ (i + j)`. -/
def hankel {R : Type*} (n : ℕ) (μ : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => μ (i + j)

/-- The `2n × 2n` block matrix `[[0, Λ], [Λᵀ, 0]]`: the entries in rows `Fin.castAdd n i` and
columns `Fin.natAdd n j`, and in rows `Fin.natAdd n j` and columns `Fin.castAdd n i`, are
`Λ i j`, and the others are zero. -/
def crossMatrix {R : Type*} [Zero R] (Λ : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + n)) (Fin (n + n)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 Λ Λᵀ 0)

/-- The coefficients of the first factor whose inputs lie in `X`. -/
def firstIn (X : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => Fin.castAdd n i ∈ X

/-- The coefficients of the second factor whose inputs lie in `X`. -/
def secondIn (X : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter fun j => Fin.natAdd n j ∈ X

end Algebraic.Cutwidth.MultiOutput
