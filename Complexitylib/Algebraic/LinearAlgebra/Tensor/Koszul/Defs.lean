/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs
public import Mathlib.Data.Fintype.Powerset

/-!
# Koszul flattenings

Let `A = ℂ^α` with basis `a_i`, where `α` is a finite linearly ordered type. The exterior
power `Λ^p A` has the basis `e_I = a_{i₁} ∧ ⋯ ∧ a_{i_p}` indexed by the `p`-element subsets
`I = {i₁ < ⋯ < i_p}` of `α`. Moving `a_i` past the factors of `e_I` below `i` gives the sign
convention used here:

`a_i ∧ e_I = (-1)^#{x ∈ I | x < i} e_{I ∪ {i}}` if `i ∉ I`, and `a_i ∧ e_I = 0` if `i ∈ I`.

* `Tensor3.wedgeCoeff J I i` is the coefficient of `e_J` in `a_i ∧ e_I`.
* `Tensor3.wedgeMatrix p u` is the matrix of `X ↦ u ∧ X : Λ^p A → Λ^{p+1} A` for `u ∈ A`; its
  rows are indexed by `(p + 1)`-subsets and its columns by `p`-subsets of `α`.
* `Tensor3.koszulFlattening p T` is the Koszul flattening
  `T_A^{∧p} : Λ^p A ⊗ B^* → Λ^{p+1} A ⊗ C` of `T = ∑ T i j k a_i ⊗ b_j ⊗ c_k` (Landsberg and
  Michałek, *Towards finding hay in a haystack*, Theory of Computing 2025, §4.1), which sends
  `e_I ⊗ b_j^*` to `∑_{i,k} T i j k (a_i ∧ e_I) ⊗ c_k`. Its rows are indexed by pairs `(J, k)`
  of a `(p + 1)`-subset `J` of `α` and `k : γ`, its columns by pairs `(I, j)` of a `p`-subset
  `I` of `α` and `j : β`, and its `((J, k), (I, j))` entry is the `(J, I)` entry of
  `wedgeMatrix p (T · j k)`.

The border-rank lower bound `rank T_A^{∧p} ≤ borderRank T * (card α - 1).choose p` is in
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul`.
-/

@[expose] public section

namespace Algebraic.Tensor3

variable {α β γ : Type*} [LinearOrder α]

/-- The coefficient of `e_J` in `a_i ∧ e_I`: `(-1)^#{x ∈ I | x < i}` if `i ∉ I` and
`J = I ∪ {i}`, and `0` otherwise. -/
def wedgeCoeff (J I : Finset α) (i : α) : ℂ :=
  if i ∉ I ∧ insert i I = J then (-1) ^ (I.filter (· < i)).card else 0

variable [Fintype α]

/-- The matrix of `X ↦ u ∧ X : Λ^p ℂ^α → Λ^{p+1} ℂ^α` in the bases `e_I`: its `(J, I)` entry is
`∑ i, wedgeCoeff J I i * u i`. -/
def wedgeMatrix (p : ℕ) (u : α → ℂ) :
    Matrix {J : Finset α // J.card = p + 1} {I : Finset α // I.card = p} ℂ :=
  Matrix.of fun J I => ∑ i, wedgeCoeff J.1 I.1 i * u i

/-- The Koszul flattening `T_A^{∧p} : Λ^p A ⊗ B^* → Λ^{p+1} A ⊗ C`,
`e_I ⊗ b_j^* ↦ ∑_{i,k} T i j k (a_i ∧ e_I) ⊗ c_k`. Its `((J, k), (I, j))` entry is
`∑ i, wedgeCoeff J I i * T i j k`. -/
def koszulFlattening (p : ℕ) (T : Tensor3 α β γ) :
    Matrix ({J : Finset α // J.card = p + 1} × γ) ({I : Finset α // I.card = p} × β) ℂ :=
  Matrix.of fun Jk Ij => wedgeMatrix p (fun i => T i Ij.2 Jk.2) Jk.1 Ij.1

end Algebraic.Tensor3
