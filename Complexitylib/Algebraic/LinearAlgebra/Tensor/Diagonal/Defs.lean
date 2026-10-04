/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs
public import Mathlib.Data.Fintype.Powerset

/-!
# Weighted shift tensors and the weighted Landsberg–Michałek tensors

* `Tensor3.weightedShifts o g` is the tensor in `ℂ^α ⊗ ℂ^m ⊗ ℂ^m` whose `t`-th slice is the
  weighted shift matrix with offset `o t` and weights `g t`: its `(t, j, ℓ)` coordinate is
  `g t j` if `ℓ = j + o t` (as integers) and `0` otherwise.
* `Tensor3.lmTensor k γ` is the tensor
  `T_k(γ) = ∑_{i, j} γ_{i, j} a_i ⊗ b_j ⊗ c_{i + j}` in `ℂ^{2k+1} ⊗ ℂ^{2k+1} ⊗ ℂ^{2k+1}` of
  Landsberg and Michałek, *Towards finding hay in a haystack*, Theory of Computing 2025, (1.1),
  with the coefficients `γ` (their `p_{ij}`) as a parameter. The slice index `a : Fin (2k+1)`
  stands for the offset `i = a - k ∈ [-k, k]`, so `T_k(γ) = weightedShifts (a ↦ a - k) γ`.
* `Tensor3.lmWeight k a j = 2^{2^{a (2k+1) + j}}` are explicit coefficients: the exponent
  `a (2k+1) + j` is an injective code of the position `(a, j)`.
* `Tensor3.weightedLMTensor k` is the Landsberg–Michałek tensor `T_k(lmWeight k)` with these
  doubly exponential weights.
* `Tensor3.selectSlices c` is the matrix of the linear map `ℂ^α → ℂ^{α'}` keeping the coordinates
  `c t`; applied to the first factor, `map (selectSlices c) 1 1 T` keeps the slices `c t` of `T`.
  For a strictly increasing `c : Fin (2p+1) → Fin (2k+1)` (a *cluster* of slices) it projects
  `T_k(γ)` to the *cluster tensor*, with `2p + 1` slices.
* `Tensor3.clusterOffsets k c t = c t - k` are the offsets of the slices of a cluster.
* `Tensor3.sumSpread p o` is the spread of the sums `∑_{t ∈ K} o t` over the subsets `K` of size
  `p` or `p + 1`: the largest minus the smallest of these sums.

The Koszul-flattening bound for cluster tensors is in
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal`.
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset

variable {α α' : Type*}

/-- The tensor whose `t`-th slice is the weighted shift matrix with offset `o t` and weights
`g t`: its `(t, j, ℓ)` coordinate is `g t j` if `ℓ = j + o t` and `0` otherwise. -/
def weightedShifts {m : ℕ} (o : α → ℤ) (g : α → Fin m → ℂ) : Tensor3 α (Fin m) (Fin m) :=
  fun t j ℓ => if (ℓ : ℤ) = j + o t then g t j else 0

/-- The Landsberg–Michałek tensor `T_k(γ) = ∑_{i, j} γ_{i, j} a_i ⊗ b_j ⊗ c_{i + j}` with
coefficients `γ`. The slice index `a : Fin (2k+1)` stands for the offset `i = a - k`: the
`(a, j, ℓ)` coordinate is `γ a j` if `ℓ = j + (a - k)` and `0` otherwise. -/
def lmTensor (k : ℕ) (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ) :
    Tensor3 (Fin (2 * k + 1)) (Fin (2 * k + 1)) (Fin (2 * k + 1)) :=
  weightedShifts (fun a => (a : ℤ) - k) γ

/-- Doubly exponential coefficients `2^{2^{a (2k+1) + j}}`, indexed by an injective code of the
position `(a, j)`. -/
def lmWeight (k : ℕ) (a j : Fin (2 * k + 1)) : ℂ :=
  ((2 ^ 2 ^ ((a : ℕ) * (2 * k + 1) + j) : ℕ) : ℂ)

/-- The weighted Landsberg–Michałek tensor `T_k(lmWeight k)`: its `(a, j, ℓ)` coordinate is
`2^{2^{a (2k+1) + j}}` if `ℓ = j + (a - k)` and `0` otherwise. -/
def weightedLMTensor (k : ℕ) : Tensor3 (Fin (2 * k + 1)) (Fin (2 * k + 1)) (Fin (2 * k + 1)) :=
  lmTensor k (lmWeight k)

/-- The matrix of the linear map `ℂ^α → ℂ^{α'}` that keeps the coordinates `c t`: its `(t, a)`
entry is `1` if `a = c t` and `0` otherwise. -/
def selectSlices [DecidableEq α] (c : α' → α) : Matrix α' α ℂ :=
  Matrix.of fun t a => if c t = a then 1 else 0

/-- The offsets `c t - k` of the slices `c t` of the Landsberg–Michałek tensor `T_k`. -/
def clusterOffsets (k : ℕ) {n : ℕ} (c : Fin n → Fin (2 * k + 1)) (t : Fin n) : ℤ :=
  (c t : ℤ) - k

/-- The subsets of `α` of size `p` or `p + 1`, which index the bases of `Λ^p ℂ^α` and
`Λ^{p+1} ℂ^α`. -/
def adjacentSubsets [Fintype α] (p : ℕ) : Finset (Finset α) :=
  univ.filter fun K => K.card = p ∨ K.card = p + 1

/-- The spread of the subset sums of `o`: the largest value of `∑_{t ∈ K} o t - ∑_{t ∈ K'} o t`
over subsets `K`, `K'` of size `p` or `p + 1`, that is, the largest minus the smallest of the
sums `∑_{t ∈ K} o t`. -/
def sumSpread [Fintype α] (p : ℕ) (o : α → ℤ) : ℕ :=
  (adjacentSubsets (α := α) p ×ˢ adjacentSubsets p).sup fun KK =>
    (∑ t ∈ KK.1, o t - ∑ t ∈ KK.2, o t).toNat

end Algebraic.Tensor3
