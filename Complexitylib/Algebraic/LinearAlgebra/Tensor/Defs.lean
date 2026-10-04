/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Three-way tensors, tensor rank, and border rank

A 3-tensor `T ∈ ℂ^α ⊗ ℂ^β ⊗ ℂ^γ` is given by its coordinates `T i j k` in the standard bases
`a_i ⊗ b_j ⊗ c_k` (`Algebraic.Tensor3`). It carries the pointwise vector-space structure and the
product topology on coordinates; for finite index types this is the usual Euclidean topology of
`ℂ^{α × β × γ}`.

* `Tensor3.outer u v w` is the outer product `u ⊗ v ⊗ w`, with coordinates `u i * v j * w k`.
* `Tensor3.RankLE T r`: `T` is a sum of `r` outer products. Zero summands are allowed, so this
  is monotone in `r`; `RankLE T 1` says that `T` is an outer product (rank at most one).
* `Tensor3.tensorRank T` is the least such `r`.
* `Tensor3.BorderRankLE T r`: `T` lies in the closure of the set of tensors of rank at most `r`,
  that is, `T` is a limit of tensors of rank at most `r`.
* `Tensor3.borderRank T` is the least such `r`.
* `Tensor3.map X Y Z T` applies the matrices `X`, `Y`, `Z` to the three factors, the linear map
  `X ⊗ Y ⊗ Z`.
* `Tensor3.subtensor T f g h` reindexes `T` along maps of the index types: deleting, permuting,
  or repeating slices in each factor.

The basic facts about these notions are in
`Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank`.
-/

@[expose] public section

namespace Algebraic

/-- A 3-tensor in `ℂ^α ⊗ ℂ^β ⊗ ℂ^γ`, given by its coordinates: `T i j k` is the coefficient of
`a_i ⊗ b_j ⊗ c_k`. -/
abbrev Tensor3 (α β γ : Type*) : Type _ := α → β → γ → ℂ

namespace Tensor3

variable {α β γ α' β' γ' : Type*}

/-- The outer product `u ⊗ v ⊗ w`, with coordinates `u i * v j * w k`. -/
def outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) : Tensor3 α β γ :=
  fun i j k => u i * v j * w k

/-- `T` has rank at most `r`: it is a sum of `r` outer products. Zero vectors are allowed, so
`T.RankLE 0` means `T = 0` and `T.RankLE 1` means that `T` is an outer product. -/
def RankLE (T : Tensor3 α β γ) (r : ℕ) : Prop :=
  ∃ (u : Fin r → α → ℂ) (v : Fin r → β → ℂ) (w : Fin r → γ → ℂ),
    T = ∑ s, outer (u s) (v s) (w s)

/-- The tensor rank of `T`: the least `r` such that `T` is a sum of `r` outer products. Over
finite index types such an `r` exists (`Tensor3.rankLE_tensorRank`). -/
noncomputable def tensorRank (T : Tensor3 α β γ) : ℕ :=
  sInf {r | T.RankLE r}

/-- `T` has border rank at most `r`: it lies in the closure, for the product topology on
coordinates, of the set of tensors of rank at most `r`. -/
def BorderRankLE (T : Tensor3 α β γ) (r : ℕ) : Prop :=
  T ∈ closure {S : Tensor3 α β γ | S.RankLE r}

/-- The border rank of `T`: the least `r` such that `T` is a limit of tensors of rank at most
`r`. Over finite index types such an `r` exists (`Tensor3.borderRankLE_borderRank`). -/
noncomputable def borderRank (T : Tensor3 α β γ) : ℕ :=
  sInf {r | T.BorderRankLE r}

/-- The image of `T` under the linear map `X ⊗ Y ⊗ Z`, for matrices `X : ℂ^α → ℂ^α'`,
`Y : ℂ^β → ℂ^β'`, and `Z : ℂ^γ → ℂ^γ'`. -/
def map [Fintype α] [Fintype β] [Fintype γ] (X : Matrix α' α ℂ) (Y : Matrix β' β ℂ)
    (Z : Matrix γ' γ ℂ) (T : Tensor3 α β γ) : Tensor3 α' β' γ' :=
  fun i' j' k' => ∑ i, ∑ j, ∑ k, X i' i * Y j' j * Z k' k * T i j k

/-- Reindex `T` along maps of the three index types: the `(i, j, k)` coordinate of the result
is the `(f i, g j, h k)` coordinate of `T`. For injective maps this deletes and permutes
slices. -/
def subtensor (T : Tensor3 α β γ) (f : α' → α) (g : β' → β) (h : γ' → γ) : Tensor3 α' β' γ' :=
  fun i j k => T (f i) (g j) (h k)

end Tensor3

end Algebraic
