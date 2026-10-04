/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Complexitylib.Algebraic.LinearAlgebra.MatrixRank
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul.Internal

/-!
# The Koszul-flattening lower bound for border rank

For a tensor `T ∈ ℂ^α ⊗ ℂ^β ⊗ ℂ^γ` with `α` finite and linearly ordered, `n = card α`, and any
`p`, the Koszul flattening `T_A^{∧p}` (`Tensor3.koszulFlattening`, see
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Koszul.Defs`) satisfies

`rank T_A^{∧p} ≤ borderRank T * (n - 1).choose p`

(`Tensor3.rank_koszulFlattening_le_borderRank_mul`), the bound
`R̲(T) ≥ rank T_A^{∧p} / (n - 1).choose p` of Landsberg and Michałek, *Towards finding hay in a
haystack*, Theory of Computing 2025, (4.1). The proof has three steps.

* **Outer products.** `X ↦ u ∧ X` on `Λ^p ℂ^α` has rank exactly `(n - 1).choose p` for `u ≠ 0`
  (`Tensor3.rank_wedgeMatrix`), and the flattening of `u ⊗ v ⊗ w` factors through it, so its
  rank is at most `(n - 1).choose p` (`Tensor3.rank_koszulFlattening_outer_le`).
* **Rank.** The flattening is linear in `T` and matrix rank is subadditive, so a sum of `r` outer
  products has flattening rank at most `r * (n - 1).choose p`
  (`Tensor3.RankLE.rank_koszulFlattening_le`).
* **Border rank.** The flattening is continuous in `T` and matrices of rank at most `R` form a
  closed set (`Matrix.isClosed_setOf_rank_le`), so the bound passes to limits
  (`Tensor3.BorderRankLE.rank_koszulFlattening_le`).

Applying the bound after a linear map `X : ℂ^α → ℂ^α'` on the first factor
(`Tensor3.BorderRankLE.rank_koszulFlattening_map_le`) replaces `n` by `card α'`; for instance
projecting the first factor onto a `(2p + 1)`-dimensional space gives the denominator
`(2p).choose p`.
-/

@[expose] public section

namespace Algebraic.Tensor3

variable {α β γ α' : Type*}

section Wedge

variable [LinearOrder α] [Fintype α]

/-- `u ∧ u ∧ X = 0`: the composite `Λ^p → Λ^{p+1} → Λ^{p+2}` of wedging with `u` vanishes. -/
theorem wedgeMatrix_mul_wedgeMatrix (p : ℕ) (u : α → ℂ) :
    wedgeMatrix (p + 1) u * wedgeMatrix p u = 0 :=
  Internal.wedgeMatrix_mul_wedgeMatrix p u

/-- `X ↦ u ∧ X` on `Λ^p ℂ^α` has rank at most `(card α - 1).choose p`. -/
theorem rank_wedgeMatrix_le (p : ℕ) (u : α → ℂ) :
    (wedgeMatrix p u).rank ≤ (Fintype.card α - 1).choose p :=
  Internal.rank_wedgeMatrix_le p u

/-- For `u ≠ 0`, `X ↦ u ∧ X` on `Λ^p ℂ^α` has rank exactly `(card α - 1).choose p`. -/
theorem rank_wedgeMatrix (p : ℕ) {u : α → ℂ} (hu : u ≠ 0) :
    (wedgeMatrix p u).rank = (Fintype.card α - 1).choose p := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  exact le_antisymm (rank_wedgeMatrix_le p u) (Internal.le_rank_wedgeMatrix p hi₀)

end Wedge

section Flattening

variable [LinearOrder α] [Fintype α]

/-- The entries of the Koszul flattening: the `((J, k), (I, j))` entry is
`∑ i, wedgeCoeff J I i * T i j k`, the coefficient of `e_J ⊗ c_k` in
`∑_{i,k} T i j k (a_i ∧ e_I) ⊗ c_k`. -/
theorem koszulFlattening_apply (p : ℕ) (T : Tensor3 α β γ)
    (Jk : {J : Finset α // J.card = p + 1} × γ) (Ij : {I : Finset α // I.card = p} × β) :
    koszulFlattening p T Jk Ij = ∑ i, wedgeCoeff Jk.1.1 Ij.1.1 i * T i Ij.2 Jk.2 :=
  rfl

/-- For `p = 0` the Koszul flattening is the ordinary flattening `B^* → A ⊗ C`: its
`(({i}, k), (∅, j))` entry is `T i j k`. -/
theorem koszulFlattening_degree_zero_apply (T : Tensor3 α β γ) (i : α) (j : β) (k : γ) :
    koszulFlattening 0 T (⟨{i}, Finset.card_singleton i⟩, k) (⟨∅, Finset.card_empty⟩, j) =
      T i j k :=
  Internal.koszulFlattening_degree_zero_apply T i j k

theorem koszulFlattening_add (p : ℕ) (S T : Tensor3 α β γ) :
    koszulFlattening p (S + T) = koszulFlattening p S + koszulFlattening p T :=
  Internal.koszulFlattening_add p S T

theorem koszulFlattening_zero (p : ℕ) : koszulFlattening p (0 : Tensor3 α β γ) = 0 :=
  Internal.koszulFlattening_zero p

theorem koszulFlattening_smul (p : ℕ) (c : ℂ) (T : Tensor3 α β γ) :
    koszulFlattening p (c • T) = c • koszulFlattening p T :=
  Internal.koszulFlattening_smul p c T

theorem koszulFlattening_sum (p : ℕ) {ι : Type*} (s : Finset ι) (T : ι → Tensor3 α β γ) :
    koszulFlattening p (∑ x ∈ s, T x) = ∑ x ∈ s, koszulFlattening p (T x) :=
  Internal.koszulFlattening_finset_sum p s T

/-- The Koszul flattening depends continuously on the tensor. -/
theorem continuous_koszulFlattening (p : ℕ) :
    Continuous (koszulFlattening p : Tensor3 α β γ → Matrix _ _ ℂ) :=
  Internal.continuous_koszulFlattening p

/-- The Koszul flattening of an outer product `u ⊗ v ⊗ w` has rank at most
`(card α - 1).choose p`. -/
theorem rank_koszulFlattening_outer_le [Fintype β] (p : ℕ) (u : α → ℂ) (v : β → ℂ)
    (w : γ → ℂ) : (koszulFlattening p (outer u v w)).rank ≤ (Fintype.card α - 1).choose p :=
  Internal.rank_koszulFlattening_outer_le p u v w

/-- A tensor of rank at most `r` has Koszul flattening of rank at most
`r * (card α - 1).choose p`. -/
theorem RankLE.rank_koszulFlattening_le [Fintype β] (p : ℕ) {T : Tensor3 α β γ} {r : ℕ}
    (h : T.RankLE r) : (koszulFlattening p T).rank ≤ r * (Fintype.card α - 1).choose p :=
  Internal.rank_koszulFlattening_le_of_rankLE p h

/-- A tensor of border rank at most `r` has Koszul flattening of rank at most
`r * (card α - 1).choose p`. -/
theorem BorderRankLE.rank_koszulFlattening_le [Fintype β] [Fintype γ] (p : ℕ)
    {T : Tensor3 α β γ} {r : ℕ} (h : T.BorderRankLE r) :
    (koszulFlattening p T).rank ≤ r * (Fintype.card α - 1).choose p :=
  Internal.rank_koszulFlattening_le_of_borderRankLE p h

/-- **The Koszul-flattening bound.** `rank T_A^{∧p} ≤ borderRank T * (card α - 1).choose p`. -/
theorem rank_koszulFlattening_le_borderRank_mul [Fintype β] [Fintype γ] (p : ℕ)
    (T : Tensor3 α β γ) :
    (koszulFlattening p T).rank ≤ T.borderRank * (Fintype.card α - 1).choose p :=
  (borderRankLE_borderRank T).rank_koszulFlattening_le p

/-- **The Koszul-flattening bound, contrapositive form.** If the Koszul flattening has rank
greater than `r * (card α - 1).choose p`, then `T` does not have border rank at most `r`. -/
theorem not_borderRankLE_of_lt_rank_koszulFlattening [Fintype β] [Fintype γ] (p : ℕ)
    {T : Tensor3 α β γ} {r : ℕ}
    (h : r * (Fintype.card α - 1).choose p < (koszulFlattening p T).rank) :
    ¬ T.BorderRankLE r :=
  fun hT => absurd (hT.rank_koszulFlattening_le p) (Nat.not_le.mpr h)

/-- If the Koszul flattening has rank greater than `r * (card α - 1).choose p`, then the border
rank of `T` exceeds `r`. -/
theorem lt_borderRank_of_lt_rank_koszulFlattening [Fintype β] [Fintype γ] (p : ℕ)
    {T : Tensor3 α β γ} {r : ℕ}
    (h : r * (Fintype.card α - 1).choose p < (koszulFlattening p T).rank) :
    r < T.borderRank :=
  Nat.lt_of_not_le fun hle =>
    not_borderRankLE_of_lt_rank_koszulFlattening p h (borderRank_le_iff.mp hle)

end Flattening

/-- **The Koszul-flattening bound after linear maps on the factors.** If `T` has border rank at
most `r`, then for all linear maps `X : ℂ^α → ℂ^α'`, `Y : ℂ^β → ℂ^β'`, `Z : ℂ^γ → ℂ^γ'` (for
instance a projection of the first factor, a restriction to some of its slices, or a change of
basis, with `Y` and `Z` the identity), the Koszul flattening of `(X ⊗ Y ⊗ Z) T` has rank at most
`r * (card α' - 1).choose p`. -/
theorem BorderRankLE.rank_koszulFlattening_map_le {β' γ' : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [LinearOrder α'] [Fintype α'] [Fintype β'] [Fintype γ'] (p : ℕ)
    (X : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ) {T : Tensor3 α β γ} {r : ℕ}
    (h : T.BorderRankLE r) :
    (koszulFlattening p (Tensor3.map X Y Z T)).rank ≤ r * (Fintype.card α' - 1).choose p :=
  (h.map X Y Z).rank_koszulFlattening_le p

end Algebraic.Tensor3
