/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Internal.BorderRank

/-!
# Basic properties of tensor rank and border rank

For 3-tensors `T : Tensor3 α β γ` (see `Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs`):

* **Rank.** `RankLE` is closed under sums (`RankLE.add`, `RankLE.sum`) and scalar multiples,
  is monotone in the bound (`RankLE.mono`), and every tensor over finite `α`, `β` has rank at most
  `card α * card β` (`rankLE_card_mul_card`), so `tensorRank` is attained
  (`rankLE_tensorRank`, `tensorRank_le_iff`).
* **Border rank.** Rank at most `r` implies border rank at most `r` (`RankLE.borderRankLE`);
  `BorderRankLE` is monotone, closed under sums and scalar multiples, and defines a closed set
  of tensors (`isClosed_setOf_borderRankLE`). `borderRank` is attained, and
  `borderRank T ≤ tensorRank T`.
* **Linear maps on the factors.** `map X Y Z` sends outer products to outer products
  (`map_outer`), is additive and continuous, and composes as matrices multiply (`map_map`), so
  it preserves `RankLE` and `BorderRankLE`: rank and border rank do not increase under
  `X ⊗ Y ⊗ Z` (`tensorRank_map_le`, `borderRank_map_le`). Taking `Y = Z = 1` gives restriction or projection along the first
  factor by any linear map `ℂ^α → ℂ^α'`.
* **Reindexing.** `subtensor` (deleting, permuting, or repeating slices in any factor) also
  preserves `RankLE` and `BorderRankLE`.
-/

@[expose] public section

namespace Algebraic.Tensor3

variable {α β γ α' β' γ' : Type*}

section Rank

/-- A tensor has rank at most `0` exactly when it is zero. -/
theorem rankLE_zero_iff {T : Tensor3 α β γ} : T.RankLE 0 ↔ T = 0 :=
  Internal.rankLE_zero_iff

/-- A tensor has rank at most `1` exactly when it is an outer product `u ⊗ v ⊗ w`. -/
theorem rankLE_one_iff {T : Tensor3 α β γ} :
    T.RankLE 1 ↔ ∃ (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ), T = outer u v w :=
  Internal.rankLE_one_iff

/-- An outer product has rank at most one. -/
theorem rankLE_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) : (outer u v w).RankLE 1 :=
  rankLE_one_iff.mpr ⟨u, v, w, rfl⟩

/-- The zero tensor has rank at most `r` for every `r`. -/
theorem zero_rankLE (r : ℕ) : (0 : Tensor3 α β γ).RankLE r :=
  Internal.zero_rankLE r

/-- Rank is subadditive. -/
theorem RankLE.add {S T : Tensor3 α β γ} {r r' : ℕ} (hS : S.RankLE r) (hT : T.RankLE r') :
    (S + T).RankLE (r + r') :=
  Internal.rankLE_add hS hT

/-- `RankLE` is monotone in the bound. -/
theorem RankLE.mono {T : Tensor3 α β γ} {r r' : ℕ} (h : T.RankLE r) (hr : r ≤ r') :
    T.RankLE r' :=
  Internal.rankLE_mono h hr

/-- Rank is subadditive over finite sums. -/
theorem RankLE.sum {ι : Type*} {s : Finset ι} {T : ι → Tensor3 α β γ} {r : ι → ℕ}
    (h : ∀ x ∈ s, (T x).RankLE (r x)) : (∑ x ∈ s, T x).RankLE (∑ x ∈ s, r x) :=
  Internal.rankLE_sum s T r h

/-- Scalar multiples do not increase rank. -/
theorem RankLE.smul {T : Tensor3 α β γ} {r : ℕ} (c : ℂ) (h : T.RankLE r) : (c • T).RankLE r :=
  Internal.rankLE_smul c h

/-- Every tensor over finite `α` and `β` is a sum of `card α * card β` outer products. -/
theorem rankLE_card_mul_card [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.RankLE (Fintype.card α * Fintype.card β) :=
  Internal.rankLE_card_mul_card T

/-- The tensor rank is attained. -/
theorem rankLE_tensorRank [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.RankLE T.tensorRank :=
  Internal.rankLE_tensorRank T

/-- `tensorRank T ≤ r` exactly when `T` is a sum of `r` outer products. -/
theorem tensorRank_le_iff [Fintype α] [Fintype β] {T : Tensor3 α β γ} {r : ℕ} :
    T.tensorRank ≤ r ↔ T.RankLE r :=
  Internal.tensorRank_le_iff

/-- Tensor rank is subadditive. -/
theorem tensorRank_add_le [Fintype α] [Fintype β] (S T : Tensor3 α β γ) :
    (S + T).tensorRank ≤ S.tensorRank + T.tensorRank :=
  tensorRank_le_iff.mpr ((rankLE_tensorRank S).add (rankLE_tensorRank T))

end Rank

section Border

/-- Rank at most `r` implies border rank at most `r`. -/
theorem RankLE.borderRankLE {T : Tensor3 α β γ} {r : ℕ} (h : T.RankLE r) : T.BorderRankLE r :=
  Internal.borderRankLE_of_rankLE h

/-- `BorderRankLE` is monotone in the bound. -/
theorem BorderRankLE.mono {T : Tensor3 α β γ} {r r' : ℕ} (h : T.BorderRankLE r)
    (hr : r ≤ r') : T.BorderRankLE r' :=
  Internal.borderRankLE_mono h hr

/-- The tensors of border rank at most `r` form a closed set. -/
theorem isClosed_setOf_borderRankLE (r : ℕ) : IsClosed {T : Tensor3 α β γ | T.BorderRankLE r} :=
  Internal.isClosed_setOf_borderRankLE r

/-- Border rank is subadditive. -/
theorem BorderRankLE.add {S T : Tensor3 α β γ} {r r' : ℕ} (hS : S.BorderRankLE r)
    (hT : T.BorderRankLE r') : (S + T).BorderRankLE (r + r') :=
  Internal.borderRankLE_add hS hT

/-- Scalar multiples do not increase border rank. -/
theorem BorderRankLE.smul {T : Tensor3 α β γ} {r : ℕ} (c : ℂ) (h : T.BorderRankLE r) :
    (c • T).BorderRankLE r :=
  Internal.borderRankLE_smul c h

/-- A tensor has border rank at most `0` exactly when it is zero. -/
theorem borderRankLE_zero_iff {T : Tensor3 α β γ} : T.BorderRankLE 0 ↔ T = 0 :=
  Internal.borderRankLE_zero_iff

/-- The border rank is attained. -/
theorem borderRankLE_borderRank [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.BorderRankLE T.borderRank :=
  Internal.borderRankLE_borderRank T

/-- `borderRank T ≤ r` exactly when `T` is a limit of tensors of rank at most `r`. -/
theorem borderRank_le_iff [Fintype α] [Fintype β] {T : Tensor3 α β γ} {r : ℕ} :
    T.borderRank ≤ r ↔ T.BorderRankLE r :=
  Internal.borderRank_le_iff

/-- Border rank is at most rank. -/
theorem borderRank_le_tensorRank [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.borderRank ≤ T.tensorRank :=
  borderRank_le_iff.mpr (rankLE_tensorRank T).borderRankLE

/-- Border rank is subadditive. -/
theorem borderRank_add_le [Fintype α] [Fintype β] (S T : Tensor3 α β γ) :
    (S + T).borderRank ≤ S.borderRank + T.borderRank :=
  borderRank_le_iff.mpr ((borderRankLE_borderRank S).add (borderRankLE_borderRank T))

end Border

section Map

variable [Fintype α] [Fintype β] [Fintype γ]
variable (X : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)

/-- `X ⊗ Y ⊗ Z` sends `u ⊗ v ⊗ w` to `Xu ⊗ Yv ⊗ Zw`. -/
theorem map_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    map X Y Z (outer u v w) = outer (X.mulVec u) (Y.mulVec v) (Z.mulVec w) :=
  Internal.map_outer X Y Z u v w

theorem map_add (S T : Tensor3 α β γ) : map X Y Z (S + T) = map X Y Z S + map X Y Z T :=
  Internal.map_add X Y Z S T

theorem map_zero : map X Y Z (0 : Tensor3 α β γ) = 0 :=
  Internal.map_zero X Y Z

theorem map_smul (c : ℂ) (T : Tensor3 α β γ) : map X Y Z (c • T) = c • map X Y Z T :=
  Internal.map_smul X Y Z c T

theorem map_sum {ι : Type*} (s : Finset ι) (T : ι → Tensor3 α β γ) :
    map X Y Z (∑ x ∈ s, T x) = ∑ x ∈ s, map X Y Z (T x) :=
  Internal.map_finset_sum X Y Z s T

theorem continuous_map : Continuous (map X Y Z : Tensor3 α β γ → Tensor3 α' β' γ') :=
  Internal.continuous_map X Y Z

/-- Diagonal matrices scale the coordinates. -/
theorem map_diagonal [DecidableEq α] [DecidableEq β] [DecidableEq γ] (a : α → ℂ) (b : β → ℂ)
    (c : γ → ℂ) (T : Tensor3 α β γ) :
    map (Matrix.diagonal a) (Matrix.diagonal b) (Matrix.diagonal c) T =
      fun i j k => a i * b j * c k * T i j k :=
  Internal.map_diagonal a b c T

/-- The identity maps fix every tensor. -/
theorem map_one [DecidableEq α] [DecidableEq β] [DecidableEq γ] (T : Tensor3 α β γ) :
    map 1 1 1 T = T :=
  Internal.map_one T

/-- Applying `X ⊗ Y ⊗ Z` and then `X' ⊗ Y' ⊗ Z'` is applying `X'X ⊗ Y'Y ⊗ Z'Z`. -/
theorem map_map [Fintype α'] [Fintype β'] [Fintype γ'] {α'' β'' γ'' : Type*}
    (X' : Matrix α'' α' ℂ) (Y' : Matrix β'' β' ℂ) (Z' : Matrix γ'' γ' ℂ) (T : Tensor3 α β γ) :
    map X' Y' Z' (map X Y Z T) = map (X' * X) (Y' * Y) (Z' * Z) T :=
  Internal.map_map X Y Z X' Y' Z' T

/-- Linear maps on the factors do not increase rank. -/
theorem RankLE.map {T : Tensor3 α β γ} {r : ℕ} (h : T.RankLE r) : (map X Y Z T).RankLE r :=
  Internal.rankLE_map X Y Z h

/-- Linear maps on the factors do not increase border rank. -/
theorem BorderRankLE.map {T : Tensor3 α β γ} {r : ℕ} (h : T.BorderRankLE r) :
    (map X Y Z T).BorderRankLE r :=
  Internal.borderRankLE_map X Y Z h

/-- Linear maps on the factors do not increase tensor rank. -/
theorem tensorRank_map_le [Fintype α'] [Fintype β'] (T : Tensor3 α β γ) :
    (map X Y Z T).tensorRank ≤ T.tensorRank :=
  tensorRank_le_iff.mpr ((rankLE_tensorRank T).map X Y Z)

/-- Linear maps on the factors do not increase border rank. -/
theorem borderRank_map_le [Fintype α'] [Fintype β'] (T : Tensor3 α β γ) :
    (map X Y Z T).borderRank ≤ T.borderRank :=
  borderRank_le_iff.mpr ((borderRankLE_borderRank T).map X Y Z)

end Map

section Subtensor

variable (f : α' → α) (g : β' → β) (h : γ' → γ)

theorem subtensor_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    (outer u v w).subtensor f g h = outer (u ∘ f) (v ∘ g) (w ∘ h) :=
  Internal.subtensor_outer f g h u v w

theorem continuous_subtensor : Continuous fun T : Tensor3 α β γ => T.subtensor f g h :=
  Internal.continuous_subtensor f g h

/-- Reindexing does not increase rank. -/
theorem RankLE.subtensor {T : Tensor3 α β γ} {r : ℕ} (hT : T.RankLE r) :
    (T.subtensor f g h).RankLE r :=
  Internal.rankLE_subtensor f g h hT

/-- Reindexing, in particular deleting or permuting slices, does not increase border rank. -/
theorem BorderRankLE.subtensor {T : Tensor3 α β γ} {r : ℕ} (hT : T.BorderRankLE r) :
    (T.subtensor f g h).BorderRankLE r :=
  Internal.borderRankLE_subtensor f g h hT

/-- Reindexing does not increase tensor rank. -/
theorem tensorRank_subtensor_le [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (T : Tensor3 α β γ) : (T.subtensor f g h).tensorRank ≤ T.tensorRank :=
  tensorRank_le_iff.mpr ((rankLE_tensorRank T).subtensor f g h)

/-- Reindexing, in particular deleting or permuting slices, does not increase border rank. -/
theorem borderRank_subtensor_le [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (T : Tensor3 α β γ) : (T.subtensor f g h).borderRank ≤ T.borderRank :=
  borderRank_le_iff.mpr ((borderRankLE_borderRank T).subtensor f g h)

end Subtensor

end Algebraic.Tensor3
