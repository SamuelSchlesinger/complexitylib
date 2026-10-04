/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Semicontinuity.Basic
import Complexitylib.Algebraic.LinearAlgebra.MatrixRank.Internal

/-!
# Matrix rank: subadditivity, minors, semicontinuity, blocks, and deletions

Facts about `Matrix.rank` over a field `K` that Mathlib does not state directly. Ranks are
natural numbers and all index types are finite.

* **Subadditivity**: `Matrix.rank_add_le` and `Matrix.rank_sum_le`.
* **Minors**: `rank A ≥ k` if and only if some `k × k` submatrix of `A` has nonzero
  determinant (`Matrix.le_rank_iff_exists_det_submatrix_ne_zero`); equivalently
  `rank A ≤ r` if and only if every `(r + 1) × (r + 1)` minor vanishes
  (`Matrix.rank_le_iff_forall_det_submatrix_eq_zero`). A nonzero minor indexed by any finite
  type `ι` gives `card ι ≤ rank A` (`Matrix.card_le_rank_of_det_submatrix_ne_zero`).
* **Semicontinuity**: over a topological field whose points are closed, the matrices of rank at
  most `r` form a closed set (`Matrix.isClosed_setOf_rank_le`), so rank is lower semicontinuous
  (`Matrix.lowerSemicontinuous_rank`): a limit of matrices of rank at most `r` has rank at most
  `r`.
* **Block-triangular matrices**: the rank of `fromBlocks A B 0 D` or `fromBlocks A 0 C D` is at
  least `rank A + rank D`, whatever the off-diagonal block and whether or not the diagonal
  blocks are square or invertible.
* **Deleting rows and columns**: restricting to the rows in the range of `f` and the columns in
  the range of `g` lowers the rank by at most the number of deleted rows plus the number of
  deleted columns (`Matrix.rank_le_rank_submatrix_add`,
  `Matrix.rank_le_rank_submatrix_add_card_sub`).

Rank is invariant under permuting rows and columns by Mathlib's `Matrix.rank_submatrix` (for
equivalences) and `Matrix.rank_reindex`; Mathlib's `Matrix.rank_submatrix_le` says that
deleting rows and columns does not increase rank.
-/

@[expose] public section

namespace Matrix

variable {K : Type*} [Field K]
variable {m n m' n' : Type*} [Fintype n]

/-- Rank is subadditive. -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank :=
  Algebraic.MatrixRank.Internal.rank_add_le A B

/-- The rank of a finite sum is at most the sum of the ranks. -/
theorem rank_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix m n K) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank :=
  Algebraic.MatrixRank.Internal.rank_sum_le s A

/-- A square submatrix indexed by `ι` with nonzero determinant forces `card ι ≤ rank A`. -/
theorem card_le_rank_of_det_submatrix_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix m n K) (f : ι → m) (g : ι → n) (h : (A.submatrix f g).det ≠ 0) :
    Fintype.card ι ≤ A.rank :=
  Algebraic.MatrixRank.Internal.card_le_rank_of_det_ne_zero A f g h

/-- If `k ≤ rank A`, then some `k × k` minor of `A` is nonzero. -/
theorem exists_det_submatrix_ne_zero_of_le_rank [Fintype m] {k : ℕ} (A : Matrix m n K)
    (hk : k ≤ A.rank) : ∃ (f : Fin k → m) (g : Fin k → n), (A.submatrix f g).det ≠ 0 :=
  Algebraic.MatrixRank.Internal.exists_det_submatrix_ne_zero A hk

/-- **Rank by minors.** `k ≤ rank A` if and only if some `k × k` minor of `A` is nonzero. -/
theorem le_rank_iff_exists_det_submatrix_ne_zero [Fintype m] (A : Matrix m n K) (k : ℕ) :
    k ≤ A.rank ↔ ∃ (f : Fin k → m) (g : Fin k → n), (A.submatrix f g).det ≠ 0 :=
  ⟨exists_det_submatrix_ne_zero_of_le_rank A, fun ⟨f, g, h⟩ => by
    simpa using card_le_rank_of_det_submatrix_ne_zero A f g h⟩

/-- **Rank by minors.** `rank A ≤ r` if and only if every `(r + 1) × (r + 1)` minor of `A`
vanishes. -/
theorem rank_le_iff_forall_det_submatrix_eq_zero [Fintype m] (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔
      ∀ (f : Fin (r + 1) → m) (g : Fin (r + 1) → n), (A.submatrix f g).det = 0 :=
  Algebraic.MatrixRank.Internal.rank_le_iff_forall_det_eq_zero A r

/-- The matrices of rank at most `r` form a closed set. -/
theorem isClosed_setOf_rank_le [Fintype m] [TopologicalSpace K] [IsTopologicalRing K]
    [T1Space K] (r : ℕ) : IsClosed {A : Matrix m n K | A.rank ≤ r} :=
  Algebraic.MatrixRank.Internal.isClosed_setOf_rank_le r

/-- **Lower semicontinuity of rank.** -/
theorem lowerSemicontinuous_rank [Fintype m] [TopologicalSpace K] [IsTopologicalRing K]
    [T1Space K] : LowerSemicontinuous fun A : Matrix m n K => A.rank :=
  lowerSemicontinuous_iff_isClosed_preimage.mpr fun r => isClosed_setOf_rank_le r

section Blocks

variable {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]

/-- The rank of a block upper-triangular matrix is at least the sum of the ranks of its diagonal
blocks. -/
theorem rank_add_rank_le_rank_fromBlocks_zero₂₁ (A : Matrix m₁ n₁ K) (B : Matrix m₁ n₂ K)
    (D : Matrix m₂ n₂ K) : A.rank + D.rank ≤ (fromBlocks A B 0 D).rank :=
  Algebraic.MatrixRank.Internal.rank_add_rank_le_rank_fromBlocks_zero₂₁ A B D

/-- The rank of a block lower-triangular matrix is at least the sum of the ranks of its diagonal
blocks. -/
theorem rank_add_rank_le_rank_fromBlocks_zero₁₂ (A : Matrix m₁ n₁ K) (C : Matrix m₂ n₁ K)
    (D : Matrix m₂ n₂ K) : A.rank + D.rank ≤ (fromBlocks A 0 C D).rank :=
  Algebraic.MatrixRank.Internal.rank_add_rank_le_rank_fromBlocks_zero₁₂ A C D

end Blocks

/-- **Deleting rows and columns.** Keeping the rows in the range of `f` and the columns in the
range of `g` lowers the rank by at most the number of rows outside the range of `f` plus the
number of columns outside the range of `g`. -/
theorem rank_le_rank_submatrix_add [Fintype m] [Fintype m'] [Fintype n'] (A : Matrix m n K)
    (f : m' → m) (g : n' → n) :
    A.rank ≤ (A.submatrix f g).rank + Nat.card {i // i ∉ Set.range f} +
      Nat.card {j // j ∉ Set.range g} :=
  Algebraic.MatrixRank.Internal.rank_le_rank_submatrix_add A f g

/-- **Deleting rows and columns**, for injective reindexings: deleting
`card m - card m'` rows and `card n - card n'` columns lowers the rank by at most their total
number. -/
theorem rank_le_rank_submatrix_add_card_sub [Fintype m] [Fintype m'] [Fintype n']
    (A : Matrix m n K) {f : m' → m} {g : n' → n} (hf : Function.Injective f)
    (hg : Function.Injective g) :
    A.rank ≤ (A.submatrix f g).rank + (Fintype.card m - Fintype.card m') +
      (Fintype.card n - Fintype.card n') := by
  have h := rank_le_rank_submatrix_add A f g
  rwa [Algebraic.MatrixRank.Internal.natCard_not_mem_range hf,
    Algebraic.MatrixRank.Internal.natCard_not_mem_range hg] at h

end Matrix
