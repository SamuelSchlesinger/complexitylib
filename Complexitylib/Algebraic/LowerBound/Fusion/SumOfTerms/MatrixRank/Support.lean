/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank

/-!
# Support bounds for matrix flattenings

The rank of a finite matrix is at most the number of rows or columns on which
it is supported.  This module converts Mathlib's natural-valued matrix-rank
bound to the cardinal-valued rank used by Fusion certificates, and packages
canonical finite row and column supports.

Nothing here depends on polynomials or a particular circuit model.  Any future
matrix-valued feature, including shifted flattenings, can reuse these lemmas.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace MatrixRank
namespace Support

noncomputable section

open Cardinal

variable {K I J : Type}

/-- On finite index types, the rank of matrix-vector multiplication is the
natural-valued matrix rank, coerced to a cardinal. -/
theorem rank_toLin'_eq_matrixRank
    [Field K]
    [Fintype J]
    [DecidableEq J]
    (matrix : Matrix I J K) :
    LinearMap.rank (Matrix.toLin' matrix) = (matrix.rank : Cardinal) := by
  rw [LinearMap.rank, ← Module.finrank_eq_rank K]
  norm_cast

/-- A finite set containing every nonzero row bounds flattening rank. -/
theorem rank_toLin'_le_card_of_rowSupport_subset
    [Field K]
    [Fintype J]
    [DecidableEq J]
    (matrix : Matrix I J K)
    (rows : Finset I)
    (supported : Function.support matrix.row ⊆ rows) :
    LinearMap.rank (Matrix.toLin' matrix) ≤ rows.card := by
  rw [rank_toLin'_eq_matrixRank matrix]
  exact_mod_cast
    Matrix.rank_le_card_of_support_subset matrix rows supported

/-- A finite set containing every nonzero column bounds flattening rank. -/
theorem rank_toLin'_le_card_of_columnSupport_subset
    [Field K]
    [Fintype I]
    [Fintype J]
    [DecidableEq J]
    (matrix : Matrix I J K)
    (columns : Finset J)
    (supported : Function.support matrix.col ⊆ columns) :
    LinearMap.rank (Matrix.toLin' matrix) ≤ columns.card := by
  rw [rank_toLin'_eq_matrixRank matrix]
  have matrixBound : matrix.rank ≤ columns.card := by
    rw [← Matrix.rank_transpose]
    apply Matrix.rank_le_card_of_support_subset matrix.transpose columns
    simpa [Matrix.row_transpose] using supported
  exact_mod_cast matrixBound

/-- The canonical finite set of nonzero rows. -/
def rowSupport
    [Zero K]
    [Fintype I]
    (matrix : Matrix I J K) : Finset I :=
  by
    classical
    exact Finset.univ.filter fun row ↦ matrix.row row ≠ 0

@[simp] theorem mem_rowSupport
    [Zero K]
    [Fintype I]
    (matrix : Matrix I J K)
    (row : I) :
    row ∈ rowSupport matrix ↔ matrix.row row ≠ 0 := by
  simp [rowSupport]

/-- The canonical finite set of nonzero columns. -/
def columnSupport
    [Zero K]
    [Fintype J]
    (matrix : Matrix I J K) : Finset J :=
  by
    classical
    exact Finset.univ.filter fun column ↦ matrix.col column ≠ 0

@[simp] theorem mem_columnSupport
    [Zero K]
    [Fintype J]
    (matrix : Matrix I J K)
    (column : J) :
    column ∈ columnSupport matrix ↔ matrix.col column ≠ 0 := by
  simp [columnSupport]

/-- Flattening rank is at most the number of its nonzero rows. -/
theorem rank_toLin'_le_card_rowSupport
    [Field K]
    [Fintype I]
    [Fintype J]
    [DecidableEq J]
    (matrix : Matrix I J K) :
    LinearMap.rank (Matrix.toLin' matrix) ≤ (rowSupport matrix).card := by
  apply rank_toLin'_le_card_of_rowSupport_subset matrix (rowSupport matrix)
  intro row nonzero
  simpa [Function.mem_support] using nonzero

/-- Flattening rank is at most the number of its nonzero columns. -/
theorem rank_toLin'_le_card_columnSupport
    [Field K]
    [Fintype I]
    [Fintype J]
    [DecidableEq J]
    (matrix : Matrix I J K) :
    LinearMap.rank (Matrix.toLin' matrix) ≤ (columnSupport matrix).card := by
  apply rank_toLin'_le_card_of_columnSupport_subset matrix
    (columnSupport matrix)
  intro column nonzero
  simpa [Function.mem_support] using nonzero

/-- Using both sides gives the smaller of the nonzero-row and nonzero-column
counts. -/
theorem rank_toLin'_le_min_support
    [Field K]
    [Fintype I]
    [Fintype J]
    [DecidableEq J]
    (matrix : Matrix I J K) :
    LinearMap.rank (Matrix.toLin' matrix) ≤
      min (rowSupport matrix).card (columnSupport matrix).card := by
  by_cases rowLe : (rowSupport matrix).card ≤ (columnSupport matrix).card
  · rw [min_eq_left rowLe]
    exact rank_toLin'_le_card_rowSupport matrix
  · rw [min_eq_right (Nat.le_of_not_ge rowLe)]
    exact rank_toLin'_le_card_columnSupport matrix

end
end Support
end MatrixRank
end SumOfTerms
end Fusion
end Algebraic
