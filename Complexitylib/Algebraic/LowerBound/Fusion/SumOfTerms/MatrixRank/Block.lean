/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Support

/-!
# Block decompositions of matrix flattenings

A matrix block comes with finite row and column covers.  Its rank is bounded
by the smaller cover size.  If a matrix is a finite sum of such blocks, rank
subadditivity bounds its rank by the sum of those block budgets.

This witness-oriented interface is deliberately independent of how the blocks
are obtained.  Later polynomial adapters may use monomial partitions,
rectangle covers, or semantic decompositions without changing the linear
algebra layer.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace MatrixRank
namespace Block

noncomputable section

open Cardinal

/-- A matrix together with certified finite covers of its nonzero rows and
columns. -/
structure Piece
    (K I J : Type)
    [Field K]
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J] where
  /-- Matrix represented by this block. -/
  matrix : Matrix I J K
  /-- Rows allowed to contain nonzero entries. -/
  rows : Finset I
  /-- Columns allowed to contain nonzero entries. -/
  columns : Finset J
  /-- Every nonzero row lies in `rows`. -/
  rows_supported : Function.support matrix.row ⊆ rows
  /-- Every nonzero column lies in `columns`. -/
  columns_supported : Function.support matrix.col ⊆ columns

variable {K I J : Type}
variable [Field K] [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

/-- Rank budget charged to one supported block. -/
def Piece.rankBudget (piece : Piece K I J) : Nat :=
  min piece.rows.card piece.columns.card

/-- A supported block has rank at most its smaller side. -/
theorem Piece.rank_toLin'_le_rankBudget (piece : Piece K I J) :
    LinearMap.rank (Matrix.toLin' piece.matrix) ≤ piece.rankBudget := by
  by_cases rowLe : piece.rows.card ≤ piece.columns.card
  · rw [Piece.rankBudget, min_eq_left rowLe]
    exact Support.rank_toLin'_le_card_of_rowSupport_subset piece.matrix
      piece.rows piece.rows_supported
  · rw [Piece.rankBudget, min_eq_right (Nat.le_of_not_ge rowLe)]
    exact Support.rank_toLin'_le_card_of_columnSupport_subset piece.matrix
      piece.columns piece.columns_supported

/-- The canonical single block using the exact nonzero row and column
supports of a matrix. -/
def Piece.ofMatrix (matrix : Matrix I J K) : Piece K I J where
  matrix := matrix
  rows := Support.rowSupport matrix
  columns := Support.columnSupport matrix
  rows_supported := by
    intro row nonzero
    exact (Support.mem_rowSupport matrix row).2 nonzero
  columns_supported := by
    intro column nonzero
    exact (Support.mem_columnSupport matrix column).2 nonzero

@[simp] theorem Piece.ofMatrix_rankBudget (matrix : Matrix I J K) :
    (Piece.ofMatrix matrix).rankBudget =
      min (Support.rowSupport matrix).card
        (Support.columnSupport matrix).card := rfl

/-- A finite additive decomposition into supported matrix blocks. -/
structure Decomposition (matrix : Matrix I J K) where
  /-- Number of block occurrences. -/
  blockCount : Nat
  /-- The blocks, counted with multiplicity. -/
  block : Fin blockCount → Piece K I J
  /-- Their matrix sum is the represented matrix. -/
  sum_eq : ∑ index, (block index).matrix = matrix

/-- Sum of the smaller-side budgets of all block occurrences. -/
def Decomposition.rankBudget
    {matrix : Matrix I J K}
    (decomposition : Decomposition matrix) : Nat :=
  ∑ index, (decomposition.block index).rankBudget

/-- Rank subadditivity converts a block decomposition into a flattening-rank
bound. -/
theorem Decomposition.rank_toLin'_le_rankBudget
    {matrix : Matrix I J K}
    (decomposition : Decomposition matrix) :
    LinearMap.rank (Matrix.toLin' matrix) ≤ decomposition.rankBudget := by
  calc
    LinearMap.rank (Matrix.toLin' matrix) =
        LinearMap.rank
          (Matrix.toLin'
            (∑ index, (decomposition.block index).matrix)) := by
      rw [decomposition.sum_eq]
    _ = LinearMap.rank
        (∑ index, Matrix.toLin' (decomposition.block index).matrix) := by
      rw [map_sum]
    LinearMap.rank
        (∑ index, Matrix.toLin' (decomposition.block index).matrix) ≤
      ∑ index,
        LinearMap.rank (Matrix.toLin' (decomposition.block index).matrix) := by
      simpa using LinearMap.rank_finsetSum_le
        (Finset.univ : Finset (Fin decomposition.blockCount))
        (fun index ↦ Matrix.toLin' (decomposition.block index).matrix)
    _ ≤ ∑ index, ((decomposition.block index).rankBudget : Cardinal) := by
      apply Finset.sum_le_sum
      intro index _
      exact (decomposition.block index).rank_toLin'_le_rankBudget
    _ = decomposition.rankBudget := by
      simp [Decomposition.rankBudget]

/-- Empty decomposition of the zero matrix. -/
def Decomposition.zero : Decomposition (0 : Matrix I J K) where
  blockCount := 0
  block := Fin.elim0
  sum_eq := by simp

@[simp] theorem Decomposition.zero_rankBudget :
    (Decomposition.zero (K := K) (I := I) (J := J)).rankBudget = 0 := by
  simp [Decomposition.rankBudget, Decomposition.zero]

/-- Concatenate decompositions to represent the sum of their matrices. -/
abbrev Decomposition.add
    {left right : Matrix I J K}
    (leftDecomposition : Decomposition left)
    (rightDecomposition : Decomposition right) :
    Decomposition (left + right) where
  blockCount := leftDecomposition.blockCount + rightDecomposition.blockCount
  block := Fin.addCases leftDecomposition.block rightDecomposition.block
  sum_eq := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [leftDecomposition.sum_eq, rightDecomposition.sum_eq]

@[simp] theorem Decomposition.add_rankBudget
    {left right : Matrix I J K}
    (leftDecomposition : Decomposition left)
    (rightDecomposition : Decomposition right) :
    (leftDecomposition.add rightDecomposition).rankBudget =
      leftDecomposition.rankBudget + rightDecomposition.rankBudget := by
  have splitSum :
      (∑ index : Fin
          (leftDecomposition.blockCount + rightDecomposition.blockCount),
        ((Fin.addCases leftDecomposition.block rightDecomposition.block
          index : Piece K I J)).rankBudget) =
        (∑ index, (leftDecomposition.block index).rankBudget) +
          ∑ index, (rightDecomposition.block index).rankBudget := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
  simpa only [Decomposition.rankBudget, Decomposition.add] using splitSum

/-- Every matrix has the one-block decomposition given by its exact row and
column supports. -/
def Decomposition.single (matrix : Matrix I J K) : Decomposition matrix where
  blockCount := 1
  block := fun _ ↦ Piece.ofMatrix matrix
  sum_eq := by simp [Piece.ofMatrix]

@[simp] theorem Decomposition.single_rankBudget (matrix : Matrix I J K) :
    (Decomposition.single matrix).rankBudget =
      min (Support.rowSupport matrix).card
        (Support.columnSupport matrix).card := by
  unfold Decomposition.rankBudget
  change (∑ _index : Fin 1,
    min (Support.rowSupport matrix).card
      (Support.columnSupport matrix).card) = _
  rw [Fin.sum_univ_one]

end
end Block
end MatrixRank
end SumOfTerms
end Fusion
end Algebraic
