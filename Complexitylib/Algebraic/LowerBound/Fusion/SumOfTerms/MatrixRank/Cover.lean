/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Block

/-!
# Rectangle covers of matrix support

A finite family of row/column rectangles covers a matrix when every nonzero
entry lies in at least one rectangle.  We assign an overlapping entry to one
covering rectangle, thereby obtaining a supported-block decomposition.  This
proves the weighted rectangle-cover estimate

`rank A ≤ ∑_t min (|rows_t|) (|columns_t|)`.

The construction is coefficient-agnostic and reusable for every finite matrix
flattening.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace MatrixRank
namespace Cover

noncomputable section

open Cardinal

variable {K I J : Type}
variable [Field K] [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

/-- A finite family of combinatorial rectangles covering every nonzero matrix
entry.  Rectangles may overlap. -/
structure Certificate (matrix : Matrix I J K) where
  /-- Number of rectangle occurrences. -/
  rectangleCount : Nat
  /-- Row side of each rectangle. -/
  rows : Fin rectangleCount → Finset I
  /-- Column side of each rectangle. -/
  columns : Fin rectangleCount → Finset J
  /-- Every nonzero entry belongs to some rectangle. -/
  covers_support : ∀ row column, matrix row column ≠ 0 →
    ∃ index, row ∈ rows index ∧ column ∈ columns index

/-- Choose one covering rectangle for an entry, if one exists. -/
def Certificate.owner
    {matrix : Matrix I J K}
    (certificate : Certificate matrix)
    (row : I)
    (column : J) : Option (Fin certificate.rectangleCount) :=
  if covered : ∃ index,
      row ∈ certificate.rows index ∧ column ∈ certificate.columns index
    then some (Classical.choose covered)
    else none

omit [Fintype I] [Fintype J] in
theorem Certificate.owner_ne_none_of_ne_zero
    {matrix : Matrix I J K}
    (certificate : Certificate matrix)
    (row : I)
    (column : J)
    (nonzero : matrix row column ≠ 0) :
    certificate.owner row column ≠ none := by
  have covered := certificate.covers_support row column nonzero
  simp [Certificate.owner, covered]

omit [Fintype I] [Fintype J] in
theorem Certificate.mem_of_owner_eq_some
    {matrix : Matrix I J K}
    (certificate : Certificate matrix)
    (row : I)
    (column : J)
    (index : Fin certificate.rectangleCount)
    (owned : certificate.owner row column = some index) :
    row ∈ certificate.rows index ∧
      column ∈ certificate.columns index := by
  unfold Certificate.owner at owned
  split at owned
  · rename_i covered
    have chosen := Classical.choose_spec covered
    simp only [Option.some.injEq] at owned
    subst index
    exact chosen
  · simp at owned

/-- Entries assigned to one rectangle, with all other entries zeroed out. -/
def Certificate.pieceMatrix
    {matrix : Matrix I J K}
    (certificate : Certificate matrix)
    (index : Fin certificate.rectangleCount) : Matrix I J K :=
  fun row column ↦
    if certificate.owner row column = some index then matrix row column else 0

/-- The assigned entries form a block supported on the chosen rectangle. -/
def Certificate.piece
    {matrix : Matrix I J K}
    (certificate : Certificate matrix)
    (index : Fin certificate.rectangleCount) : Block.Piece K I J where
  matrix := certificate.pieceMatrix index
  rows := certificate.rows index
  columns := certificate.columns index
  rows_supported := by
    intro row nonzeroRow
    by_contra outside
    apply nonzeroRow
    funext column
    by_cases owned : certificate.owner row column = some index
    · exact (outside
        (certificate.mem_of_owner_eq_some row column index owned).1).elim
    · simp [Certificate.pieceMatrix, owned]
  columns_supported := by
    intro column nonzeroColumn
    by_contra outside
    apply nonzeroColumn
    funext row
    by_cases owned : certificate.owner row column = some index
    · exact (outside
        (certificate.mem_of_owner_eq_some row column index owned).2).elim
    · simp [Certificate.pieceMatrix, owned]

@[simp] theorem Certificate.piece_matrix
    {matrix : Matrix I J K}
    (certificate : Certificate matrix)
    (index : Fin certificate.rectangleCount) :
    (certificate.piece index).matrix = certificate.pieceMatrix index := rfl

/-- Assigning overlaps to one owner turns a rectangle cover into a supported
block decomposition. -/
abbrev Certificate.toDecomposition
    {matrix : Matrix I J K}
    (certificate : Certificate matrix) : Block.Decomposition matrix where
  blockCount := certificate.rectangleCount
  block := certificate.piece
  sum_eq := by
    ext row column
    simp only [Certificate.piece_matrix]
    rw [show (∑ index, certificate.pieceMatrix index) row column =
        ∑ index, certificate.pieceMatrix index row column by
      simpa using Matrix.sum_apply row column Finset.univ
        certificate.pieceMatrix]
    by_cases nonzero : matrix row column ≠ 0
    · have owned := certificate.owner_ne_none_of_ne_zero row column nonzero
      cases ownerEquation : certificate.owner row column with
      | none => exact (owned ownerEquation).elim
      | some index =>
          rw [Finset.sum_eq_single index]
          · simp [Certificate.pieceMatrix, ownerEquation]
          · intro other _ different
            have notOwned : certificate.owner row column ≠ some other := by
              rw [ownerEquation]
              exact fun equal ↦ different (Option.some.inj equal).symm
            simp [Certificate.pieceMatrix, notOwned]
          · intro notMember
            exact (notMember (Finset.mem_univ index)).elim
    · have zero : matrix row column = 0 := not_ne_iff.mp nonzero
      simp [Certificate.pieceMatrix, zero]

/-- Weighted size of a rectangle cover. -/
def Certificate.rankBudget
    {matrix : Matrix I J K}
    (certificate : Certificate matrix) : Nat :=
  ∑ index,
    min (certificate.rows index).card (certificate.columns index).card

@[simp] theorem Certificate.toDecomposition_rankBudget
    {matrix : Matrix I J K}
    (certificate : Certificate matrix) :
    certificate.toDecomposition.rankBudget = certificate.rankBudget := by
  simp [Block.Decomposition.rankBudget, Certificate.rankBudget,
    Certificate.toDecomposition, Certificate.piece, Block.Piece.rankBudget]

/-- A rectangle cover bounds flattening rank by its weighted size. -/
theorem Certificate.rank_toLin'_le_rankBudget
    {matrix : Matrix I J K}
    (certificate : Certificate matrix) :
    LinearMap.rank (Matrix.toLin' matrix) ≤ certificate.rankBudget := by
  rw [← certificate.toDecomposition_rankBudget]
  exact certificate.toDecomposition.rank_toLin'_le_rankBudget

/-- One rectangle formed by the exact nonzero rows and columns always covers
the matrix support. -/
abbrev Certificate.single (matrix : Matrix I J K) : Certificate matrix where
  rectangleCount := 1
  rows := fun _ ↦ Support.rowSupport matrix
  columns := fun _ ↦ Support.columnSupport matrix
  covers_support := by
    intro row column nonzero
    refine ⟨(0 : Fin 1), ?_, ?_⟩
    · apply (Support.mem_rowSupport matrix row).2
      intro rowZero
      apply nonzero
      simpa using congrFun rowZero column
    · apply (Support.mem_columnSupport matrix column).2
      intro columnZero
      apply nonzero
      simpa using congrFun columnZero row

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem Certificate.single_rankBudget (matrix : Matrix I J K) :
    (Certificate.single matrix).rankBudget =
      min (Support.rowSupport matrix).card
        (Support.columnSupport matrix).card := by
  unfold Certificate.rankBudget
  change (∑ _index : Fin 1,
    min (Support.rowSupport matrix).card
      (Support.columnSupport matrix).card) = _
  rw [Fin.sum_univ_one]

/-- Empty rectangle cover of the zero matrix. -/
def Certificate.zero : Certificate (0 : Matrix I J K) where
  rectangleCount := 0
  rows := Fin.elim0
  columns := Fin.elim0
  covers_support := by simp

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
@[simp] theorem Certificate.zero_rankBudget :
    (Certificate.zero (K := K) (I := I) (J := J)).rankBudget = 0 := by
  simp [Certificate.rankBudget, Certificate.zero]

end
end Cover
end MatrixRank
end SumOfTerms
end Fusion
end Algebraic
