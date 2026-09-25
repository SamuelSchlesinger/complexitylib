/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.BooleanRecovery

/-!
# Existence of the high-rate code and complete source-bit placement

The monomial construction supplies the exact information dimension. Its
positivity then gives an offline placement for any source table, using the
quotient-plus-one number of code copies from the finite packing bound.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped LinearAlgebra.Projectivization

/-- Retaining at least one digit block gives a nonempty information space. -/
theorem retainedDimension_positive (alphabet blocks : Nat)
    (alphabetPositive : 0 < alphabet) (blocksPositive : 0 < blocks) :
    0 < retainedDimension alphabet blocks := by
  unfold retainedDimension
  apply Nat.sub_pos_iff_lt.mpr
  exact Nat.pow_lt_pow_left (by omega : alphabet - 1 < alphabet) (by omega : blocks ≠ 0)

/-- A systematic binary-extension line code and a placement of every source
bit exist with exactly the prescribed information dimension and copy count. -/
theorem existsBinaryCodeAndPlacement (blockWidth blocks dimension prefixWidth : Nat)
    (blockPositive : 0 < blockWidth) (blocksPositive : 0 < blocks) (dimensionPositive : 0 < dimension)
    (dimensionFits : dimension ≤ 2 ^ blockWidth) :
    ∃ code : LineCode (BinaryExtension (blockWidth * blocks)) (Fin dimension),
      Nat.card code.information = retainedDimension (2 ^ (blockWidth * dimension)) blocks ∧
      Nonempty (Fin (2 ^ prefixWidth) ↪ InformationBit code
        (packingCopies (2 ^ prefixWidth) (retainedDimension (2 ^ (blockWidth * dimension)) blocks) (blockWidth * blocks))) := by
  classical
  have widthPositive : 0 < blockWidth * blocks := Nat.mul_pos blockPositive blocksPositive
  let _ := Fintype.ofFinite (BinaryExtension (blockWidth * blocks))
  let _ : Nonempty (Fin dimension) := ⟨⟨0, dimensionPositive⟩⟩
  have fieldCard : Fintype.card (BinaryExtension (blockWidth * blocks)) = 2 ^ (blockWidth * blocks) := by
    rw [← Nat.card_eq_fintype_card, card_binaryExtension widthPositive]
  obtain ⟨code, dimensionExact⟩ := existsHighRateLineCode
    (K := BinaryExtension (blockWidth * blocks)) (Coordinate := Fin dimension)
    blockWidth blocks blockPositive (by simpa only [Fintype.card_fin] using dimensionFits) fieldCard
  have informationExact : Nat.card code.information = retainedDimension (2 ^ (blockWidth * dimension)) blocks := by
    simpa only [Fintype.card_fin, retainedDimension] using dimensionExact
  let _ := Fintype.ofFinite code.information
  have informationCard : Fintype.card code.information = retainedDimension (2 ^ (blockWidth * dimension)) blocks := by
    simpa only [Nat.card_eq_fintype_card] using informationExact
  have informationPositive : 0 < Fintype.card code.information := by
    rw [informationCard]
    exact retainedDimension_positive _ _ (by positivity) blocksPositive
  have placement := existsPackingPlacement (Information := code.information) (2 ^ prefixWidth)
    (blockWidth * blocks) informationPositive widthPositive
  rw [informationCard] at placement
  exact ⟨code, informationExact, placement⟩

end Algebraic.MassProduction.HighRate
