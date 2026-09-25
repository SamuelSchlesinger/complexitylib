/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.DigitMonomials
public import Complexitylib.Algebraic.MassProduction.HighRate.Independence
public import Complexitylib.Algebraic.MassProduction.HighRate.Systematic

/-!
# A high-rate systematic code with punctured-line recovery

The retained common-zero-block monomials are distinct reduced monomials, so
their evaluation tables are independent. Choosing a basis among evaluation
rows gives a systematic information set of exactly the retained cardinality.
Every codeword preserves punctured-line recovery by linearity.

The information set and encoding matrices are chosen offline. No efficient
uniform procedure for finding them is asserted.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators LinearAlgebra.Projectivization

/-- A systematic field-valued code whose symbols are recoverable from every
punctured projective line through the target point. -/
structure LineCode (K Coordinate : Type*)
    [Field K] [Finite K] [Fintype Coordinate] where
  /-- The information positions, chosen once for the code. -/
  information : Set (Coordinate → K)
  /-- Encoding an arbitrary assignment to the information positions. -/
  encode : (information → K) → (Coordinate → K) → K
  /-- Encoding preserves the assigned information symbols. -/
  systematic : ∀ message index, encode message index.val = message index
  /-- Every nonzero projective direction supplies a recovery set. -/
  lineRecovery : ∀ message target (direction : ℙ K (Coordinate → K)),
    encode message target = ∑ point ∈ puncturedLine target direction, encode message point

/-- Digit matrices have distinct natural exponent vectors. -/
theorem digitDegrees_injective (Coordinate : Type*) (blockWidth blocks : Nat) :
    Function.Injective (digitDegrees (Coordinate := Coordinate)
      (blockWidth := blockWidth) (blocks := blocks)) := by
  intro left right equalDegrees
  apply (digitExponentEquiv Coordinate blockWidth blocks).injective
  funext coordinate
  exact Fin.ext (congrFun equalDegrees coordinate)

/-- A code with `N - (A-1)^m` information symbols exists over the whole
`N = A^m` point space, where `A = 2^(dimension * blockWidth)`. -/
theorem existsHighRateLineCode
    {K Coordinate : Type u}
    [Field K] [Fintype K] [CharP K 2] [Fintype Coordinate] [Nonempty Coordinate]
    (blockWidth blocks : Nat) (blockPositive : 0 < blockWidth)
    (dimensionFits : Fintype.card Coordinate ≤ 2 ^ blockWidth)
    (fieldCard : Fintype.card K = 2 ^ (blockWidth * blocks)) :
    ∃ code : LineCode K Coordinate,
      Nat.card code.information =
        (2 ^ (blockWidth * Fintype.card Coordinate)) ^ blocks -
          (2 ^ (blockWidth * Fintype.card Coordinate) - 1) ^ blocks := by
  classical
  let Index := RetainedDigits Coordinate blockWidth blocks
  let degrees : Index → Coordinate → Nat := fun index => digitDegrees index.val
  let functions : Index → (Coordinate → K) → K := fun index => monomialValue (degrees index)
  have degreesDistinct : Function.Injective degrees :=
    (digitDegrees_injective Coordinate blockWidth blocks).comp Subtype.val_injective
  have reduced : ∀ index coordinate, degrees index coordinate < Fintype.card K := by
    intro index coordinate
    rw [fieldCard]
    exact digitDegrees_lt index.val coordinate
  have independent : LinearIndependent K functions :=
    monomialValuesLinearIndependent degrees degreesDistinct reduced
  obtain ⟨information, informationCard, encoder, systematic⟩ :=
    existsSystematicEncoder functions independent
  let row := flip functions
  let code : LineCode K Coordinate := {
    information := information
    encode := fun message point => encoder message (row point)
    systematic := systematic
    lineRecovery := by
      intro message target direction
      have rowRecovery : row target = ∑ point ∈ puncturedLine target direction, row point := by
        funext index
        simp only [Finset.sum_apply]
        obtain ⟨block, zeroBlock⟩ := retainedDigitsCommonZeroBlock index
        have blockFits : blockWidth * block.val + blockWidth ≤ blockWidth * blocks := by
          calc
            _ = blockWidth * (block.val + 1) := by ring
            _ ≤ _ := Nat.mul_le_mul_left _ block.isLt
        exact monomialValueSumPuncturedLine (degrees index) target direction
          (blockWidth * blocks) (blockWidth * block.val) blockWidth fieldCard
          blockPositive blockFits dimensionFits (digitDegrees_lt index.val) zeroBlock
      change encoder message (row target) =
        ∑ point ∈ puncturedLine target direction, encoder message (row point)
      rw [rowRecovery, map_sum]
  }
  refine ⟨code, ?_⟩
  change Nat.card information = _
  rw [informationCard, ← Nat.card_eq_fintype_card]
  exact cardRetainedDigits Coordinate blockWidth blocks

end Algebraic.MassProduction.HighRate
