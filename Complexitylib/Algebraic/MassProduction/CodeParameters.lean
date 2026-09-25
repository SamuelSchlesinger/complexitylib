/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.FiniteParameters

/-!
# Finite evaluation-code parameter selection

The field width must satisfy two competing requirements.  Its interpolation
grid must hold all `2^prefixWidth` prefix bits, while the number of resource
bits must remain within a dimension-dependent constant factor of that same
quantity.  Choosing a merely convenient large field would lose a factor of
`prefixWidth` and therefore destroy the final `2^n / n` bound.

We consequently choose the least field width above a fixed safe floor which
satisfies the exact packing inequality.  This is nonuniform parameter
selection, not a run-time computation, and introduces no instances.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace CodeParameters

open scoped LinearAlgebra.Projectivization
open CanonicalPacking
open GroupedScheduler
open LineEnumeration
open ResourceEvaluation

/-- A safe dimension-dependent floor for the binary-extension width. -/
def baseWidth (dimension : Nat) : Nat :=
  2 * dimension + 2

/-- A coarse explicit candidate used only to prove that minimal parameter
selection is nonempty. -/
def candidateWidth (prefixWidth dimension : Nat) : Nat :=
  prefixWidth ⌈/⌉ dimension + 4 * dimension + 2

/-- Exact admissibility predicate for a binary-extension width. -/
def Admissible
    (prefixWidth dimension width : Nat) : Prop :=
  baseWidth dimension <= width ∧
    2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width

private theorem dimension_lt_large_power
    (dimension : Nat) (dimensionPositive : 0 < dimension) :
    dimension < 2 ^ (4 * dimension + 2) := by
  have selfPower : dimension < 2 ^ dimension :=
    @Nat.lt_pow_self dimension 2 (by omega)
  have exponentBound : dimension <= 4 * dimension + 2 := by omega
  exact selfPower.trans_le
    (Nat.pow_le_pow_right (by omega : 0 < 2) exponentBound)

private theorem candidate_grid_lower
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    2 ^ (prefixWidth ⌈/⌉ dimension) <=
      gridWidth dimension (candidateWidth prefixWidth dimension) := by
  let quotient := prefixWidth ⌈/⌉ dimension
  have dimensionPower := dimension_lt_large_power dimension dimensionPositive
  have multiplied :
      dimension * 2 ^ quotient <
        2 ^ (candidateWidth prefixWidth dimension) := by
    calc
      dimension * 2 ^ quotient <
          2 ^ (4 * dimension + 2) * 2 ^ quotient :=
        Nat.mul_lt_mul_of_pos_right dimensionPower
          (Nat.pow_pos (by omega))
      _ = 2 ^ quotient * 2 ^ (4 * dimension + 2) := by
        rw [Nat.mul_comm]
      _ = 2 ^ (quotient + (4 * dimension + 2)) := by
        exact (Nat.pow_add 2 quotient (4 * dimension + 2)).symm
      _ = 2 ^ (candidateWidth prefixWidth dimension) := by
        unfold candidateWidth quotient
        congr 1
  have belowPred :
      dimension * 2 ^ quotient <=
        2 ^ (candidateWidth prefixWidth dimension) - 1 := by
    omega
  rw [gridWidth_eq (dimension := dimension)
    (width := candidateWidth prefixWidth dimension) (by
      unfold candidateWidth
      omega)]
  unfold resourceGridWidth
  apply (Nat.le_div_iff_mul_le dimensionPositive).mpr
  simpa only [Nat.mul_comm] using belowPred

theorem candidate_admissible
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    Admissible prefixWidth dimension
      (candidateWidth prefixWidth dimension) := by
  constructor
  · unfold baseWidth candidateWidth
    have quotientNonnegative : 0 <= prefixWidth ⌈/⌉ dimension :=
      Nat.zero_le _
    omega
  · let quotient := prefixWidth ⌈/⌉ dimension
    have prefixFitsExponent : prefixWidth <= dimension * quotient := by
      exact (ceilDiv_le_iff_le_mul dimensionPositive).mp le_rfl
    have powerFits :
        2 ^ prefixWidth <= 2 ^ (dimension * quotient) :=
      Nat.pow_le_pow_right (by omega) prefixFitsExponent
    have gridLower := candidate_grid_lower prefixWidth dimension
      dimensionPositive
    have gridPower :
        (2 ^ quotient) ^ dimension <=
          gridWidth dimension (candidateWidth prefixWidth dimension) ^
            dimension :=
      Nat.pow_le_pow_left gridLower dimension
    have powerIdentity :
        2 ^ (dimension * quotient) = (2 ^ quotient) ^ dimension := by
      rw [Nat.mul_comm dimension quotient, Nat.pow_mul]
    calc
      2 ^ prefixWidth <= (2 ^ quotient) ^ dimension := by
        rw [← powerIdentity]
        exact powerFits
      _ <= gridWidth dimension (candidateWidth prefixWidth dimension) ^
          dimension := gridPower
      _ <= gridWidth dimension (candidateWidth prefixWidth dimension) ^
          dimension * candidateWidth prefixWidth dimension := by
        nth_rewrite 1 [← Nat.mul_one
          (gridWidth dimension (candidateWidth prefixWidth dimension) ^
            dimension)]
        apply Nat.mul_le_mul_left
        unfold candidateWidth
        omega

/-- Least admissible binary-extension width above `baseWidth`. -/
noncomputable def fieldWidth
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) : Nat :=
  by
    classical
    exact Nat.find ⟨candidateWidth prefixWidth dimension,
      candidate_admissible prefixWidth dimension dimensionPositive⟩

theorem fieldWidth_admissible
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    Admissible prefixWidth dimension
      (fieldWidth prefixWidth dimension dimensionPositive) := by
  classical
  exact Nat.find_spec ⟨candidateWidth prefixWidth dimension,
    candidate_admissible prefixWidth dimension dimensionPositive⟩

theorem baseWidth_le_fieldWidth
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    baseWidth dimension <= fieldWidth prefixWidth dimension dimensionPositive :=
  (fieldWidth_admissible prefixWidth dimension dimensionPositive).1

theorem fieldWidth_packingFits
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    2 ^ prefixWidth <=
      gridWidth dimension (fieldWidth prefixWidth dimension dimensionPositive) ^
        dimension * fieldWidth prefixWidth dimension dimensionPositive :=
  (fieldWidth_admissible prefixWidth dimension dimensionPositive).2

theorem fieldWidth_le_candidate
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    fieldWidth prefixWidth dimension dimensionPositive <=
      candidateWidth prefixWidth dimension := by
  classical
  exact Nat.find_min'
    ⟨candidateWidth prefixWidth dimension,
      candidate_admissible prefixWidth dimension dimensionPositive⟩
    (candidate_admissible prefixWidth dimension dimensionPositive)

/-- Ceiling division differs from ordinary natural division by at most one. -/
theorem ceilDiv_le_div_add_one
    (value divisor : Nat)
    (divisorPositive : 0 < divisor) :
    value ⌈/⌉ divisor <= value / divisor + 1 := by
  apply (ceilDiv_le_iff_le_mul divisorPositive).2
  exact Nat.le_of_lt (Nat.lt_mul_div_succ value divisorPositive)

/-- A division-based upper bound on the least admissible field width. -/
theorem fieldWidth_le_quotient_add
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    fieldWidth prefixWidth dimension dimensionPositive <=
      prefixWidth / dimension + (4 * dimension + 3) := by
  exact (fieldWidth_le_candidate prefixWidth dimension
    dimensionPositive).trans (by
      unfold candidateWidth
      have := ceilDiv_le_div_add_one prefixWidth dimension dimensionPositive
      omega)

/-- The selected field cardinality is a fixed dimension-dependent factor
times the ideal `2^(prefixWidth / dimension)` rate. -/
theorem fieldCard_le
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    2 ^ fieldWidth prefixWidth dimension dimensionPositive <=
      2 ^ (4 * dimension + 3) * 2 ^ (prefixWidth / dimension) := by
  have widthBound := fieldWidth_le_quotient_add prefixWidth dimension
    dimensionPositive
  calc
    2 ^ fieldWidth prefixWidth dimension dimensionPositive <=
        2 ^ (prefixWidth / dimension + (4 * dimension + 3)) :=
      Nat.pow_le_pow_right (by omega) widthBound
    _ = 2 ^ (4 * dimension + 3) *
        2 ^ (prefixWidth / dimension) := by
      rw [Nat.pow_add]
      ring

/-- Raising the selected field cardinality to the fixed code dimension costs
only a fixed factor beyond the prefix truth-table size. -/
theorem fieldCard_pow_dimension_le
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    2 ^ (dimension *
        fieldWidth prefixWidth dimension dimensionPositive) <=
      2 ^ (dimension * (4 * dimension + 3)) * 2 ^ prefixWidth := by
  have widthBound := fieldWidth_le_quotient_add prefixWidth dimension
    dimensionPositive
  have exponentBound :
      dimension * fieldWidth prefixWidth dimension dimensionPositive <=
        dimension * (4 * dimension + 3) + prefixWidth := by
    calc
      dimension * fieldWidth prefixWidth dimension dimensionPositive <=
          dimension * (prefixWidth / dimension +
            (4 * dimension + 3)) := Nat.mul_le_mul_left dimension widthBound
      _ = dimension * (prefixWidth / dimension) +
          dimension * (4 * dimension + 3) := by ring
      _ <= prefixWidth + dimension * (4 * dimension + 3) := by
        gcongr
        exact Nat.mul_div_le prefixWidth dimension
      _ = dimension * (4 * dimension + 3) + prefixWidth := by omega
  calc
    2 ^ (dimension *
        fieldWidth prefixWidth dimension dimensionPositive) <=
      2 ^ (dimension * (4 * dimension + 3) + prefixWidth) :=
        Nat.pow_le_pow_right (by omega) exponentBound
    _ = 2 ^ (dimension * (4 * dimension + 3)) * 2 ^ prefixWidth := by
      rw [Nat.pow_add]

theorem fieldWidth_minimal
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension)
    {width : Nat}
    (smaller : width < fieldWidth prefixWidth dimension dimensionPositive) :
    ¬ Admissible prefixWidth dimension width := by
  classical
  exact Nat.find_min
    ⟨candidateWidth prefixWidth dimension,
      candidate_admissible prefixWidth dimension dimensionPositive⟩ smaller

theorem fieldWidth_atLeastTwo
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    2 <= fieldWidth prefixWidth dimension dimensionPositive := by
  have := baseWidth_le_fieldWidth prefixWidth dimension dimensionPositive
  unfold baseWidth at this
  omega

theorem fieldWidth_positive
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    0 < fieldWidth prefixWidth dimension dimensionPositive :=
  (fieldWidth_atLeastTwo prefixWidth dimension dimensionPositive).trans_lt'
    (by omega)

theorem fieldWidth_gridPositive
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    0 < gridWidth dimension
      (fieldWidth prefixWidth dimension dimensionPositive) := by
  let width := fieldWidth prefixWidth dimension dimensionPositive
  have packing := fieldWidth_packingFits prefixWidth dimension
    dimensionPositive
  change 2 ^ prefixWidth <=
    gridWidth dimension width ^ dimension * width at packing
  apply Nat.pos_of_ne_zero
  intro gridZero
  rw [gridZero, Nat.zero_pow dimensionPositive, zero_mul] at packing
  have powerPositive : 0 < 2 ^ prefixWidth := Nat.pow_pos (by omega)
  omega

/-- Packing forces the selected field width to carry at least the prefix
information rate.  The extra `+ 1` accounts for the basis-bit coordinate in
the packed grid. -/
theorem prefixWidth_le_succ_dimension_mul_fieldWidth
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    prefixWidth <= (dimension + 1) *
      fieldWidth prefixWidth dimension dimensionPositive := by
  let width := fieldWidth prefixWidth dimension dimensionPositive
  have widthPositive := fieldWidth_positive prefixWidth dimension
    dimensionPositive
  have packing := fieldWidth_packingFits prefixWidth dimension
    dimensionPositive
  have gridBound : gridWidth dimension width <= 2 ^ width := by
    rw [gridWidth_eq widthPositive]
    unfold resourceGridWidth
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have widthBound : width <= 2 ^ width := by
    exact (by omega : width <= 2 * width).trans
      (Nat.mul_le_pow (by decide : 2 ≠ 1) width)
  have packedUpper :
      gridWidth dimension width ^ dimension * width <=
        2 ^ ((dimension + 1) * width) := by
    calc
      gridWidth dimension width ^ dimension * width <=
          (2 ^ width) ^ dimension * 2 ^ width :=
        Nat.mul_le_mul (Nat.pow_le_pow_left gridBound dimension)
          widthBound
      _ = 2 ^ ((dimension + 1) * width) := by
        rw [← Nat.pow_mul, ← Nat.pow_add]
        congr 1
        ring
  apply (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp
  exact packing.trans packedUpper

/-! ## Minimality preserves the code rate -/

/-- Once the safe width floor has been passed, the current field cardinality
is controlled by the preceding width's interpolation grid. -/
private theorem fieldCard_le_four_mul_previousGrid
    (dimension width : Nat)
    (dimensionPositive : 0 < dimension)
    (pastBase : baseWidth dimension < width) :
    2 ^ width <=
      4 * dimension * gridWidth dimension (width - 1) := by
  let atom := 2 ^ (width - 2)
  have widthAtLeast : 2 * dimension + 3 <= width := by
    unfold baseWidth at pastBase
    omega
  have exponentBound : dimension <= width - 2 := by omega
  have dimensionLeAtom : dimension <= atom := by
    have dimensionLeOwnPower : dimension <= 2 ^ dimension :=
      Nat.le_of_lt (@Nat.lt_pow_self dimension 2 (by omega))
    exact dimensionLeOwnPower.trans
      (Nat.pow_le_pow_right (by omega) exponentBound)
  have previousPower : 2 ^ (width - 1) = 2 * atom := by
    unfold atom
    conv_lhs => rw [show width - 1 = (width - 2) + 1 by omega]
    rw [Nat.pow_succ]
    ring
  have currentPower : 2 ^ width = 4 * atom := by
    unfold atom
    conv_lhs => rw [show width = (width - 2) + 2 by omega]
    rw [Nat.pow_add]
    norm_num
    ring
  let dividend := 2 ^ (width - 1) - 1
  let quotient := dividend / dimension
  let remainder := dividend % dimension
  have divisionIdentity : dimension * quotient + remainder = dividend := by
    exact Nat.div_add_mod dividend dimension
  have remainderSmall : remainder < dimension := by
    exact Nat.mod_lt dividend dimensionPositive
  have divisionIdentity' :
      quotient * dimension + remainder = 2 * atom - 1 := by
    rw [Nat.mul_comm quotient dimension, divisionIdentity]
    dsimp [dividend]
    rw [previousPower]
  have atomLeProduct : atom <= quotient * dimension := by
    omega
  have gridEquality :
      gridWidth dimension (width - 1) = quotient := by
    rw [gridWidth_eq (dimension := dimension) (width := width - 1) (by omega)]
    rfl
  calc
    2 ^ width = 4 * atom := currentPower
    _ <= 4 * (quotient * dimension) :=
      Nat.mul_le_mul_left 4 atomLeProduct
    _ = 4 * dimension * gridWidth dimension (width - 1) := by
      rw [gridEquality]
      ring

/-- Dimension-dependent constant in the resource-count estimate. -/
def resourceConstant (dimension : Nat) : Nat :=
  2 ^ (dimension * baseWidth dimension) * baseWidth dimension +
    2 * (4 * dimension) ^ dimension

/-- Minimal field selection keeps the exact number of `(point, bit)`
resources within a fixed dimension-dependent factor of `2^prefixWidth`. -/
theorem resourceBitCount_le
    (prefixWidth dimension : Nat)
    (dimensionPositive : 0 < dimension) :
    resourceBitCount dimension
        (fieldWidth prefixWidth dimension dimensionPositive) <=
      resourceConstant dimension * 2 ^ prefixWidth := by
  let width := fieldWidth prefixWidth dimension dimensionPositive
  have baseBound := baseWidth_le_fieldWidth prefixWidth dimension
    dimensionPositive
  change baseWidth dimension <= width at baseBound
  change resourceBitCount dimension width <=
    resourceConstant dimension * 2 ^ prefixWidth
  rcases baseBound.eq_or_lt with atBase | pastBase
  · have widthEquality : width = baseWidth dimension := atBase.symm
    unfold resourceBitCount pointCount
    rw [widthEquality]
    have fixedLeConstant :
        2 ^ (dimension * baseWidth dimension) * baseWidth dimension <=
          resourceConstant dimension := by
      unfold resourceConstant
      omega
    calc
      2 ^ (dimension * baseWidth dimension) * baseWidth dimension <=
          resourceConstant dimension := fixedLeConstant
      _ <= resourceConstant dimension * 2 ^ prefixWidth := by
        nth_rewrite 1 [← Nat.mul_one (resourceConstant dimension)]
        apply Nat.mul_le_mul_left
        exact Nat.one_le_pow prefixWidth 2 (by omega)
  · have widthPositive : 0 < width := by
      unfold baseWidth at baseBound
      omega
    have widthAtLeastTwo : 2 <= width := by
      have safeFloor := baseBound
      unfold baseWidth at safeFloor
      omega
    have previousSmaller : width - 1 < width := Nat.pred_lt widthPositive.ne'
    have previousBase : baseWidth dimension <= width - 1 := by omega
    have previousNotAdmissible := fieldWidth_minimal prefixWidth dimension
      dimensionPositive previousSmaller
    have previousPackingFails :
        gridWidth dimension (width - 1) ^ dimension * (width - 1) <
          2 ^ prefixWidth := by
      have notPacking : ¬ 2 ^ prefixWidth <=
          gridWidth dimension (width - 1) ^ dimension * (width - 1) := by
        intro packing
        exact previousNotAdmissible ⟨previousBase, packing⟩
      omega
    have fieldCardBound := fieldCard_le_four_mul_previousGrid
      dimension width dimensionPositive pastBase
    have fieldPowerBound :
        (2 ^ width) ^ dimension <=
          (4 * dimension * gridWidth dimension (width - 1)) ^ dimension :=
      Nat.pow_le_pow_left fieldCardBound dimension
    have widthBound : width <= 2 * (width - 1) := by omega
    have previousPackingBound :
        gridWidth dimension (width - 1) ^ dimension * (width - 1) <=
          2 ^ prefixWidth :=
      Nat.le_of_lt previousPackingFails
    have coefficientBound :
        2 * (4 * dimension) ^ dimension <= resourceConstant dimension := by
      unfold resourceConstant
      omega
    unfold resourceBitCount pointCount
    calc
      2 ^ (dimension * width) * width = (2 ^ width) ^ dimension * width := by
        rw [Nat.mul_comm dimension width, Nat.pow_mul]
      _ <= (4 * dimension * gridWidth dimension (width - 1)) ^
          dimension * width := Nat.mul_le_mul_right width fieldPowerBound
      _ = ((4 * dimension) ^ dimension *
          gridWidth dimension (width - 1) ^ dimension) * width := by
        rw [Nat.mul_pow]
      _ <= ((4 * dimension) ^ dimension *
          gridWidth dimension (width - 1) ^ dimension) *
            (2 * (width - 1)) :=
        Nat.mul_le_mul_left _ widthBound
      _ = (2 * (4 * dimension) ^ dimension) *
          (gridWidth dimension (width - 1) ^ dimension *
            (width - 1)) := by ring
      _ <= (2 * (4 * dimension) ^ dimension) * 2 ^ prefixWidth :=
        Nat.mul_le_mul_left _ previousPackingBound
      _ <= resourceConstant dimension * 2 ^ prefixWidth :=
        Nat.mul_le_mul_right _ coefficientBound

/-! ## Projective-direction capacity and finite composition -/

/-- The projective direction space contains at least the top term of its
geometric cardinality sum. -/
theorem projectiveDirections_lower
    (dimension width : Nat)
    (dimensionPositive : 0 < dimension)
    (widthPositive : 0 < width) :
    2 ^ (width * (dimension - 1)) <=
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := by
  rw [card_projectiveDirections]
  have fieldCard : Nat.card (BinaryExtension width) = 2 ^ width :=
    card_binaryExtension widthPositive
  rw [fieldCard]
  have topMember : dimension - 1 ∈ Finset.range dimension := by
    simp only [Finset.mem_range]
    omega
  calc
    2 ^ (width * (dimension - 1)) =
        (2 ^ width) ^ (dimension - 1) := by
      rw [Nat.pow_mul]
    _ <= ∑ exponent ∈ Finset.range dimension, (2 ^ width) ^ exponent := by
      exact Finset.single_le_sum
        (fun exponent _membership => Nat.zero_le _)
        topMember

/-- A simple exponential load inequality implies the exact scheduler
direction-capacity hypothesis. -/
theorem directionCapacity_of_load
    (totalRequests groups dimension width : Nat)
    (dimensionPositive : 0 < dimension)
    (widthPositive : 0 < width)
    (loadBound : requestGroupSize totalRequests groups * 2 ^ width <
      2 ^ (width * (dimension - 1))) :
    requestGroupSize totalRequests groups * nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := by
  have scalarBound : nonzeroScalarCount width <= 2 ^ width := by
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    exact Nat.sub_le _ _
  exact (Nat.mul_le_mul_left _ scalarBound).trans_lt <|
    loadBound.trans_le
      (projectiveDirections_lower dimension width dimensionPositive
        widthPositive)

set_option maxHeartbeats 3000000 in
/-- Composition with the least admissible field width and canonical routing
bookkeeping. -/
theorem booleanMassComplexity_le
    (totalRequests groups prefixWidth dimension suffixWidth : Nat)
    (dimensionAtLeastTwo : 2 <= dimension)
    (groupsPositive : 0 < groups)
    (suffixLarge : 16 <= suffixWidth)
    (loadBound : requestGroupSize totalRequests groups *
        2 ^ fieldWidth prefixWidth dimension
          (show 0 < dimension by omega) <
      2 ^ (fieldWidth prefixWidth dimension
        (show 0 < dimension by omega) * (dimension - 1)))
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (resourceBound : Nat)
    (resourceComplexity : forall member : Fin (resourceBitCount dimension
        (fieldWidth prefixWidth dimension (show 0 < dimension by omega))),
      booleanMassComplexity
          (CompositionBound.canonicalResourceFunction
            (fieldWidth_positive prefixWidth dimension (by omega))
            (fieldWidth_packingFits prefixWidth dimension (by omega))
            function member)
          groups <= (resourceBound : Nat)) :
    booleanMassComplexity (RuntimePipeline.requestFunction function)
        totalRequests <=
      (FiniteParameters.canonicalCostBound totalRequests groups prefixWidth
        dimension (fieldWidth prefixWidth dimension
          (show 0 < dimension by omega)) suffixWidth
        resourceBound : Nat) := by
  let dimensionPositive : 0 < dimension := by omega
  let width := fieldWidth prefixWidth dimension dimensionPositive
  have widthPositive := fieldWidth_positive prefixWidth dimension
    dimensionPositive
  have widthAtLeastTwo := fieldWidth_atLeastTwo prefixWidth dimension
    dimensionPositive
  have gridPositive := fieldWidth_gridPositive prefixWidth dimension
    dimensionPositive
  have packingFits := fieldWidth_packingFits prefixWidth dimension
    dimensionPositive
  apply FiniteParameters.booleanMassComplexity_le totalRequests groups
    prefixWidth dimension width suffixWidth widthPositive widthAtLeastTwo
    dimensionPositive gridPositive groupsPositive packingFits suffixLarge
    (directionCapacity_of_load totalRequests groups dimension width
      dimensionPositive widthPositive (by simpa only [width] using loadBound))
    function resourceBound
  intro member
  simpa only [width, proof_irrel_heq] using resourceComplexity member

end CodeParameters
end MassProduction
end Algebraic
