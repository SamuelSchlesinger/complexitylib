/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.LupanovParameters
public import Complexitylib.Algebraic.MassProduction.UhligTheorem

/-!
# Sharp Lupanov synthesis

This module packages the finite circuit and parameter bounds into a uniform
coefficient-one synthesis family, then feeds that explicit family into the
sharp Uhlig theorem.

All synthesis data is passed explicitly.  In particular, this module adds no
type-class instances.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace LupanovSynthesis

open ShannonSynthesis

/-! ## The coefficient-one synthesis family -/

/-- Uniform width-indexed form of the finite Lupanov circuit. -/
noncomputable def lupanovCircuit
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    Circuit DeMorgan.signature inputs
      (synthesisGateCount
        (reindexFunction (lupanovAddressDataSum inputs) function)
        (lupanovBlockSize inputs)) 1 :=
  (circuit
      (addressWidth := lupanovAddressWidth inputs)
      (dataWidth := lupanovDataWidth inputs)
      (reindexFunction (lupanovAddressDataSum inputs) function)
      (lupanovBlockSize inputs)).castCounts
    (lupanovAddressDataSum inputs) rfl rfl

@[simp] theorem lupanovCircuit_eval
    (inputs : Nat)
    (function : ScalarFunction Bool inputs)
    (input : Fin inputs -> Bool) :
    (lupanovCircuit inputs function).eval DeMorgan.interpretation input 0 =
      function input := by
  rw [lupanovCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, id_eq]
  rw [circuit_eval (lupanovBlockSize_positive inputs)]
  unfold reindexFunction
  apply congrArg function
  funext index
  simp [Function.comp_apply]

theorem lupanovCircuit_computes
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    (lupanovCircuit inputs function).ComputesWith DeMorgan.interpretation
      (scalarTarget function) := by
  intro input
  funext output
  have outputZero : output = 0 := Fin.eq_zero output
  subst output
  exact lupanovCircuit_eval inputs function input

theorem lupanovCircuit_cost_le
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    (lupanovCircuit inputs function).cost DeMorgan.standardCost <=
      costBound (lupanovAddressWidth inputs) (lupanovDataWidth inputs)
        (lupanovBlockSize inputs) := by
  rw [lupanovCircuit, Circuit.cost_castCounts]
  exact circuit_cost_le _ _

/-- Explicit one-copy synthesis data at every width. -/
noncomputable def lupanovScalarSynthesis
    (inputs : Nat) : ScalarSynthesis inputs where
  gateCount function :=
    synthesisGateCount
      (reindexFunction (lupanovAddressDataSum inputs) function)
      (lupanovBlockSize inputs)
  circuit := lupanovCircuit inputs
  computes := lupanovCircuit_computes inputs

/-- The Lupanov family as explicit dependent data, not a typeclass. -/
noncomputable def lupanovFamily : ScalarSynthesisFamily :=
  lupanovScalarSynthesis

@[simp] theorem lupanovFamily_circuit
    (inputs : Nat)
    (function : ScalarFunction Bool inputs) :
    (lupanovFamily inputs).circuit function =
      lupanovCircuit inputs function := rfl

/-- Lupanov's coefficient-one one-copy upper bound, in the exact integral
form consumed by the Uhlig recursion. -/
theorem lupanovFamily_hasSharpOneCopyCost :
    UhligTheorem.HasSharpOneCopyCost lupanovFamily := by
  intro precision precisionPositive
  let scaledPrecision := 4 * precision
  let logarithmicConstant := 11 * scaledPrecision + 1
  have parametersEventually := lupanov_parameters_eventually
  have removedEventually :=
    eventually_const_mul_log_le_self (5 * (scaledPrecision + 1))
  have polynomialEventually :=
    Growth.eventually_const_mul_pow_le_two_pow
      (4 * scaledPrecision) 4
  have sizeEventually :
      ∀ᶠ inputs in Filter.atTop,
        8 * logarithmicConstant <= inputs :=
    Filter.eventually_ge_atTop (8 * logarithmicConstant)
  have sharpEventually :
      ∀ᶠ inputs in Filter.atTop,
        forall function : ScalarFunction Bool inputs,
          precision *
                ((lupanovFamily inputs).circuit function).cost
                  DeMorgan.standardCost *
              inputs <=
            (precision + 1) * 2 ^ inputs := by
    filter_upwards [parametersEventually, removedEventually,
      polynomialEventually, sizeEventually] with inputs parameters
        removedBound polynomialBound sizeBound
    rintro function
    rcases parameters with
      ⟨fiveLogStrict, addressWidthIdentity, dataWidthIdentity,
        blockSizeIdentity⟩
    have inputsPositive : 0 < inputs := by omega
    have threeLogFits : 3 * Nat.log 2 inputs <= inputs := by omega
    have removedSmall :
        (scaledPrecision + 1) * (5 * Nat.log 2 inputs) <= inputs := by
      calc
        (scaledPrecision + 1) * (5 * Nat.log 2 inputs) =
            (5 * (scaledPrecision + 1)) * Nat.log 2 inputs := by ring
        _ <= inputs := removedBound
    have selectedCost := lupanovCircuit_cost_le inputs function
    conv_rhs at selectedCost =>
      rw [addressWidthIdentity, dataWidthIdentity, blockSizeIdentity]
    have constructionCost := selectedCost.trans
      (parameterCostBound_le inputs fiveLogStrict)
    let blocks := blockCount (3 * Nat.log 2 inputs)
      (inputs - 5 * Nat.log 2 inputs)
    let dataPower := 2 ^ (inputs - 3 * Nat.log 2 inputs)
    let mainTerm := blocks * dataPower
    have mainBound :
        scaledPrecision * inputs * mainTerm <=
          (scaledPrecision + 1) * 2 ^ inputs +
            (scaledPrecision + 1) * inputs * dataPower := by
      dsimp [mainTerm, blocks, dataPower]
      exact scaledMainTerm_le scaledPrecision inputs fiveLogStrict
        removedSmall
    have inputLeSquare : inputs <= inputs ^ 2 := by
      simpa only [pow_two] using
        Nat.le_mul_of_pos_left inputs inputsPositive
    have lowerOrderMerge :
        (scaledPrecision + 1) * inputs * dataPower +
            10 * scaledPrecision * inputs ^ 2 * dataPower <=
          (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
      calc
        (scaledPrecision + 1) * inputs * dataPower +
              10 * scaledPrecision * inputs ^ 2 * dataPower <=
            (scaledPrecision + 1) * inputs ^ 2 * dataPower +
              10 * scaledPrecision * inputs ^ 2 * dataPower := by
          gcongr
        _ = (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
          ring
    have scaledCost :
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
          (scaledPrecision + 1) * 2 ^ inputs +
            4 * scaledPrecision * inputs ^ 4 +
              (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
      calc
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
            scaledPrecision * inputs *
              (mainTerm + 4 * inputs ^ 3 +
                10 * inputs * dataPower) := by
          exact Nat.mul_le_mul_left (scaledPrecision * inputs) <| by
            simpa only [mainTerm, blocks, dataPower] using constructionCost
        _ = scaledPrecision * inputs * mainTerm +
              4 * scaledPrecision * inputs ^ 4 +
                10 * scaledPrecision * inputs ^ 2 * dataPower := by ring
        _ <= ((scaledPrecision + 1) * 2 ^ inputs +
              (scaledPrecision + 1) * inputs * dataPower) +
            4 * scaledPrecision * inputs ^ 4 +
              10 * scaledPrecision * inputs ^ 2 * dataPower := by
          gcongr
        _ = (scaledPrecision + 1) * 2 ^ inputs +
            4 * scaledPrecision * inputs ^ 4 +
              ((scaledPrecision + 1) * inputs * dataPower +
                10 * scaledPrecision * inputs ^ 2 * dataPower) := by ring
        _ <= (scaledPrecision + 1) * 2 ^ inputs +
            4 * scaledPrecision * inputs ^ 4 +
              (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower := by
          gcongr
    have logarithmicError :
        (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower <=
          2 ^ inputs := by
      dsimp [dataPower]
      exact const_mul_square_mul_two_pow_sub_three_log_le
        (11 * scaledPrecision + 1) inputs
        (by simpa only [logarithmicConstant] using sizeBound)
        threeLogFits
    have scaledTotal :
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
          (scaledPrecision + 3) * 2 ^ inputs := by
      calc
        scaledPrecision * inputs *
              (lupanovCircuit inputs function).cost
                DeMorgan.standardCost <=
            (scaledPrecision + 1) * 2 ^ inputs +
              4 * scaledPrecision * inputs ^ 4 +
                (11 * scaledPrecision + 1) * inputs ^ 2 * dataPower :=
          scaledCost
        _ <= (scaledPrecision + 1) * 2 ^ inputs +
            2 ^ inputs + 2 ^ inputs := by gcongr
        _ = (scaledPrecision + 3) * 2 ^ inputs := by ring
    apply le_of_mul_le_mul_left (a := 4) _ (by omega)
    calc
      4 * (precision *
              ((lupanovFamily inputs).circuit function).cost
                DeMorgan.standardCost * inputs) =
          scaledPrecision * inputs *
            (lupanovCircuit inputs function).cost
              DeMorgan.standardCost := by
        dsimp [scaledPrecision, lupanovFamily, lupanovScalarSynthesis]
        ring
      _ <= (scaledPrecision + 3) * 2 ^ inputs := scaledTotal
      _ <= 4 * ((precision + 1) * 2 ^ inputs) := by
        have coefficientBound :
            scaledPrecision + 3 <= 4 * (precision + 1) := by
          dsimp [scaledPrecision]
          omega
        calc
          (scaledPrecision + 3) * 2 ^ inputs <=
              (4 * (precision + 1)) * 2 ^ inputs :=
            Nat.mul_le_mul_right _ coefficientBound
          _ = 4 * ((precision + 1) * 2 ^ inputs) := by ring
  exact Filter.eventually_atTop.1 sharpEventually

/-!
The following is the unconditional sharp Uhlig theorem.  It combines the
coefficient-one Lupanov family above with the exact recursive two-copy circuit
from `UhligRecursion`.  Its discrete `IsUhligDepth` premise is precisely the
denominator-free form of `depth(n) = o(n / log n)`, so it covers every batch
size `1 <= t <= 2 ^ depth(n)` with asymptotic leading coefficient one.
-/
theorem uhlig_massProduction
    (depth : Nat -> Nat)
    (depthSmall : UhligTheorem.IsUhligDepth depth) :
    UhligTheorem.HasSharpMassProduction depth :=
  UhligTheorem.uhlig_of_sharp_one_copy lupanovFamily
    lupanovFamily_hasSharpOneCopyCost depth depthSmall

end LupanovSynthesis
end MassProduction
end Algebraic
