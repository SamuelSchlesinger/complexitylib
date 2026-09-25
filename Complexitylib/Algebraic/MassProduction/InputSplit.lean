/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.RuntimePipeline
public import Complexitylib.Algebraic.MassProduction.Statement

/-!
# Splitting an arbitrary Boolean function into prefix and suffix inputs

The finite composition theorem accepts a function indexed by a numeric
`prefixWidth`-bit prefix and an ordinary Boolean suffix.  The headline theorem
instead quantifies over an arbitrary Boolean function on the concatenated
input block.  This module proves that the runtime prefix encoding used by the
circuit is exactly inverse to the corresponding semantic split.

All transports are explicit functions or equalities; no instances are
introduced.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace InputSplit

universe u

/-- Decode a bounded numeric prefix into the same little-endian Boolean bits
used by `RuntimePacking.source`. -/
def sourceBits
    (source : Fin (2 ^ prefixWidth)) : Fin prefixWidth -> Bool :=
  fun bit => finTwoEquiv ((finFunctionFinEquiv.symm source) bit)

@[simp] theorem sourceBits_runtimeSource
    (bits : Fin prefixWidth -> Bool) :
    sourceBits (RuntimePacking.source bits) = bits := by
  funext bit
  unfold sourceBits RuntimePacking.source FixedDivision.bitVectorIndex
  rw [Equiv.symm_apply_apply]
  cases bits bit <;> rfl

/-- Encoding the decoded bits of a bounded source returns that source. -/
@[simp] theorem runtimeSource_sourceBits
    (source : Fin (2 ^ prefixWidth)) :
    RuntimePacking.source (sourceBits source) = source := by
  unfold sourceBits RuntimePacking.source FixedDivision.bitVectorIndex
  have boolFin_eq : FixedDivision.boolFin = finTwoEquiv.symm := by
    funext bit
    cases bit <;> rfl
  rw [boolFin_eq]
  simp

/-- Concatenate the decoded prefix and the ordinary suffix. -/
def joinedInput
    (source : Fin (2 ^ prefixWidth))
    (suffix : Fin suffixWidth -> Bool) :
    Fin (prefixWidth + suffixWidth) -> Bool :=
  Fin.append (sourceBits source) suffix

/-- Semantic split of an arbitrary function on a concatenated input block. -/
def splitFunction
    (function : ScalarFunction Bool (prefixWidth + suffixWidth)) :
    Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool :=
  fun source suffix => function (joinedInput source suffix)

/-- Splitting a function and passing it through the runtime request interface
recovers the original function exactly. -/
@[simp] theorem requestFunction_splitFunction
    (function : ScalarFunction Bool (prefixWidth + suffixWidth)) :
    RuntimePipeline.requestFunction (splitFunction function) = function := by
  funext input
  apply congrArg function
  funext index
  refine Fin.addCases (motive := fun index =>
      joinedInput
          (RuntimePacking.source fun bit =>
            input (RuntimePipeline.requestPrefixInputIndex
              prefixWidth suffixWidth bit))
          (fun bit => input (RuntimePipeline.requestSuffixInputIndex
            prefixWidth suffixWidth bit)) index = input index)
    (fun prefixBit => ?_) (fun suffixBit => ?_) index
  · simp [joinedInput, RuntimePipeline.requestPrefixInputIndex]
  · simp [joinedInput, RuntimePipeline.requestSuffixInputIndex]

/-- The finite composition theorem therefore bounds the ordinary mass
complexity of every function on `prefixWidth + suffixWidth` inputs. -/
theorem booleanMassComplexity_requestFunction_splitFunction
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (copies : Nat) :
    booleanMassComplexity
        (RuntimePipeline.requestFunction (splitFunction function)) copies =
      booleanMassComplexity function copies := by
  rw [requestFunction_splitFunction]

/-! ## Zero-cost input transport -/

/-- Apply one input-index map independently in every row-major request
block. -/
def batchedInputMap
    (copies : Nat)
    (inputMap : Fin sourceWidth -> Fin targetWidth) :
    Fin (copies * sourceWidth) -> Fin (copies * targetWidth) :=
  fun input =>
    let location := finProdFinEquiv.symm input
    finProdFinEquiv (location.1, inputMap location.2)

theorem directProductInput_batchedInputMap
    (copies : Nat)
    (inputMap : Fin sourceWidth -> Fin targetWidth)
    (input : Fin (copies * targetWidth) -> U)
    (copy : Fin copies)
    (index : Fin sourceWidth) :
    directProductInput (input ∘ batchedInputMap copies inputMap) copy index =
      directProductInput input copy (inputMap index) := by
  simp [directProductInput, batchedInputMap]

/-- Reindexing the inputs of every copy commutes with direct product. -/
theorem directProduct_batchedInputMap
    (function : ScalarFunction U sourceWidth)
    (copies : Nat)
    (inputMap : Fin sourceWidth -> Fin targetWidth)
    (input : Fin (copies * targetWidth) -> U) :
    directProduct function copies
        (input ∘ batchedInputMap copies inputMap) =
      directProduct (fun block => function (block ∘ inputMap)) copies input := by
  funext copy
  unfold directProduct
  rw [show directProductInput
      (input ∘ batchedInputMap copies inputMap) copy =
        directProductInput input copy ∘ inputMap by
    funext index
    exact directProductInput_batchedInputMap
      copies inputMap input copy index]

/-- Rewiring source inputs cannot increase minimum circuit complexity. -/
theorem costComplexity_reindexInputs_le
    (interpretation : Interpretation σ U)
    (operationCost : OperationCost σ)
    (target : Target U sourceWidth outputs)
    (inputMap : Fin sourceWidth -> Fin targetWidth) :
    Circuit.costComplexity interpretation operationCost
        (fun input output => target (input ∘ inputMap) output) <=
      Circuit.costComplexity interpretation operationCost target := by
  apply Circuit.le_costComplexity
  intro circuit computes
  have mappedComputes :
      (circuit.mapInputs inputMap).ComputesWith interpretation
        (fun input output => target (input ∘ inputMap) output) := by
    intro input
    rw [Circuit.eval_mapInputs]
    exact computes (input ∘ inputMap)
  simpa using
    (circuit.mapInputs inputMap).costComplexity_le
      operationCost mappedComputes

/-- The scalar direct-product specialization of zero-cost input rewiring. -/
theorem booleanMassComplexity_reindexInputs_le
    (function : ScalarFunction Bool sourceWidth)
    (copies : Nat)
    (inputMap : Fin sourceWidth -> Fin targetWidth) :
    booleanMassComplexity
        (fun input => function (input ∘ inputMap)) copies <=
      booleanMassComplexity function copies := by
  unfold booleanMassComplexity
  let batchMap := batchedInputMap copies inputMap
  have bound := costComplexity_reindexInputs_le
    DeMorgan.interpretation DeMorgan.standardCost
    (directProduct function copies) batchMap
  have targetEquality :
      (fun input output =>
        directProduct function copies (input ∘ batchMap) output) =
        directProduct (fun input => function (input ∘ inputMap)) copies := by
    funext input output
    exact congrFun
      (directProduct_batchedInputMap function copies inputMap input) output
  rw [targetEquality] at bound
  exact bound

/-! ## Padding to a convenient larger block length -/

/-- Retraction from a padded input block to a nonempty original block.  Only
its behavior on the initial embedded block matters. -/
def paddingRetraction
    (sourcePositive : 0 < sourceWidth) : Fin targetWidth -> Fin sourceWidth :=
  fun input =>
    if inside : input.val < sourceWidth then
      ⟨input.val, inside⟩
    else
      ⟨0, sourcePositive⟩

@[simp] theorem paddingRetraction_castLE
    (sourcePositive : 0 < sourceWidth)
    (fits : sourceWidth <= targetWidth)
    (input : Fin sourceWidth) :
    paddingRetraction (targetWidth := targetWidth) sourcePositive
        (Fin.castLE fits input) = input := by
  apply Fin.ext
  simp [paddingRetraction, Fin.castLE, input.isLt]

/-- Extend a function to a larger input block by ignoring the padded tail. -/
def paddedFunction
    (fits : sourceWidth <= targetWidth)
    (function : ScalarFunction U sourceWidth) :
    ScalarFunction U targetWidth :=
  fun input => function (input ∘ Fin.castLE fits)

@[simp] theorem paddedFunction_retract
    (sourcePositive : 0 < sourceWidth)
    (fits : sourceWidth <= targetWidth)
    (function : ScalarFunction U sourceWidth)
    (input : Fin sourceWidth -> U) :
    paddedFunction fits function
        (input ∘ paddingRetraction (targetWidth := targetWidth)
          sourcePositive) = function input := by
  apply congrArg function
  funext index
  simp

/-- Padding unused tail variables cannot make the original Boolean direct
product cheaper: a circuit for the padded function rewires back at zero
cost. -/
theorem booleanMassComplexity_le_paddedFunction
    (sourcePositive : 0 < sourceWidth)
    (fits : sourceWidth <= targetWidth)
    (function : ScalarFunction Bool sourceWidth)
    (copies : Nat) :
    booleanMassComplexity function copies <=
      booleanMassComplexity (paddedFunction fits function) copies := by
  have bound := booleanMassComplexity_reindexInputs_le
    (paddedFunction fits function) copies
    (paddingRetraction (targetWidth := targetWidth) sourcePositive)
  simpa only [paddedFunction_retract] using bound

end InputSplit
end MassProduction
end Algebraic
