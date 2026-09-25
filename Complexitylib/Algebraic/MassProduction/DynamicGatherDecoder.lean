/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.GatherDecoder

/-!
# Runtime-selected gather decoder

The fixed decoder chooses one field coordinate nonuniformly for every request.
For the actual direct-product circuit that coordinate comes from the runtime
prefix.  This module appends a one-hot coordinate selector to the gather
output and compiles the bilinear XOR

`XOR_(scalar, bit) selector(request, bit) AND value(request, scalar, bit)`.

Thus the selected coordinate remains runtime data, while the cost stays
linear in the number of gathered field bits.  No type-class instances are
introduced.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace DynamicGatherDecoder

open GatherDecoder
open GatherRouting
open IncidenceRouting
open LineEnumeration
open RoutingMetadata
open Sorting

/-- Number of one-hot selector bits appended after the gather records. -/
@[reducible] def selectorBitCount
    (totalRequests valueWidth : Nat) : Nat :=
  totalRequests * valueWidth

/-- Full input width: gather records followed by row-major selector bits. -/
@[reducible] def inputCount
    (depth keyWidth metadataWidth valueWidth totalRequests : Nat) : Nat :=
  networkBits depth (recordWidth keyWidth metadataWidth valueWidth) +
    selectorBitCount totalRequests valueWidth

/-- A gathered value wire, embedded in the left part of the decoder input. -/
noncomputable def gatheredInputIndex
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (request : Fin totalRequests)
    (scalar : Fin (nonzeroScalarCount width))
    (bit : Fin valueWidth) :
    Fin (inputCount depth keyWidth metadataWidth valueWidth totalRequests) :=
  Fin.castAdd (selectorBitCount totalRequests valueWidth)
    (gatheredValueInputIndex (keyWidth := keyWidth)
      (metadataWidth := metadataWidth) destinationFits request scalar bit)

/-- A row-major selector wire, embedded in the right part of the input. -/
def selectorInputIndex
    (depth keyWidth metadataWidth : Nat)
    (request : Fin totalRequests)
    (bit : Fin valueWidth) :
    Fin (inputCount depth keyWidth metadataWidth valueWidth totalRequests) :=
  Fin.natAdd
    (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))
    (finProdFinEquiv (request, bit))

/-- Restrict the combined input to its gather-record prefix. -/
def gatherInput
    (input : Fin (inputCount depth keyWidth metadataWidth valueWidth
      totalRequests) -> Bool) :
    Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool :=
  fun index => input (Fin.castAdd
    (selectorBitCount totalRequests valueWidth) index)

/-- Read one request's runtime one-hot selector bit. -/
def selectorInput
    (input : Fin (inputCount depth keyWidth metadataWidth valueWidth
      totalRequests) -> Bool)
    (request : Fin totalRequests)
    (bit : Fin valueWidth) : Bool :=
  input (selectorInputIndex depth keyWidth metadataWidth request bit)

@[simp] theorem gatherInput_append
    (gather : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (selectors : Fin (selectorBitCount totalRequests valueWidth) -> Bool) :
    gatherInput (Fin.append gather selectors) = gather := by
  funext index
  simp [gatherInput]

@[simp] theorem selectorInput_append
    (gather : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (selectors : Fin (selectorBitCount totalRequests valueWidth) -> Bool)
    (request : Fin totalRequests)
    (bit : Fin valueWidth) :
    selectorInput (Fin.append gather selectors) request bit =
      selectors (finProdFinEquiv (request, bit)) := by
  simp [selectorInput, selectorInputIndex]

/-- Bilinear decoding expression for one request. -/
noncomputable def decoderExpression
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (request : Fin totalRequests) :
    Arithmetic.Expression Bool
      (inputCount depth keyWidth metadataWidth valueWidth totalRequests) :=
  DeMorgan.ArithmeticExpression.finSum
      (nonzeroScalarCount width * valueWidth) fun flat =>
    let scalarAndBit :=
      (finProdFinEquiv
        (m := nonzeroScalarCount width) (n := valueWidth)).symm flat
    .mul
      (.input (selectorInputIndex depth keyWidth metadataWidth
        request scalarAndBit.2))
      (.input (gatheredInputIndex (keyWidth := keyWidth)
        (metadataWidth := metadataWidth) destinationFits request
        scalarAndBit.1 scalarAndBit.2))

/-- Gate count produced for one request. -/
@[reducible] noncomputable def decoderGateCount
    (keyWidth metadataWidth valueWidth : Nat)
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (request : Fin totalRequests) : Nat :=
  DeMorgan.arithmeticTranslation.compiledGateCount
    (decoderExpression (keyWidth := keyWidth)
      (metadataWidth := metadataWidth) (valueWidth := valueWidth)
      destinationFits request).circuit

/-- Complete runtime-selected row-major gather decoder. -/
noncomputable def circuit
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth) :
    Circuit DeMorgan.signature
      (inputCount depth keyWidth metadataWidth valueWidth totalRequests)
      (∑ request, decoderGateCount keyWidth metadataWidth valueWidth
        destinationFits request)
      totalRequests :=
  Circuit.parallelFin totalRequests
    (decoderGateCount keyWidth metadataWidth valueWidth destinationFits)
    (fun request => DeMorgan.ArithmeticExpression.circuit
      (decoderExpression (keyWidth := keyWidth)
        (metadataWidth := metadataWidth) (valueWidth := valueWidth)
        destinationFits request))

@[simp] theorem circuit_eval_apply
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (input : Fin (inputCount depth keyWidth metadataWidth valueWidth
      totalRequests) -> Bool)
    (request : Fin totalRequests) :
    (circuit (keyWidth := keyWidth) (metadataWidth := metadataWidth)
      (valueWidth := valueWidth) destinationFits).eval
        DeMorgan.interpretation input request =
      ∑ flat : Fin (nonzeroScalarCount width * valueWidth),
        let scalarAndBit :=
          (finProdFinEquiv
            (m := nonzeroScalarCount width) (n := valueWidth)).symm flat
        selectorInput input request scalarAndBit.2 *
          recordValue (gatherInput input)
            (Fin.castLE destinationFits
              (finProdFinEquiv (request, scalarAndBit.1)))
            scalarAndBit.2 := by
  rw [circuit, Circuit.eval_parallelFin,
    DeMorgan.ArithmeticExpression.circuit_eval]
  rw [decoderExpression, DeMorgan.ArithmeticExpression.finSum_eval]
  apply Finset.sum_congr rfl
  intro flat _member
  rfl

/-- Exact De Morgan cost of one request's bilinear decoder. -/
theorem decoderExpression_cost
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (request : Fin totalRequests) :
    (DeMorgan.ArithmeticExpression.circuit
      (decoderExpression (keyWidth := keyWidth)
        (metadataWidth := metadataWidth) (valueWidth := valueWidth)
        destinationFits request)).cost
        DeMorgan.standardCost =
      nonzeroScalarCount width * valueWidth * 5 := by
  rw [DeMorgan.ArithmeticExpression.circuit_cost, decoderExpression,
    DeMorgan.ArithmeticExpression.finSum_weightedCost]
  simp [Arithmetic.Expression.weightedCost]
  omega

/-- The full runtime decoder remains linear in the gathered field bits. -/
@[simp] theorem circuit_cost
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth) :
    (circuit (keyWidth := keyWidth) (metadataWidth := metadataWidth)
      (valueWidth := valueWidth) destinationFits).cost
        DeMorgan.standardCost =
      totalRequests * (nonzeroScalarCount width * valueWidth * 5) := by
  rw [circuit, Circuit.cost_parallelFin]
  simp only [decoderExpression_cost]
  simp

/-- A one-hot runtime selector reduces the bilinear decoder to the same
coordinate XOR used by the fixed decoder. -/
theorem circuit_recovers
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth)
    (input : Fin (inputCount depth keyWidth metadataWidth valueWidth
      totalRequests) -> Bool)
    (incidenceValue :
      Fin (totalRequests * nonzeroScalarCount width) ->
        Fin valueWidth -> Bool)
    (answer : Fin totalRequests -> Bool)
    (valuesCorrect : forall incidence,
      recordValue (gatherInput input)
          (Fin.castLE destinationFits incidence) =
        incidenceValue incidence)
    (selectorCorrect : forall request bit,
      selectorInput input request bit = decide (bit = selectedBit request))
    (xorRecovers : forall request,
      (∑ scalar, incidenceValue (finProdFinEquiv (request, scalar))
        (selectedBit request)) = answer request) :
    (circuit (keyWidth := keyWidth) (metadataWidth := metadataWidth)
      (valueWidth := valueWidth) destinationFits).eval
        DeMorgan.interpretation input = answer := by
  funext request
  rw [circuit_eval_apply]
  let pairEquiv :=
    (finProdFinEquiv
      (m := nonzeroScalarCount width) (n := valueWidth)).symm
  let term : Fin (nonzeroScalarCount width) × Fin valueWidth -> Bool :=
    fun scalarAndBit =>
      selectorInput input request scalarAndBit.2 *
        recordValue (gatherInput input)
          (Fin.castLE destinationFits
            (finProdFinEquiv (request, scalarAndBit.1)))
          scalarAndBit.2
  change (∑ flat, term (pairEquiv flat)) = answer request
  rw [pairEquiv.sum_comp term]
  dsimp only [term]
  rw [Fintype.sum_prod_type]
  simp_rw [selectorCorrect]
  simp_rw [valuesCorrect]
  apply (Finset.sum_congr rfl fun scalar _member => ?_).trans
    (xorRecovers request)
  classical
  calc
    (∑ bit, decide (bit = selectedBit request) *
        incidenceValue (finProdFinEquiv (request, scalar)) bit) =
        decide (selectedBit request = selectedBit request) *
          incidenceValue (finProdFinEquiv (request, scalar))
            (selectedBit request) := by
      apply Finset.sum_eq_single (selectedBit request)
      · intro bit _member bitNe
        simp [bitNe, Bool.mul_eq_and]
        exact Bool.zero_eq_false
      · simp
    _ = incidenceValue (finProdFinEquiv (request, scalar))
          (selectedBit request) := by simp [Bool.mul_eq_and]

/-- Appending a one-hot runtime selector makes the dynamic decoder
extensionally equal to the corresponding fixed-coordinate decoder. -/
theorem circuit_eval_append_oneHot
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth)
    (gather : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    (circuit (keyWidth := keyWidth) (metadataWidth := metadataWidth)
      (valueWidth := valueWidth) destinationFits).eval
        DeMorgan.interpretation
        (Fin.append gather fun flat =>
          let requestAndBit :=
            (finProdFinEquiv
              (m := totalRequests) (n := valueWidth)).symm flat
          decide (requestAndBit.2 = selectedBit requestAndBit.1)) =
      (GatherDecoder.circuit (keyWidth := keyWidth)
        (metadataWidth := metadataWidth) destinationFits selectedBit).eval
          DeMorgan.interpretation gather := by
  let selectors : Fin (selectorBitCount totalRequests valueWidth) -> Bool :=
    fun flat =>
      let requestAndBit :=
        (finProdFinEquiv
          (m := totalRequests) (n := valueWidth)).symm flat
      decide (requestAndBit.2 = selectedBit requestAndBit.1)
  apply circuit_recovers destinationFits selectedBit
    (Fin.append gather selectors)
    (fun incidence bit =>
      recordValue gather (Fin.castLE destinationFits incidence) bit)
    ((GatherDecoder.circuit (keyWidth := keyWidth)
      (metadataWidth := metadataWidth) destinationFits selectedBit).eval
        DeMorgan.interpretation gather)
  · intro incidence
    rw [gatherInput_append]
  · intro request bit
    rw [selectorInput_append]
    change decide
        (((finProdFinEquiv
          (m := totalRequests) (n := valueWidth)).symm
            (finProdFinEquiv (request, bit))).2 =
          selectedBit
            ((finProdFinEquiv
              (m := totalRequests) (n := valueWidth)).symm
                (finProdFinEquiv (request, bit))).1) =
      decide (bit = selectedBit request)
    rw [Equiv.symm_apply_apply]
  · intro request
    exact (GatherDecoder.circuit_eval_apply destinationFits selectedBit
      gather request).symm

end DynamicGatherDecoder
end MassProduction
end Algebraic
