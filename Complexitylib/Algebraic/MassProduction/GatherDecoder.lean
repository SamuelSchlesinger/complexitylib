/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Arithmetic
public import Complexitylib.Algebraic.MassProduction.GatherRouting

/-!
# Fixed-wire line decoder

Gather places incidence `(request, scalar)` at its row-major record index.
The decoder therefore needs no compaction or dynamic lookup: for each request
it XORs the selected field-bit coordinate across all nonzero scalars.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace GatherDecoder

open GatherRouting
open IncidenceRouting
open LineEnumeration
open RoutingMetadata
open Sorting

/-- Physical gather-input wire holding one selected incidence value bit. -/
noncomputable def gatheredValueInputIndex
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (request : Fin totalRequests)
    (scalar : Fin (nonzeroScalarCount width))
    (bit : Fin valueWidth) :
    Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) :=
  Routing.recordBitIndex depth keyWidth (metadataWidth + valueWidth)
    (Fin.castLE destinationFits (finProdFinEquiv (request, scalar)))
    (valueBit keyWidth metadataWidth valueWidth bit)

/-- XOR expression for one request's selected field coordinate. -/
noncomputable def decoderExpression
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth)
    (request : Fin totalRequests) :
    Arithmetic.Expression Bool
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) :=
  DeMorgan.ArithmeticExpression.finSum (nonzeroScalarCount width) fun scalar =>
    .input (gatheredValueInputIndex destinationFits request scalar
      (selectedBit request))

/-- Gate count emitted by translating one request's XOR expression. -/
@[reducible] noncomputable def decoderGateCount
    (keyWidth metadataWidth : Nat)
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth)
    (request : Fin totalRequests) : Nat :=
  DeMorgan.arithmeticTranslation.compiledGateCount
    (decoderExpression (keyWidth := keyWidth)
      (metadataWidth := metadataWidth) destinationFits selectedBit
      request).circuit

/-- Complete row-major gather decoder. -/
noncomputable def circuit
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth) :
    Circuit DeMorgan.signature
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))
      (∑ request, decoderGateCount (keyWidth := keyWidth)
        (metadataWidth := metadataWidth) destinationFits selectedBit request)
      totalRequests :=
  Circuit.parallelFin totalRequests
    (decoderGateCount (keyWidth := keyWidth)
      (metadataWidth := metadataWidth) destinationFits selectedBit)
    (fun request => DeMorgan.ArithmeticExpression.circuit
      (decoderExpression (keyWidth := keyWidth)
        (metadataWidth := metadataWidth) destinationFits selectedBit request))

@[simp] theorem circuit_eval_apply
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (request : Fin totalRequests) :
    (circuit (keyWidth := keyWidth) (metadataWidth := metadataWidth)
      destinationFits selectedBit).eval DeMorgan.interpretation input
        request =
      ∑ scalar,
        recordValue input
          (Fin.castLE destinationFits
            (finProdFinEquiv (request, scalar)))
          (selectedBit request) := by
  rw [circuit, Circuit.eval_parallelFin,
    DeMorgan.ArithmeticExpression.circuit_eval]
  rw [decoderExpression, DeMorgan.ArithmeticExpression.finSum_eval]
  apply Finset.sum_congr rfl
  intro scalar _member
  rfl

theorem decoderExpression_cost
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth)
    (request : Fin totalRequests) :
    (DeMorgan.ArithmeticExpression.circuit
      (decoderExpression (keyWidth := keyWidth)
        (metadataWidth := metadataWidth) destinationFits selectedBit
        request)).cost
        DeMorgan.standardCost =
      nonzeroScalarCount width * 4 := by
  rw [DeMorgan.ArithmeticExpression.circuit_cost, decoderExpression,
    DeMorgan.ArithmeticExpression.finSum_weightedCost]
  simp [Arithmetic.Expression.weightedCost]

/-- The decoder ledger is linear in the number of incidences. -/
@[simp] theorem circuit_cost
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth) :
    (circuit (keyWidth := keyWidth) (metadataWidth := metadataWidth)
      destinationFits selectedBit).cost DeMorgan.standardCost =
      totalRequests * (nonzeroScalarCount width * 4) := by
  rw [circuit, Circuit.cost_parallelFin]
  simp only [decoderExpression_cost]
  simp

/-- Any fixed-wire incidence-value invariant immediately lifts to exact
per-request XOR recovery. -/
theorem circuit_recovers
    (destinationFits :
      totalRequests * nonzeroScalarCount width <= networkRecords depth)
    (selectedBit : Fin totalRequests -> Fin valueWidth)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (incidenceValue :
      Fin (totalRequests * nonzeroScalarCount width) ->
        Fin valueWidth -> Bool)
    (answer : Fin totalRequests -> Bool)
    (valuesCorrect : forall incidence,
      recordValue input (Fin.castLE destinationFits incidence) =
        incidenceValue incidence)
    (xorRecovers : forall request,
      (∑ scalar, incidenceValue (finProdFinEquiv (request, scalar))
        (selectedBit request)) = answer request) :
    (circuit (keyWidth := keyWidth) (metadataWidth := metadataWidth)
      destinationFits selectedBit).eval DeMorgan.interpretation input =
      answer := by
  funext request
  rw [circuit_eval_apply]
  apply (Finset.sum_congr rfl fun scalar _member => ?_).trans
    (xorRecovers request)
  exact congrFun (valuesCorrect (finProdFinEquiv (request, scalar)))
    (selectedBit request)

end GatherDecoder
end MassProduction
end Algebraic
