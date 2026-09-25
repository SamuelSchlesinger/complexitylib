/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseCircuit

/-!
# Correctness of a complete fixed-menu geometric phase

For encoded targets and occupancy, the circuit chooses one successful
candidate, preserves every original request as a permutation, carries its
complete generated point list, and returns a clean prefix. The menu-success
premise can be supplied by the universal phase-menu theorem.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GeometricPhase

open Sorting GeometricPhaseLayout
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- The complete phase preserves request data and point lists while selecting
the requested number of pairwise-disjoint, unoccupied recovery lines. -/
theorem circuit_correct (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords (menuDepth + requestDepth + width) + padding =
      networkRecords routingDepth)
    (neededPositive : 0 < needed) (neededFits : needed ≤ networkRecords requestDepth)
    (input : Fin inputs → Bool)
    (targets : Fin (networkRecords requestDepth) → Fin dimension → BinaryExtension width)
    (targetsCorrect : ∀ request bit, (targetWires request bit).eval input =
      binaryExtensionVectorBits positive (targets request) bit)
    (occupied : Finset (Fin dimension → BinaryExtension width))
    (occupiedCorrect : MenuPointLayout.occupied sourceKeys sourceFlags input =
      occupied.image (binaryExtensionVectorBits positive))
    (available : ∃ candidate, needed ≤ Nat.card {request : Fin (networkRecords requestDepth) //
      Clean (fun request direction => puncturedLine (targets request) direction)
        occupied (menu candidate) request})
    (distinct : Function.Injective (fun request => fun bit => (original request bit).eval input)) :
    ∃ candidate, ∃ order : Equiv.Perm (Fin (networkRecords requestDepth)),
      (∀ request bit, flatRecords
        ((circuit positive menu targetWires sourceKeys sourceFlags original recordCount neededPositive neededFits).eval
          DeMorgan.interpretation input) request
          (Fin.natAdd 1 (Fin.castAdd (2 ^ width * (dimension * width)) bit)) =
            (original (order request) bit).eval input) ∧
      (∀ request slot bit, flatRecords
        ((circuit positive menu targetWires sourceKeys sourceFlags original recordCount neededPositive neededFits).eval
          DeMorgan.interpretation input) request
          (Fin.natAdd 1 (Fin.natAdd requestWidth (finProdFinEquiv (slot, bit)))) =
            binaryExtensionVectorBits positive
              (PaddedLinePoints.point positive (targets (order request)) (menu candidate (order request)) slot) bit) ∧
      ∀ request : Fin (networkRecords requestDepth), request.val < needed →
        Clean (fun request direction => puncturedLine (targets request) direction)
          occupied (menu candidate) (order request) := by
  let generated := AffineMenuPoints.circuit positive menu targetWires
  let prepared := (PreparedInputs.circuit generated).eval DeMorgan.interpretation input
  let layout := PowerLayout.points menuDepth requestDepth width
  let valid := validWires positive menuDepth requestDepth inputs dimension
  let keys := keyWires menuDepth requestDepth inputs dimension width
  let liftedKeys := fun source bit => PreparedInputs.original
    (generatedBits menuDepth requestDepth dimension width) (sourceKeys source bit)
  let liftedFlags := fun source => PreparedInputs.original
    (generatedBits menuDepth requestDepth dimension width) (sourceFlags source)
  let payloads := payloadWires menuDepth dimension width original
  have cleanCorrect (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth)) :
      MenuSelection.RequestClean layout valid keys liftedKeys liftedFlags prepared candidate request ↔
        Clean (fun request direction => puncturedLine (targets request) direction)
          occupied (menu candidate) request :=
    requestClean_iff positive menu targetWires sourceKeys sourceFlags input targets targetsCorrect
      occupied occupiedCorrect candidate request
  have enough : ∃ candidate, needed ≤ Nat.card {request : Fin (networkRecords requestDepth) //
      MenuSelection.RequestClean layout valid keys liftedKeys liftedFlags prepared candidate request} := by
    obtain ⟨candidate, enough⟩ := available
    refine ⟨candidate, ?_⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight (cleanCorrect candidate))]
    exact enough
  have withinRequest : ∀ candidate request left right,
      (valid (layout (candidate, request, left))).eval prepared = true →
      (valid (layout (candidate, request, right))).eval prepared = true →
      (fun bit => (keys (layout (candidate, request, left)) bit).eval prepared) =
        (fun bit => (keys (layout (candidate, request, right)) bit).eval prepared) → left = right := by
    intro candidate request left right _ _ equal
    apply PaddedLinePoints.pointBits_injective positive (targets request) (menu candidate request)
    funext bit
    simpa only [keys, layout, prepared, generated,
      keyWires_eval positive menu targetWires input targets targetsCorrect] using congrFun equal bit
  have payloadDistinct : ∀ candidate, Function.Injective
      (fun request : Fin (networkRecords requestDepth) =>
        fun bit => (payloads (finProdFinEquiv (candidate, request)) bit).eval prepared) := by
    intro candidate left right equal
    apply distinct
    funext bit
    have sameBit := congrFun equal (Fin.castAdd (2 ^ width * (dimension * width)) bit)
    simpa only [payloads, prepared, payloadWires_original_eval] using sameBit
  obtain ⟨candidate, order, preserved, selected⟩ := MenuSelection.circuit_selects layout
    (PowerLayout.codes menuDepth) (PowerLayout.codes_injective menuDepth)
    valid keys liftedKeys liftedFlags recordCount payloads neededPositive neededFits prepared
    withinRequest enough payloadDistinct
  have saved (request : Fin (networkRecords requestDepth))
      (bit : Fin (requestWidth + 2 ^ width * (dimension * width))) :
      flatRecords
        ((circuit positive menu targetWires sourceKeys sourceFlags original recordCount neededPositive neededFits).eval
          DeMorgan.interpretation input) request (Fin.natAdd 1 bit) =
        (payloads (finProdFinEquiv (candidate, order request)) bit).eval prepared := by
    simpa only [circuit, Circuit.eval_comp, selector, generated, prepared, layout,
      valid, keys, liftedKeys, liftedFlags, payloads] using preserved request bit
  refine ⟨candidate, order, ?_, ?_, ?_⟩
  · intro request bit
    rw [saved]
    exact payloadWires_original_eval generated original input candidate (order request) bit
  · intro request slot bit
    rw [saved]
    change (payloadWires menuDepth dimension width original (finProdFinEquiv (candidate, order request))
      (Fin.natAdd requestWidth (finProdFinEquiv (slot, bit)))).eval prepared = _
    rw [payloadWires_point_eval]
    exact keyWires_eval positive menu targetWires input targets targetsCorrect candidate (order request) slot bit
  · intro request before
    exact (cleanCorrect candidate (order request)).mp (selected request before)

end Algebraic.MassProduction.Nonuniform.GeometricPhase
