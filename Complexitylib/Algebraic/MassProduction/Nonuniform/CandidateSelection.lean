/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.FlagSelection
public import Complexitylib.Algebraic.Basis.DeMorgan.Wiring

/-!
# Selecting a successful candidate and its clean prefix

Each candidate consists of flagged request records. First sort the request
records of every candidate by their flags. A candidate succeeds precisely
when its last required prefix position is flagged. Then sort whole candidate
blocks by this success bit and select the first block by free wiring.

The carried candidate blocks may be large, but the outer comparison key is
only one bit. The total cost remains linear in the candidate-request product
apart from record widths and squared sorting depths.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.CandidateSelection

open scoped BigOperators
open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Bit length of one candidate's request array. -/
abbrev rowBits (requestDepth payloadWidth : Nat) := networkBits requestDepth (1 + payloadWidth)

/-- One candidate's row in the flat input array. -/
def row
    (input : Fin (networkRecords menuDepth * rowBits requestDepth payloadWidth) → Bool)
    (candidate : Fin (networkRecords menuDepth)) :
    Fin (rowBits requestDepth payloadWidth) → Bool :=
  fun bit => input (finProdFinEquiv (candidate, bit))

/-- Sort each candidate's requests with clean records first. -/
def rowsCircuit (menuDepth requestDepth payloadWidth : Nat) :=
  Circuit.parallelFinVector (networkRecords menuDepth) (rowBits requestDepth payloadWidth)
    (fun _ => bitonicSortGateCount (by omega : 1 ≤ 1 + payloadWidth) requestDepth)
    (fun candidate => (FlagSelection.circuit requestDepth payloadWidth).mapInputs
      (fun bit => finProdFinEquiv (candidate, bit)))

/-- Each output row is exactly its independent flag sort. -/
theorem rowsCircuit_eval
    (input : Fin (networkRecords menuDepth * rowBits requestDepth payloadWidth) → Bool)
    (candidate : Fin (networkRecords menuDepth)) :
    row ((rowsCircuit menuDepth requestDepth payloadWidth).eval DeMorgan.interpretation input)
      candidate =
      (FlagSelection.circuit requestDepth payloadWidth).eval DeMorgan.interpretation
        (row input candidate) := by
  funext bit
  rw [row, rowsCircuit, Circuit.eval_parallelFinVector, Circuit.eval_mapInputs]
  rfl

/-- The final position in the required clean prefix. -/
def thresholdIndex (requestDepth payloadWidth needed : Nat)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :
    Fin (rowBits requestDepth payloadWidth) :=
  finProdFinEquiv ((⟨needed - 1, by omega⟩ : Fin (networkRecords requestDepth)),
    (⟨0, by omega⟩ : Fin (1 + payloadWidth)))

/-- Add each candidate's success bit before its complete sorted row. -/
def packWiring (menuDepth requestDepth payloadWidth needed : Nat)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth)
    (output : Fin (networkBits menuDepth (1 + rowBits requestDepth payloadWidth))) :
    DeMorgan.Wiring (networkRecords menuDepth * rowBits requestDepth payloadWidth) :=
  let pair := (finProdFinEquiv
    (m := networkRecords menuDepth) (n := 1 + rowBits requestDepth payloadWidth)).symm output
  .input (finProdFinEquiv (pair.1,
    Fin.addCases (fun _ : Fin 1 => thresholdIndex requestDepth payloadWidth needed positive fits)
      (fun bit => bit) pair.2))

/-- Packing preserves the row and prefixes its selected threshold flag. -/
theorem packWiring_eval
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth)
    (input : Fin (networkRecords menuDepth * rowBits requestDepth payloadWidth) → Bool)
    (candidate : Fin (networkRecords menuDepth))
    (bit : Fin (1 + rowBits requestDepth payloadWidth)) :
    (packWiring menuDepth requestDepth payloadWidth needed positive fits
      (finProdFinEquiv (candidate, bit))).eval input =
      Fin.append (fun _ : Fin 1 => FlagSelection.flag (row input candidate)
        ⟨needed - 1, by omega⟩) (row input candidate) bit := by
  simp only [packWiring, Equiv.symm_apply_apply, DeMorgan.Wiring.eval_input]
  refine Fin.addCases (fun headerBit => ?_) (fun rowBit => ?_) bit
  · rw [Fin.addCases_left, Fin.append_left]
    rfl
  · rw [Fin.addCases_right, Fin.append_right]
    rfl

/-- The complete selection circuit returns the first sorted candidate block. -/
def circuit (menuDepth requestDepth payloadWidth needed : Nat)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :=
  (((FlagSelection.circuit menuDepth (rowBits requestDepth payloadWidth)).comp
    (DeMorgan.Wiring.circuit (packWiring menuDepth requestDepth payloadWidth needed positive fits))).comp
    (rowsCircuit menuDepth requestDepth payloadWidth)).mapOutputs
      (fun bit => finProdFinEquiv
        ((⟨0, by simp⟩ : Fin (networkRecords menuDepth)), Fin.natAdd 1 bit))

/-- If any candidate has enough clean requests, the selected complete row
comes from one candidate and all required prefix positions are clean. -/
theorem circuit_selects
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth)
    (input : Fin (networkRecords menuDepth * rowBits requestDepth payloadWidth) → Bool)
    (available : ∃ candidate, needed ≤
      Nat.card {request : Fin (networkRecords requestDepth) //
        FlagSelection.flag (row input candidate) request = true}) :
    ∃ candidate,
      (circuit menuDepth requestDepth payloadWidth needed positive fits).eval
          DeMorgan.interpretation input =
        (FlagSelection.circuit requestDepth payloadWidth).eval
          DeMorgan.interpretation (row input candidate) ∧
      ∀ request : Fin (networkRecords requestDepth), request.val < needed →
        FlagSelection.flag
          ((circuit menuDepth requestDepth payloadWidth needed positive fits).eval
            DeMorgan.interpretation input) request = true := by
  let sortedRows := (rowsCircuit menuDepth requestDepth payloadWidth).eval
    DeMorgan.interpretation input
  let packed := fun bit =>
    (packWiring menuDepth requestDepth payloadWidth needed positive fits bit).eval sortedRows
  have packedRecord (candidate : Fin (networkRecords menuDepth)) :
      flatRecords packed candidate =
        Fin.append (fun _ : Fin 1 => FlagSelection.flag (row sortedRows candidate)
          ⟨needed - 1, by omega⟩) (row sortedRows candidate) := by
    funext bit
    exact packWiring_eval positive fits sortedRows candidate bit
  have packedFlag (candidate : Fin (networkRecords menuDepth)) :
      FlagSelection.flag packed candidate =
        FlagSelection.flag (row sortedRows candidate) ⟨needed - 1, by omega⟩ := by
    change flatRecords packed candidate (Fin.castAdd (rowBits requestDepth payloadWidth) 0) = _
    rw [packedRecord, Fin.append_left]
  have packedAvailable : ∃ candidate, FlagSelection.flag packed candidate = true := by
    obtain ⟨candidate, enough⟩ := available
    refine ⟨candidate, ?_⟩
    rw [packedFlag, rowsCircuit_eval]
    exact FlagSelection.circuit_selects (row input candidate) needed enough
      ⟨needed - 1, by omega⟩ (by change needed - 1 < needed; omega)
  obtain ⟨candidate, candidateFlag, sameRecord⟩ :=
    FlagSelection.circuit_firstFlagged packed packedAvailable
  have outputRow :
      (circuit menuDepth requestDepth payloadWidth needed positive fits).eval
          DeMorgan.interpretation input = row sortedRows candidate := by
    funext bit
    rw [circuit, Circuit.eval_mapOutputs, Circuit.eval_comp, Circuit.eval_comp,
      DeMorgan.Wiring.circuit_eval]
    have sameBit := congrFun sameRecord (Fin.natAdd 1 bit)
    rw [packedRecord, Fin.append_right] at sameBit
    exact sameBit
  refine ⟨candidate, outputRow.trans (rowsCircuit_eval input candidate), ?_⟩
  intro request selected
  rw [outputRow, rowsCircuit_eval]
  rw [packedFlag, rowsCircuit_eval] at candidateFlag
  have ordered := FlagSelection.circuit_flagsAntitone (row input candidate)
    (show request ≤ (⟨needed - 1, by omega⟩ : Fin (networkRecords requestDepth)) by
      exact Nat.le_sub_one_of_lt selected)
  rw [candidateFlag] at ordered
  cases flagValue : FlagSelection.flag
      ((FlagSelection.circuit requestDepth payloadWidth).eval DeMorgan.interpretation
        (row input candidate)) request with
  | false =>
      rw [flagValue] at ordered
      exact False.elim ((by decide : ¬ (true : Bool) ≤ false) ordered)
  | true => rfl

/-- Explicit cost for inner request sorts and the outer candidate-block sort. -/
theorem circuit_cost_le
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :
    (circuit menuDepth requestDepth payloadWidth needed positive fits).cost DeMorgan.standardCost ≤
      networkRecords menuDepth *
        (48 * requestDepth * requestDepth * networkRecords requestDepth * (1 + payloadWidth)) +
      48 * menuDepth * menuDepth * networkRecords menuDepth *
        (1 + rowBits requestDepth payloadWidth) := by
  rw [circuit, Circuit.cost_mapOutputs, Circuit.cost_comp, Circuit.cost_comp,
    DeMorgan.Wiring.circuit_cost, Nat.zero_add, rowsCircuit, Circuit.cost_parallelFinVector]
  apply Nat.add_le_add _ FlagSelection.circuit_cost_le
  calc
    _ ≤ ∑ _candidate : Fin (networkRecords menuDepth),
        48 * requestDepth * requestDepth * networkRecords requestDepth * (1 + payloadWidth) := by
      apply Finset.sum_le_sum
      intro candidate _
      rw [Circuit.cost_mapInputs]
      exact FlagSelection.circuit_cost_le
    _ = _ := by simp

end Algebraic.MassProduction.Nonuniform.CandidateSelection
