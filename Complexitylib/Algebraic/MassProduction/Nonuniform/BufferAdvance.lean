/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferInput
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PreparedInputs

/-!
# Free buffer compaction after a geometric phase

Preserve previously completed records, append the accepted prefix with its
full point lists, and retain only original request data for the pending
suffix. These operations are all fixed wiring; the phase is charged once.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferAdvance

open BufferInput

/-- Literal position of an accepted prefix record. -/
def acceptedIndex (split : accepted + remaining = pending) (index : Fin accepted) : Fin pending :=
  Fin.castLE (by omega : accepted ≤ pending) index

/-- Literal position of a record in the remaining suffix. -/
def pendingIndex (split : accepted + remaining = pending) (index : Fin remaining) : Fin pending :=
  ⟨accepted + index.val, by omega⟩

/-- Prefix positions are distinct. -/
theorem acceptedIndex_injective (split : accepted + remaining = (pending : Nat)) :
    Function.Injective (acceptedIndex split) := by
  intro left right equal
  have values := congrArg (fun index : Fin pending => index.val) equal
  exact Fin.ext values

/-- Suffix positions are distinct. -/
theorem pendingIndex_injective (split : accepted + remaining = (pending : Nat)) :
    Function.Injective (pendingIndex split) := by
  intro left right equal
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg (fun index : Fin pending => index.val) equal)

/-- Preserve old completed records and append the newly accepted point lists. -/
def completedWires (completed requestWidth slots keyWidth : Nat)
    (split : accepted + remaining = pending) (record : Fin (completed + accepted))
    (bit : Fin (storedWidth requestWidth slots keyWidth)) :
    DeMorgan.Wiring
      (pending * (1 + storedWidth requestWidth slots keyWidth) +
        inputWidth completed pending requestWidth slots keyWidth) :=
  Fin.addCases
    (fun old => PreparedInputs.original (pending * (1 + storedWidth requestWidth slots keyWidth))
      (completedWire pending old bit))
    (fun fresh => PreparedInputs.output (inputWidth completed pending requestWidth slots keyWidth)
      (finProdFinEquiv (acceptedIndex split fresh, Fin.natAdd 1 bit))) record

/-- Keep the pending suffix's original request data and discard its unused point lists. -/
def pendingWires (completed requestWidth slots keyWidth : Nat)
    (split : accepted + remaining = pending) (record : Fin remaining) (bit : Fin requestWidth) :
    DeMorgan.Wiring
      (pending * (1 + storedWidth requestWidth slots keyWidth) +
        inputWidth completed pending requestWidth slots keyWidth) :=
  PreparedInputs.output (inputWidth completed pending requestWidth slots keyWidth)
    (finProdFinEquiv (pendingIndex split record, Fin.natAdd 1 (Fin.castAdd (slots * keyWidth) bit)))

/-- The complete fixed wiring for the next scheduler buffer. -/
def wiring (completed requestWidth slots keyWidth : Nat) (split : accepted + remaining = (pending : Nat)) :=
  encode (completedWires completed requestWidth slots keyWidth split)
    (pendingWires completed requestWidth slots keyWidth split)

/-- Run the phase once and compact its results into the next buffer. -/
def circuit
    (phase : Circuit DeMorgan.signature (inputWidth completed pending requestWidth slots keyWidth) gates
      (pending * (1 + storedWidth requestWidth slots keyWidth)))
    (split : accepted + remaining = pending) :=
  (DeMorgan.Wiring.circuit (wiring completed requestWidth slots keyWidth split)).comp
    (PreparedInputs.circuit phase)

/-- Exact semantics of buffer compaction: old records, accepted point lists,
and the pending original-data suffix all appear at their fixed positions. -/
theorem circuit_eval
    (phase : Circuit DeMorgan.signature (inputWidth completed pending requestWidth slots keyWidth) gates
      (pending * (1 + storedWidth requestWidth slots keyWidth)))
    (split : accepted + remaining = pending)
    (completedRecords : Fin completed → Fin (storedWidth requestWidth slots keyWidth) → Bool)
    (pendingRecords : Fin pending → Fin requestWidth → Bool) :
    let input := encode completedRecords pendingRecords
    let output := phase.eval DeMorgan.interpretation input
    (circuit phase split).eval DeMorgan.interpretation input =
      encode
        (Fin.append completedRecords
          (fun fresh bit => output (finProdFinEquiv (acceptedIndex split fresh, Fin.natAdd 1 bit))))
        (fun waiting bit => output
          (finProdFinEquiv (pendingIndex split waiting, Fin.natAdd 1 (Fin.castAdd (slots * keyWidth) bit)))) := by
  dsimp only
  rw [circuit, Circuit.eval_comp, DeMorgan.Wiring.circuit_eval, wiring, map_encode]
  congr 1
  · funext record bit
    refine Fin.addCases (fun old => ?_) (fun fresh => ?_) record
    · simp only [completedWires, Fin.addCases_left, PreparedInputs.original_eval,
        completedWire_eval, Fin.append_left]
    · simp only [completedWires, Fin.addCases_right, PreparedInputs.output_eval, Fin.append_right]
  · funext record bit
    exact PreparedInputs.output_eval phase _ _

/-- Buffer compaction adds no charged gates. -/
theorem circuit_cost
    (phase : Circuit DeMorgan.signature (inputWidth completed pending requestWidth slots keyWidth) gates
      (pending * (1 + storedWidth requestWidth slots keyWidth)))
    (split : accepted + remaining = pending) :
    (circuit phase split).cost DeMorgan.standardCost = phase.cost DeMorgan.standardCost := by
  rw [circuit, Circuit.cost_comp, DeMorgan.Wiring.circuit_cost, PreparedInputs.circuit_cost, Nat.add_zero]

end Algebraic.MassProduction.Nonuniform.BufferAdvance
