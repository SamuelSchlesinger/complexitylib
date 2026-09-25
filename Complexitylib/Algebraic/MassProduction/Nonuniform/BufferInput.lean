/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Wiring

/-!
# Input layout for a halving scheduler buffer

Completed records contain original request data and a complete point list.
Pending records contain original request data only. All phase inputs are
free selections from this buffer; scalar-validity flags are fixed constants.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferInput

/-- Width of a completed request together with its stored point list. -/
abbrev storedWidth (requestWidth slots keyWidth : Nat) : Nat := requestWidth + slots * keyWidth

/-- Completed records followed by pending request records. -/
abbrev inputWidth (completed pending requestWidth slots keyWidth : Nat) : Nat :=
  completed * storedWidth requestWidth slots keyWidth + pending * requestWidth

/-- Flatten the two record arrays into the buffer input. -/
def encode
    (completedRecords : Fin completed → Fin (storedWidth requestWidth slots keyWidth) → Value)
    (pendingRecords : Fin pending → Fin requestWidth → Value) :
    Fin (inputWidth completed pending requestWidth slots keyWidth) → Value :=
  Fin.append
    (fun bit => let pair := finProdFinEquiv.symm bit; completedRecords pair.1 pair.2)
    (fun bit => let pair := finProdFinEquiv.symm bit; pendingRecords pair.1 pair.2)

/-- Applying a function to a buffer acts independently on its stored fields. -/
theorem map_encode (f : Value → Result)
    (completedRecords : Fin completed → Fin (storedWidth requestWidth slots keyWidth) → Value)
    (pendingRecords : Fin pending → Fin requestWidth → Value) :
    (fun bit => f (encode completedRecords pendingRecords bit)) =
      encode (fun record bit => f (completedRecords record bit))
        (fun record bit => f (pendingRecords record bit)) := by
  funext bit
  refine Fin.addCases (fun completedBit => ?_) (fun pendingBit => ?_) bit
  · simp only [encode, Fin.append_left]
  · simp only [encode, Fin.append_right]

/-- One bit of an already completed record. -/
def completedWire (pending : Nat) (record : Fin completed)
    (bit : Fin (storedWidth requestWidth slots keyWidth)) :
    DeMorgan.Wiring (inputWidth completed pending requestWidth slots keyWidth) :=
  .input (Fin.castAdd (pending * requestWidth) (finProdFinEquiv (record, bit)))

/-- One bit of a pending request's original data. -/
def pendingWire (completed slots keyWidth : Nat) (record : Fin pending) (bit : Fin requestWidth) :
    DeMorgan.Wiring (inputWidth completed pending requestWidth slots keyWidth) :=
  .input (Fin.natAdd (completed * storedWidth requestWidth slots keyWidth) (finProdFinEquiv (record, bit)))

/-- A stored occupied-point address, with source records flattened by request and slot. -/
def pointWire (pending requestWidth : Nat) (source : Fin (completed * slots)) (bit : Fin keyWidth) :
    DeMorgan.Wiring (inputWidth completed pending requestWidth slots keyWidth) :=
  let pair := (finProdFinEquiv (m := completed) (n := slots)).symm source
  completedWire pending pair.1 (Fin.natAdd requestWidth (finProdFinEquiv (pair.2, bit)))

/-- Scalar-validity flags are repeated for every stored completed request. -/
def flagWire (inputs : Nat) (valid : Fin slots → Bool) (source : Fin (completed * slots)) :
    DeMorgan.Wiring inputs :=
  .constant (valid ((finProdFinEquiv (m := completed) (n := slots)).symm source).2)

/-- Reading a completed record recovers its exact stored bit. -/
theorem completedWire_eval
    (completedRecords : Fin completed → Fin (storedWidth requestWidth slots keyWidth) → Bool)
    (pendingRecords : Fin pending → Fin requestWidth → Bool)
    (record : Fin completed) (bit : Fin (storedWidth requestWidth slots keyWidth)) :
    (completedWire pending record bit).eval (encode completedRecords pendingRecords) = completedRecords record bit := by
  simp only [completedWire, DeMorgan.Wiring.eval_input, encode, Fin.append_left, Equiv.symm_apply_apply]

/-- Reading a pending record recovers its exact original request bit. -/
theorem pendingWire_eval
    (completedRecords : Fin completed → Fin (storedWidth requestWidth slots keyWidth) → Bool)
    (pendingRecords : Fin pending → Fin requestWidth → Bool)
    (record : Fin pending) (bit : Fin requestWidth) :
    (pendingWire completed slots keyWidth record bit).eval (encode completedRecords pendingRecords) =
      pendingRecords record bit := by
  simp only [pendingWire, DeMorgan.Wiring.eval_input, encode, Fin.append_right, Equiv.symm_apply_apply]

/-- Each occupied-point query uses the stored point-list suffix. -/
theorem pointWire_eval
    (completedRecords : Fin completed → Fin (storedWidth requestWidth slots keyWidth) → Bool)
    (pendingRecords : Fin pending → Fin requestWidth → Bool)
    (record : Fin completed) (slot : Fin slots) (bit : Fin keyWidth) :
    (pointWire pending requestWidth (finProdFinEquiv (record, slot)) bit).eval
      (encode completedRecords pendingRecords) =
        completedRecords record (Fin.natAdd requestWidth (finProdFinEquiv (slot, bit))) := by
  simp only [pointWire, Equiv.symm_apply_apply, completedWire_eval]

/-- Repeated validity flags depend only on the scalar slot. -/
theorem flagWire_eval (valid : Fin slots → Bool) (input : Fin inputs → Bool)
    (record : Fin completed) (slot : Fin slots) :
    (flagWire inputs valid (finProdFinEquiv (record, slot))).eval input = valid slot := by
  simp only [flagWire, Equiv.symm_apply_apply, DeMorgan.Wiring.eval_constant]

end Algebraic.MassProduction.Nonuniform.BufferInput
