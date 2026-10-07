/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Defs
public import Mathlib.Computability.DFA

/-!
# Validating a finite Mathlib machine's input

A DFA scans the binary input without changing it. Accepted inputs are rewound
and passed to the source machine. Rejected inputs halt at the first blank, so
their complete right-of-head output is empty.
-/

@[expose] public section

namespace Complexity.MathlibTM0.BinaryMachine

/-- Control for input validation, rewinding, and source execution. -/
inductive GuardState (σ Q : Type) where
  /-- Scan the input using a DFA state. -/
  | scan : σ → GuardState σ Q
  /-- Return to the blank preceding the input. -/
  | rewind
  /-- Execute a source state. -/
  | run : Q → GuardState σ Q
  deriving Fintype

/-- A DFA check followed by the original machine on accepted inputs. -/
noncomputable abbrev guarded (M : BinaryMachine) {σ : Type} [Fintype σ]
    (D : DFA Bool σ) : BinaryMachine := by
  classical
  exact {
    Alphabet := M.Alphabet
    State := GuardState σ M.State
    stateInhabited := ⟨.scan D.start⟩
    bit := M.bit
    readBit := M.readBit
    readBit_bit := M.readBit_bit
    readBit_blank := M.readBit_blank
    code := fun q a => match q with
      | .scan q => match M.readBit a with
          | some b => some (.scan (D.step q b), .move .right)
          | none => if q ∈ D.accept then some (.rewind, .move .left) else none
      | .rewind => match M.readBit a with
          | some _ => some (.rewind, .move .left)
          | none => some (.run default, .move .right)
      | .run q => (M.code q a).map fun (q', a') => (.run q', a') }

end Complexity.MathlibTM0.BinaryMachine
