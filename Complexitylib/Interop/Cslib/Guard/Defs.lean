/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Computability.DFA
public import Mathlib.Tactic.DeriveFintype

/-!
# A regular-domain guard for binary CSLib machines

The guard scans the read-only input with a DFA. Rejection halts with empty
output. Acceptance rewinds the input and starts the original machine with
untouched work tapes and output.
-/

@[expose] public section

namespace Complexity.CslibGuard

/-- Validation, rewind, and source execution control. -/
inductive State (σ Q : Type) where
  /-- Scan using the current DFA state. -/
  | scan : σ → State σ Q
  /-- Return to the left input boundary. -/
  | rewind
  /-- Execute the source machine. -/
  | run : Q → State σ Q
  deriving Fintype

/-- Change control and input position without changing work tapes or output. -/
def idle {k : ℕ} {σ Q : Type} (q : Option (State σ Q)) (move : SignType) :
    Turing.Action k Bool (State σ Q) where
  state := q
  inputTape := move
  output := none
  workTapes := fun _ => (none, 0)

/-- Validate a regular input format before executing a binary CSLib machine. -/
noncomputable def machine {k : ℕ} {σ Q : Type}
    (M : Turing.MultiTapeTM k Bool Q) (D : DFA Bool σ) :
    Turing.MultiTapeTM k Bool (State σ Q) := by
  classical
  exact {
    q₀ := .scan D.start
    tr := fun q input work => match q with
      | .scan q => match input with
        | some b => idle (some (.scan (D.step q b))) 1
        | none => if q ∈ D.accept then idle (some .rewind) (-1) else idle none 0
      | .rewind => match input with
        | some _ => idle (some .rewind) (-1)
        | none => idle (some (.run M.q₀)) 1
      | .run q =>
          let a := M.tr q input work
          { a with state := a.state.map State.run } }

end Complexity.CslibGuard
