/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength.Defs

/-!
# Fresh-input entry for proof-carrying binary routines -- definitions

This module connects the initial Turing-machine configuration to the canonical
binary work-vector discipline. It first counts the unary input length into one
designated work tape, then runs a proof-carrying binary routine.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

/-- The canonical all-zero work vector with one designated value set to the
input length. -/
def inputLengthValues (lengthIdx : Fin n) (length : ℕ) : BinaryValues n :=
  Function.update (fun _ => 0) lengthIdx length

/-- Count the input length in binary, then enter a proof-carrying routine. -/
def afterInputLength (lengthIdx : Fin n) (routine : BinaryRoutine n) : TM n :=
  TM.seqTM (TM.binaryLengthTM lengthIdx) routine.machine

/-- Compositional runtime bound for fresh-input routine entry. -/
def afterInputLengthTime (lengthIdx : Fin n) (routine : BinaryRoutine n)
    (length : ℕ) : ℕ :=
  TM.binaryLengthTime length + 1 +
    routine.timeBound (inputLengthValues lengthIdx length)

/-- All-prefix auxiliary-space bound for fresh-input routine entry. -/
def afterInputLengthSpace (lengthIdx : Fin n) (routine : BinaryRoutine n)
    (length : ℕ) : ℕ :=
  max (TM.binaryLengthSpace length)
    (routine.spaceBound (TM.binaryLengthSpace length)
      (inputLengthValues lengthIdx length))

/-- Function emitted by a fresh-input routine. Only the unary input length is
observable after entry into the binary routine layer. -/
def afterInputLengthFunction (lengthIdx : Fin n) (routine : BinaryRoutine n) :
    List Bool → List Bool :=
  fun input => routine.emitted (inputLengthValues lengthIdx input.length)

end BinaryRoutine

end Complexity
