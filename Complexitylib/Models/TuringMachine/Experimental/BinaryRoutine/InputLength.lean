/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength.Internal

/-!
# Fresh-input entry for proof-carrying binary routines

This module packages the seam from a fresh Turing-machine configuration to a
canonical binary routine. The input is scanned once to obtain its length, and
the resulting routine inherits a total all-prefix `ComputesInSpace` contract.

## Main results

- `Sound.afterInputLength_hoareTimeSpace` gives the per-input composed contract.
- `Sound.afterInputLength_computesInSpace` packages the resulting function
  transducer.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

variable {n : ℕ}

/-- A sound routine with its unary input length loaded into one work value has
the expected fresh-start time-and-space contract. -/
theorem Sound.afterInputLength_hoareTimeSpace
    {routine : BinaryRoutine n} (hsound : routine.Sound)
    (lengthIdx : Fin n) (input : List Bool)
    (hrequires : routine.requires
      (inputLengthValues lengthIdx input.length)) :
    (afterInputLength lengthIdx routine).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.HasOutput
        (afterInputLengthFunction lengthIdx routine input))
      (afterInputLengthTime lengthIdx routine input.length) input.length
      (afterInputLengthSpace lengthIdx routine input.length) :=
  hsound.afterInputLength_hoareTimeSpace_internal lengthIdx input hrequires

/-- A sound routine whose pure precondition holds at every input length yields
a total function transducer with the composed all-prefix space bound. -/
theorem Sound.afterInputLength_computesInSpace
    {routine : BinaryRoutine n} (hsound : routine.Sound)
    (lengthIdx : Fin n)
    (hrequires : ∀ length,
      routine.requires (inputLengthValues lengthIdx length)) :
    (afterInputLength lengthIdx routine).ComputesInSpace
      (afterInputLengthFunction lengthIdx routine)
      (afterInputLengthSpace lengthIdx routine) :=
  hsound.afterInputLength_computesInSpace_internal lengthIdx hrequires

/-- A logarithmic bound for the routine phase, measured from the binary-length
counter's own budget, lifts to the complete fresh-input composition. -/
theorem afterInputLengthSpace_bigO_log
    (lengthIdx : Fin n) (routine : BinaryRoutine n)
    (hroutine : (fun length =>
      routine.spaceBound (TM.binaryLengthSpace length)
        (inputLengthValues lengthIdx length)) =O
          (fun length => Nat.log 2 length)) :
    afterInputLengthSpace lengthIdx routine =O
      (fun length => Nat.log 2 length) :=
  afterInputLengthSpace_bigO_log_internal lengthIdx routine hroutine

end BinaryRoutine

end Complexity
