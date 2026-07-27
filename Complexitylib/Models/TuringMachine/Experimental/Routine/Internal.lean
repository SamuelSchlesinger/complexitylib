/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Combinators.ForInput
public import Complexitylib.Models.TuringMachine.Experimental.Routine.Defs
public import Complexitylib.Models.TuringMachine.Hoare.Space

/-!
# Experimental first-order Turing-machine routines — proof internals

This module proves that the structural `Routine.TransducerSafe` certificate is
preserved by lowering through sequential composition and read-only-input loops.
-/

@[expose] public section

namespace Complexity

namespace TM

namespace Experimental

namespace Routine.TransducerSafe

/-- Lowering a transducer-safe routine produces a concrete one-way-output
transducer. -/
theorem lower_isTransducer_internal {routine : Routine n}
    (h : routine.TransducerSafe) : routine.lower.IsTransducer := by
  induction h with
  | call hmachine => exact hmachine
  | seq _ _ hfirst hsecond => exact hfirst.seqTM hsecond
  | forInput _ hbody => exact hbody.forInputTM

end Routine.TransducerSafe

end Experimental

end TM

end Complexity
