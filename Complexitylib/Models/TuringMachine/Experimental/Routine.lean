/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.Routine.Defs
public import Complexitylib.Models.TuringMachine.Experimental.Routine.Internal

/-!
# Experimental first-order Turing-machine routines

This module exposes a small provisional authoring language for composing
concrete Turing machines. Routines lower definitionally through the established
`TM.seqTM` and `TM.forInputTM` combinators, while `Routine.TransducerSafe`
records only the one-way-output obligations of leaf calls. The namespace stays
experimental until a second independent construction validates the interface.

## Main definitions

- `TM.Experimental.Routine` — first-order call, sequence, and input-loop syntax.
- `TM.Experimental.Routine.lower` — structural lowering to the concrete `TM` model.
- `TM.Experimental.Routine.TransducerSafe` — structural output-safety certificate.

## Main result

- `TM.Experimental.Routine.TransducerSafe.lower_isTransducer` — certified routines
  lower to transducers.
-/

@[expose] public section

namespace Complexity

namespace TM

namespace Experimental

namespace Routine.TransducerSafe

/-- A transducer-safe routine lowers to a concrete machine satisfying the
one-way-output discipline. -/
theorem lower_isTransducer {routine : Routine n} (h : routine.TransducerSafe) :
    routine.lower.IsTransducer :=
  h.lower_isTransducer_internal

end Routine.TransducerSafe

end Experimental

end TM

end Complexity
