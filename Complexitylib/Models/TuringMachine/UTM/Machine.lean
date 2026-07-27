/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.UTM.Internal.Init
public import Complexitylib.Models.TuringMachine.UTM.Internal.Body
public import Complexitylib.Models.TuringMachine.UTM.Internal.HaltTest
public import Complexitylib.Models.TuringMachine.UTM.Internal.Extract

/-!
# The universal Turing machine

`utmTM` — a single, fixed six-work-tape machine. On input `pair α x` it
simulates the single-work-tape machine `(decodeDesc α).toTM` on input `x`:

* `initTM` parses the input — the description `α` is translated onto the
  desc tape, `x` onto the (+1-shifted) virtual input tape, and the start
  state onto the state tape;
* the loop alternates `bodyTM` (one simulated step: first-match table scan
  and application) with `haltTestTM` (compare the state tape against the
  description's halt field, reporting the verdict on the output tape);
* `extractTM` copies the virtual output tape to the real output tape.

Its specification is the interpreter `TMDesc.toTM` (`UTM/Interp.lean`);
the simulation and time-bound theorems are assembled in `UTM/Sim.lean`
from the phase Hoare triples.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- **The universal Turing machine**: initialization, then the
    simulate-one-step / test-halt loop, then output extraction. -/
def utmTM : TM 6 :=
  seqTM initTM (seqTM (loopTM UTMBody.bodyTM haltTestTM) extractTM)

end TM

end Complexity
