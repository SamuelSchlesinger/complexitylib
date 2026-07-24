/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control.Defs
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control.Internal

/-!
# Proof-carrying binary routine control

This module exposes a canonical zero branch and a reusable count-up-loop
adapter for `BinaryRoutine`. The loop accepts arbitrary starting counters,
requests body obligations only along the reachable segment, and treats body
times as upper bounds rather than falsely claiming exact runtimes.

Its auxiliary-space bound is width-sensitive: comparison space and every
reachable body-plus-successor budget are maximized rather than accumulated.
Thus many iterations can retain logarithmic auxiliary space.

## Main results

- `BinaryRoutine.Sound.branchZero` verifies canonical zero/nonzero dispatch.
- `BinaryRoutine.Sound.binaryFor` verifies bounded count-up iteration.
- `TM.BinaryForSegmentSpec.reachesIn` composes a bounded reachable segment.
- `TM.BinaryForSegmentSpaceSpec.prefix_withinAuxSpace` covers all prefixes.
-/

namespace Complexity

namespace BinaryRoutine

variable {n : ℕ}

/-- Canonical binary zero branching preserves routine soundness. -/
theorem Sound.branchZero {onZero onPositive : BinaryRoutine n}
    (hzero : onZero.Sound) (hpositive : onPositive.Sound) (idx : Fin n) :
    (branchZero idx onZero onPositive).Sound :=
  hzero.branchZero_internal hpositive idx

/-- A sound body yields a sound canonical count-up loop when the routine
domain supplies the reachable body obligations and controller preservation. -/
theorem Sound.binaryFor {body : BinaryRoutine n} (hbody : body.Sound)
    (counterIdx limitIdx : Fin n) :
    (binaryFor body counterIdx limitIdx).Sound :=
  hbody.binaryFor_internal counterIdx limitIdx

end BinaryRoutine

end Complexity
