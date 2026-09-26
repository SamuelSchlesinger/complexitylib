/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Defs
public import Complexitylib.Classes.Containments.Internal.PSPACESubsetEXP

/-!
# `PSPACE ⊆ EXP`

⚠️ Unreviewed by Bolton

Polynomial space is contained in exponential time.

A machine using space `S(n)` has only `2^O(S(n))` configurations that respect its space bound, so
a deterministic run visits each at most once before halting: a repeat would make the run periodic
and pull an earlier halt, contradicting minimality. The halting time is therefore bounded by the
configuration count, and the *same machine* — no simulation is needed — decides the language in
exponential time.

The proof is in `Complexitylib.Classes.Containments.Internal.PSPACESubsetEXP`. Its one subtlety
is that `Cfg.WithinDecisionSpace` bounds head *positions* but says nothing about tape *contents*;
`Complexity.Windowed` (in `Internal.ConfigCount`) supplies the missing invariant — a head that
never leaves the window can never write outside it — which is what makes the configuration count
finite.

## Main results

- `TM.decidesInTime_of_decidesInSpace` — a space-`f` decider decides the same language within
  `TM.spaceTimeBound tm f` steps, with no change of machine
- `PSPACE_subset_EXP` — the containment
-/

@[expose] public section

namespace Complexity

/-- **A space-bounded decider is a time-bounded decider**, with no change of machine: if `tm`
decides `L` in space `f`, it decides `L` within `TM.spaceTimeBound tm f` steps, the number of
configurations inside its space window. The run halts before it could repeat a configuration. -/
theorem TM.decidesInTime_of_decidesInSpace {k : ℕ} {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L f) : tm.DecidesInTime L (TM.spaceTimeBound tm f) :=
  TM.decidesInTime_of_decidesInSpace_internal hdec

/-- **`PSPACE ⊆ EXP`**: a space-bounded machine halts within its configuration count. -/
theorem PSPACE_subset_EXP : PSPACE ⊆ EXP := PSPACE_subset_EXP_internal

end Complexity
