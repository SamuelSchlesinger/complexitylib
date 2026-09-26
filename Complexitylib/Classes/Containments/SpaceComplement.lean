/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.Containments.Internal.ComplementSpace

/-!
# Deterministic space classes are closed under complement

A deterministic space-bounded decider is turned into a decider for the complement by running it,
rewinding its output head to the verdict cell, and flipping the bit. The rewind only moves heads
leftward or off the left marker, so it costs one extra cell of space. The machine and its space
accounting are in `Complexitylib.Classes.Containments.Internal.ComplementSpace`.

## Main results

- `DSPACE_compl` — `DSPACE(S)` is closed under complement whenever the constant `1` is `O(S)`
- `PSPACE_compl` — `PSPACE` is closed under complement
-/

@[expose] public section

namespace Complexity

/-- **A space class with room for one more cell is closed under complement.** If `L ∈ DSPACE S`
and the constant function `1` is `O(S)`, then `Lᶜ ∈ DSPACE S`: the complement machine uses space
`S + 1`, and the extra cell is what the rewind to the verdict cell costs. -/
theorem DSPACE_compl {L : Language} {S : ℕ → ℕ} (hone : (fun _ => 1) =O S)
    (h : L ∈ DSPACE S) : Lᶜ ∈ DSPACE S :=
  DSPACE_compl_internal hone h

/-- **`PSPACE` is closed under complement.** The same machine runs, then rewinds its output head
to the verdict cell and flips the bit; the rewind only moves heads leftward or off the left
marker, so it costs one extra cell of space and no more. -/
theorem PSPACE_compl {L : Language} (h : L ∈ PSPACE) : Lᶜ ∈ PSPACE :=
  PSPACE_compl_internal h

end Complexity
