/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.IPSubsetPSPACE
public import Complexitylib.Classes.Interactive
public import Complexitylib.Classes.P.Defs

/-!
# `PSPACE ⊆ IP`

⚠️ Unreviewed by Bolton

Shamir's theorem, the hard half of `IP = PSPACE`.

Take a `PSPACE`-complete problem — validity of a quantified Boolean formula — and arithmetize it:
replace the Boolean connectives by polynomial operations over a finite field, so that the formula's
truth value becomes the value of an iterated sum and product. The prover then convinces the
verifier of that value by the sum-check protocol, one variable at a time, with a degree-reduction
step interleaved to keep the intermediate polynomials small.

## What the proof needs

- A `PSPACE`-complete problem and the reduction to it — `Complexitylib.SAT.QBF` has the syntax.
- Arithmetization over a finite field, and the sum-check protocol with its soundness bound.
- The interactive machinery of `Complexitylib.Classes.Interactive` to package the protocol.

## TODO

- Prove it.
-/

@[expose] public section

namespace Complexity

/-- **`PSPACE ⊆ IP`** (Shamir): arithmetize a quantified Boolean formula and run sum-check. -/
def PSPACESubsetIP : Prop := PSPACE ⊆ IP

/-- The two halves together are Shamir's theorem; the first is `IP_subset_PSPACE`. -/
theorem IP_eq_PSPACE_of (h' : PSPACESubsetIP) : IP = PSPACE :=
  subset_antisymm IP_subset_PSPACE (h' : PSPACE ⊆ IP)

end Complexity
