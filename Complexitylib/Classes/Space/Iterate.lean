/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.Pairing
import Complexitylib.Classes.Space.Iterate.Internal

/-!
# Polynomial-space iteration

`SpaceIter.mem_PSPACE_of_iterate` proves membership in `PSPACE` by iterating a
polynomial-time string function on polynomially bounded states. The number of
iterations may be exponential in a polynomial in the input length.

The initial state is `pair [] x`. Every positive iterate before `Nof x` has a
false head bit; iterate `Nof x` signals completion with a true head bit. One
more application produces a nonempty state whose head bit is the answer.
Both the initial state and this final answer state are included in the length
bound. The iteration count is a mathematical bound and need not itself be
computed by the step function.

This is the shared machine-independent entry point used by Savitch's theorem
and `IP ⊆ PSPACE`. The machine construction and its space accounting live in
`Complexitylib.Classes.Space.Iterate.Internal`.
-/

@[expose] public section

namespace Complexity.SpaceIter

/-- **Iterating a polynomial-time function on a polynomially bounded state is in
`PSPACE`**, however many iterations it takes. The function is applied to
`pair [] x` over and over; it signals completion by putting a `1` at the head of
its state, and the head of the state one application later is the answer. -/
theorem mem_PSPACE_of_iterate {L : Language} {G : List Bool → List Bool}
    (hG : G ∈ FP) (r w : Polynomial ℕ) (Nof : List Bool → ℕ)
    (hlen : ∀ (x : List Bool) (i : ℕ), i ≤ Nof x + 1 →
      (G^[i] (pair [] x)).length ≤ r.eval x.length)
    (hN1 : ∀ x : List Bool, 1 ≤ Nof x)
    (hNw : ∀ x : List Bool, Nof x ≤ 2 ^ w.eval x.length)
    (hcont : ∀ (x : List Bool) (i : ℕ), 0 < i → i < Nof x →
      (G^[i] (pair [] x)).headD false = false)
    (hdone : ∀ x : List Bool, (G^[Nof x] (pair [] x)).headD false = true)
    (hne : ∀ x : List Bool, G^[Nof x + 1] (pair [] x) ≠ [])
    (hans : ∀ x : List Bool, x ∈ L ↔ (G^[Nof x + 1] (pair [] x)).headD false = true) :
    L ∈ PSPACE :=
  mem_PSPACE_of_iterate_internal hG r w Nof hlen hN1 hNw hcont hdone hne hans

end Complexity.SpaceIter
