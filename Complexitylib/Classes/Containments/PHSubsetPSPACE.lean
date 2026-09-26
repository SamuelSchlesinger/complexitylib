/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.Containments.SpaceComplement
public import Complexitylib.Classes.Containments.Internal.PHSubsetPSPACE

/-!
# `PH ⊆ PSPACE`

⚠️ Unreviewed by Bolton

The polynomial hierarchy is contained in polynomial space.

A language at level `Σ_k` is defined by `k` alternating polynomially bounded quantifiers over a
polynomial-time matrix. Polynomial space can evaluate the whole prefix directly: enumerate the
witness strings of each quantifier in turn, reusing the same tape for each, and combine the
results with the connective the quantifier calls for. Only one witness per level is stored at a
time, so the space used is the sum of the witness lengths — polynomial.

## Progress

The containment is proved — see `PH_subset_PSPACE`. The rest of this section records how.

The induction on the level is done. `PH_subset_PSPACE_of` below reduces the containment to two
closure properties of `PSPACE` and nothing else — closure under complement, and closure under a
polynomially bounded existential quantifier. The base case `P ⊆ PSPACE` is already available, and
neither remaining obligation mentions the hierarchy, so each can be attacked on its own.

One of the two is now proved. **`PSPACE` is closed under complement** (`PSPACE_compl`): the same
machine runs, then rewinds its output head to the verdict cell and flips the bit, and the rewind
only moves heads leftward or off the left marker, so it costs one extra cell and no more. The
delicate point is that the space predicate constrains *every* reachable configuration, not just
the final one; see `Complexitylib.Classes.Containments.Internal.ComplementSpace`.

The other is proved too. **`PSPACE` is closed under a polynomially bounded existential**: a
machine enumerates the witness strings of bounded length on a work tape, reusing that tape for
each, and runs the matrix machine on the pair — for which
`Complexitylib.Models.TuringMachine.Combinators.Apply` supplies work-tape-resident evaluation.
The counter and the witness advance together, so a single register below `p |x| + 1` bits drives
the whole enumeration, and the loop's running time — exponential — never enters the space
accounting. See `Complexitylib.Classes.Containments.Internal.PHBounds`.

## Main results

- `PSPACE_compl` — `PSPACE` is closed under complement
- `SigmaP_subset_PSPACE_of` — every level, granted the two closure properties
- `PH_subset_PSPACE_of` — the containment, granted the same two
- `PH_subset_PSPACE_of_polyExists` — the containment, granted the existential alone
- `mem_polyExistsLang_iff_numeric` — what the enumerating machine has to decide (two numeric
  quantifiers; no quantifier over witness strings survives)
- `PH_subset_PSPACE_of_polyExistsLang` — the containment, granted one concrete statement
- `PH_subset_PSPACE_of_enumerator` — the containment, granted one machine
- `polyExistsClass_PSPACE_subset_PSPACE` — `PSPACE` is closed under the bounded existential
- `PH_subset_PSPACE` — the containment

-/

@[expose] public section

namespace Complexity

/-- **`PH ⊆ PSPACE`**: the alternating quantifier prefix of a level of the hierarchy is
evaluated in place, one witness at a time. -/
def PHSubsetPSPACE : Prop := PH ⊆ PSPACE

/-- Every level of the hierarchy lies in `PSPACE`, granted that `PSPACE` is closed under
complement and under a polynomially bounded existential quantifier. -/
theorem SigmaP_subset_PSPACE_of
    (hcompl : ∀ L ∈ PSPACE, Lᶜ ∈ PSPACE)
    (hex : polyExistsClass PSPACE ⊆ PSPACE) :
    ∀ n, SigmaP n ⊆ PSPACE :=
  SigmaP_subset_PSPACE_of_internal hcompl hex

/-- **`PH ⊆ PSPACE`, reduced to two closure properties of `PSPACE`.** The alternating prefix is
consumed one quantifier at a time: a complement flips the verdict, and an existential is
evaluated by trying every witness in place. Neither hypothesis mentions the hierarchy. -/
theorem PH_subset_PSPACE_of
    (hcompl : ∀ L ∈ PSPACE, Lᶜ ∈ PSPACE)
    (hex : polyExistsClass PSPACE ⊆ PSPACE) :
    PH ⊆ PSPACE :=
  PH_subset_PSPACE_of_internal hcompl hex

/-- **`PH ⊆ PSPACE`, modulo a single closure property.** Closure under complement is proved
(`PSPACE_compl`), so evaluating a polynomially bounded existential in place is all that is left
between the library and the containment. -/
theorem PH_subset_PSPACE_of_polyExists (hex : polyExistsClass PSPACE ⊆ PSPACE) :
    PH ⊆ PSPACE :=
  PH_subset_PSPACE_of_polyExists_internal hex


/-- **`PH ⊆ PSPACE`, reduced to a single concrete obligation.** Closure under complement is
proved (`PSPACE_compl`), and the class-level plumbing is discharged; all that is left is to
decide one bounded existential in polynomial space, for one polynomial and one polynomially
space-bounded language. -/
theorem PH_subset_PSPACE_of_polyExistsLang
    (h : ∀ (p : Polynomial ℕ) (L' : Language), L' ∈ PSPACE → polyExistsLang p L' ∈ PSPACE) :
    PH ⊆ PSPACE :=
  PH_subset_PSPACE_of_polyExistsLang_internal h



/-- **`PH ⊆ PSPACE`, reduced to the existence of one machine.** For each polynomial `p` and each
polynomially space-bounded `L'`, exhibit a machine that keeps a polynomial window and decides the
bounded existential `polyExistsLang p L'`; the containment follows. Closure under complement is
already proved, and `mem_polyExistsLang_iff_numeric` states the membership condition that machine
must decide, as two numeric quantifiers over a witness length and value. -/
theorem PH_subset_PSPACE_of_enumerator
    (h : ∀ (p : Polynomial ℕ) (L' : Language), L' ∈ PSPACE →
      ∃ (k : ℕ) (tm : TM k) (q : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k tm.Q), tm.reaches (tm.initCfg x) c' →
          c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
          (x ∈ polyExistsLang p L' → c'.output.cells 1 = Γ.one) ∧
          (x ∉ polyExistsLang p L' → c'.output.cells 1 = Γ.zero))) :
    PH ⊆ PSPACE :=
  PH_subset_PSPACE_of_enumerator_internal h

/-- **`PSPACE` is closed under polynomially bounded existential quantification**: if
`L' ∈ PSPACE` and `p` is a polynomial, then `{x | ∃ w, |w| ≤ p(|x|) ∧ pair x w ∈ L'}` is in
`PSPACE`. A machine enumerates the candidate witnesses on one work tape, reusing it for each, and
runs the decider for `L'` on every pair. -/
theorem polyExistsClass_PSPACE_subset_PSPACE : polyExistsClass PSPACE ⊆ PSPACE :=
  polyExistsClass_PSPACE_subset_PSPACE_internal

/-- **`PH ⊆ PSPACE`**: every level of the polynomial hierarchy is decided in polynomial space.
The alternating prefix is consumed one quantifier at a time — a complement flips the verdict, and
an existential is evaluated by enumerating its witnesses in place, one at a time on a single work
tape. -/
theorem PH_subset_PSPACE : PH ⊆ PSPACE :=
  PH_subset_PSPACE_internal

end Complexity
