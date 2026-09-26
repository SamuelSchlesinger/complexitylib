/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH
public import Complexitylib.Classes.Containments
public import Complexitylib.Classes.Containments.Internal.ComplementSpace
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Window
public import Complexitylib.Classes.Containments.Internal.PolyWindow
public import Complexitylib.Classes.Containments.Internal.PHParts
public import Complexitylib.Classes.Containments.Internal.PHLayout
public import Complexitylib.Classes.Containments.Internal.PHMatrix
public import Complexitylib.Classes.Containments.Internal.PHEmit
public import Complexitylib.Classes.Containments.Internal.PHBody
public import Complexitylib.Classes.Containments.Internal.PHLoop
public import Complexitylib.Classes.Containments.Internal.PHEpilogue
public import Complexitylib.Classes.Containments.Internal.PHPrologue
public import Complexitylib.Classes.Containments.Internal.PHBodyWindow
public import Complexitylib.Classes.Containments.Internal.PHLoopWindow
public import Complexitylib.Classes.Containments.Internal.PHAssemble
public import Complexitylib.Classes.Containments.Internal.PHAssembleWindow
public import Complexitylib.Classes.Containments.Internal.PHBounds
public import Complexitylib.Classes.Containments.Internal.WitnessEnum

/-!
# `PH ⊆ PSPACE` — the induction on the level

⚠️ Unreviewed by Bolton

The hierarchy is built one quantifier at a time: `SigmaP 0 = P` and
`SigmaP (n+1) = polyExistsClass (complClass (SigmaP n))`. So an induction on the level reduces
the containment to two closure properties of `PSPACE`, and nothing else: closure under
complement, and closure under a polynomially bounded existential quantifier. The base case is
already available as `P_subset_PSPACE`.

Closure under complement is now proved — see
`Complexitylib.Classes.Containments.Internal.ComplementSpace` — so only the existential
quantifier is left, and `PH_subset_PSPACE_of_polyExists_internal` states the containment with
that as its single remaining hypothesis.

## The intended construction

The machine that will discharge the remaining hypothesis enumerates witnesses in a loop. Its
space accounting is supplied by
`Complexitylib.Models.TuringMachine.Combinators.Internal.Window`: `TM.KeepsWindow` is a space
discipline that survives re-entry, `TM.loopTM_keepsWindow` shows a loop inherits it from its body
and test — so a loop may run as long as it likes without its bound growing — and
`TM.decidesInSpace_of_keepsWindow` turns the result into a `DSPACE` membership.

The enumeration itself is a single loop. `mem_polyExistsLang_iff_count` replaces the two numeric
quantifiers by one counter below `2 ^ (p |x| + 1)`, a value denoting the witness `dropTop v` — its
canonical bits with the leading one removed. The machine never computes `dropTop`: it carries the
witness on a tape of its own and advances it in step with the counter, which `dropTop_succ` says
is the increment `bumpLE` — the ordinary binary increment, except that a carry off the end
*extends* the witness by a zero rather than writing a one. So the loop control is exactly the one
`NTM.ppMachine` already runs, and the witness tape is maintained by a variant of
`TM.binarySuccTM`.

The body can be assembled from existing subroutines rather than built from scratch. The one
apparent obstacle is that `TM.pairInputWorkTM` emits `pair w x`, taking its *second* component
from the real input, whereas `polyExistsLang` needs `pair x w`. Retargeting resolves it:
`TM.retargetInputStarted` makes a machine read its input off a work tape, so the emitter can be
pointed at the witness tape as its "input" while the copy of `x` — produced by
`TM.copyInputToOutputTM` under `TM.retargetOutput` — sits on the work tape it delimits. No new
emitter is required. The space cost of that relocation is accounted for by
`TM.retargetInput_keepsWindow_of_reaches`: what was the machine's free input tape becomes a
charged work tape, so the window it needs is its own budget plus the virtual input's length.
`TM.resetTapesTM` clears the scratch between iterations, which is what makes the body robust
enough for `TM.seqTM_keepsWindow_of_post`.

## Main results

- `PH_subset_PSPACE_of_enumerator_internal` — the containment, modulo one machine
- `SigmaP_subset_PSPACE_of_internal` — every level, modulo the two closure properties
- `PH_subset_PSPACE_of_internal` — the induction, modulo the two closure properties
- `PH_subset_PSPACE_of_polyExists_internal` — the containment, modulo the existential alone
- `mem_polyExistsLang_iff_numeric` — what the enumerating machine has to decide
- `mem_polyExistsLang_iff_count` — the same, as a single count over one counter
- `PH_subset_PSPACE_of_polyExistsLang_internal` — the containment, modulo one concrete
  language-level statement
- `PH_enumerator_exists` — the enumerating machine, with its window and its verdict
- `polyExistsClass_PSPACE_subset_PSPACE_internal` — closure of `PSPACE` under the bounded
  existential
- `PH_subset_PSPACE_internal` — the containment
-/

@[expose] public section

namespace Complexity

/-- Every level of the hierarchy is in `PSPACE`, granted the two closure properties. -/
theorem SigmaP_subset_PSPACE_of_internal
    (hcompl : ∀ L ∈ PSPACE, Lᶜ ∈ PSPACE)
    (hex : polyExistsClass PSPACE ⊆ PSPACE) :
    ∀ n, SigmaP n ⊆ PSPACE := by
  intro n
  induction n with
  | zero => exact P_subset_PSPACE
  | succ n ih =>
      refine (polyExistsClass_mono ?_).trans hex
      intro L hL
      have h : Lᶜ ∈ PSPACE := ih hL
      have h' : (Lᶜ)ᶜ ∈ PSPACE := hcompl _ h
      rwa [compl_compl] at h'

/-- **`PH ⊆ PSPACE`, modulo two closure properties of `PSPACE`.** The alternating prefix is
consumed one quantifier at a time; a complement flips the verdict and an existential is
evaluated by trying every witness in place. -/
theorem PH_subset_PSPACE_of_internal
    (hcompl : ∀ L ∈ PSPACE, Lᶜ ∈ PSPACE)
    (hex : polyExistsClass PSPACE ⊆ PSPACE) :
    PH ⊆ PSPACE := by
  intro L hL
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hL
  exact SigmaP_subset_PSPACE_of_internal hcompl hex n hn

/-- **`PH ⊆ PSPACE`, modulo a single closure property.** Closure under complement is proved, so
only the polynomially bounded existential quantifier remains. -/
theorem PH_subset_PSPACE_of_polyExists_internal (hex : polyExistsClass PSPACE ⊆ PSPACE) :
    PH ⊆ PSPACE :=
  PH_subset_PSPACE_of_internal (fun _ h => PSPACE_compl_internal h) hex

/-- **Membership in a bounded existential, as two numeric quantifiers.** This is the condition the
enumerating machine decides: iterate a witness length and a witness value, and test the pair. -/
theorem mem_polyExistsLang_iff_numeric (p : Polynomial ℕ) (L' : Language) (x : List Bool) :
    x ∈ polyExistsLang p L' ↔
      ∃ ℓ ≤ p.eval x.length, ∃ v < 2 ^ ℓ, pair x (bitsOfLen ℓ v) ∈ L' :=
  exists_bounded_iff _ _

/-- **Membership in a bounded existential, as a single count.** The two numeric quantifiers above
collapse to one: a counter below `2 ^ (p |x| + 1)` denotes a witness through `dropTop`, every
witness of the admitted lengths being denoted. This is the form the enumerating machine runs —
one loop over one register, the same shape as the path-counting machine of `PP ⊆ PSPACE`. -/
theorem mem_polyExistsLang_iff_count (p : Polynomial ℕ) (L' : Language) (x : List Bool) :
    x ∈ polyExistsLang p L' ↔
      ∃ v < 2 ^ (p.eval x.length + 1), pair x (dropTop v) ∈ L' :=
  exists_bounded_iff_count _ _

/-- The class-level closure reduces to a statement about one language construction. -/
theorem polyExistsClass_PSPACE_subset_PSPACE_of
    (h : ∀ (p : Polynomial ℕ) (L' : Language), L' ∈ PSPACE → polyExistsLang p L' ∈ PSPACE) :
    polyExistsClass PSPACE ⊆ PSPACE := by
  rintro L ⟨p, L', hL', rfl⟩
  exact h p L' hL'

/-- **`PH ⊆ PSPACE`, reduced to a single concrete obligation.** No class-level plumbing is left:
what remains is to exhibit, for one polynomial and one polynomially space-bounded language, a
machine deciding the bounded existential in polynomial space. Closure under complement is already
proved, and `mem_polyExistsLang_iff_numeric` says exactly what that machine has to decide. -/
theorem PH_subset_PSPACE_of_polyExistsLang_internal
    (h : ∀ (p : Polynomial ℕ) (L' : Language), L' ∈ PSPACE → polyExistsLang p L' ∈ PSPACE) :
    PH ⊆ PSPACE :=
  PH_subset_PSPACE_of_polyExists_internal (polyExistsClass_PSPACE_subset_PSPACE_of h)


/-- **The last obligation, spelled out at the machine level.** `PH ⊆ PSPACE` now follows from the
existence of one machine: for each polynomial `p` and each polynomially space-bounded `L'`, a
machine that keeps a polynomial window and decides the bounded existential — whose membership
condition is the two numeric quantifiers of `mem_polyExistsLang_iff_numeric`. -/
theorem PH_subset_PSPACE_of_enumerator_internal
    (h : ∀ (p : Polynomial ℕ) (L' : Language), L' ∈ PSPACE →
      ∃ (k : ℕ) (tm : TM k) (q : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k tm.Q), tm.reaches (tm.initCfg x) c' →
          c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
          (x ∈ polyExistsLang p L' → c'.output.cells 1 = Γ.one) ∧
          (x ∉ polyExistsLang p L' → c'.output.cells 1 = Γ.zero))) :
    PH ⊆ PSPACE := by
  refine PH_subset_PSPACE_of_polyExistsLang_internal fun p L' hL' => ?_
  obtain ⟨k, tm, q, hwin, hdec⟩ := h p L' hL'
  exact mem_PSPACE_of_polyWindow tm q hwin hdec

/-- **The enumerating machine exists.** For every polynomial `p` and every polynomially
space-bounded `L'`, the witness enumerator `PolyExists.enumTM` decides the bounded existential
`polyExistsLang p L'` and keeps a polynomial window while doing so. Its space bound is
independent of the loop's running time: the counter and the witness are the only things that
grow, and both stay below `p |x| + 1` bits. -/
theorem PH_enumerator_exists (p : Polynomial ℕ) (L' : Language) (hL' : L' ∈ PSPACE) :
    ∃ (k' : ℕ) (tm : TM k') (Q : Polynomial ℕ),
      (∀ (x : List Bool) (c' : Cfg k' tm.Q), tm.reaches (tm.initCfg x) c' →
        c'.WithinDecisionSpace x.length (Q.eval x.length)) ∧
      (∀ x : List Bool, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
        (x ∈ polyExistsLang p L' → c'.output.cells 1 = Γ.one) ∧
        (x ∉ polyExistsLang p L' → c'.output.cells 1 = Γ.zero)) := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hL'
  obtain ⟨k, M, f, hdecS, hf⟩ := hm
  obtain ⟨s, hs⟩ := BigO.pow_polynomial_bound hf
  have hdec : M.DecidesInTime L' (TM.spaceTimeBound M f) :=
    TM.decidesInTime_of_decidesInSpace_internal hdecS
  have hne : M.qstart ≠ M.qhalt := TM.qstart_ne_qhalt_of_decidesInTime M hdec
  refine ⟨PolyExists.enumTapes k, PolyExists.enumTM M p (PolyExists.bHPoly p s),
    PolyExists.bWPoly ((PolyExists.scratchTargets k).length) p s (PolyExists.bHPoly p s), ?_, ?_⟩
  · intro x c' hreach
    obtain ⟨bBody, bTest, hb1, hb2⟩ := PolyExists.exists_loop_bounds M f x L'
      (2 ^ (p.eval x.length + 1) - 1)
      (PolyExists.bH x.length (p.eval x.length)
        (s.eval (PolyExists.bP x.length (p.eval x.length))))
      (PolyExists.bB x.length (p.eval x.length))
      (PolyExists.bHb x.length (p.eval x.length)
        (s.eval (PolyExists.bP x.length (p.eval x.length))))
    exact PolyExists.enumTM_space M s hs hdecS hdec hne p x _ _ _ _ _ _ bBody bTest
      rfl rfl rfl rfl rfl (PolyExists.bWPoly_eval _ p s _ x.length) hb1 hb2 c' hreach
  · intro x
    obtain ⟨bBody, bTest, hb1, hb2⟩ := PolyExists.exists_loop_bounds M f x L'
      (2 ^ (p.eval x.length + 1) - 1)
      (PolyExists.bH x.length (p.eval x.length)
        (s.eval (PolyExists.bP x.length (p.eval x.length))))
      (PolyExists.bB x.length (p.eval x.length))
      (PolyExists.bHb x.length (p.eval x.length)
        (s.eval (PolyExists.bP x.length (p.eval x.length))))
    exact PolyExists.enumTM_decides M s hs hdecS hdec p x _ _ _ _ bBody bTest
      rfl rfl rfl rfl hb1 hb2

/-- **`PSPACE` is closed under polynomially bounded existential quantification.** The witness
enumerator of `PH_enumerator_exists` keeps a polynomial window and decides the bounded
existential, and `mem_PSPACE_of_polyWindow` turns that into `PSPACE` membership. -/
theorem polyExistsClass_PSPACE_subset_PSPACE_internal : polyExistsClass PSPACE ⊆ PSPACE :=
  polyExistsClass_PSPACE_subset_PSPACE_of fun p L' hL' => by
    obtain ⟨k, tm, q, hwin, hdec⟩ := PH_enumerator_exists p L' hL'
    exact mem_PSPACE_of_polyWindow tm q hwin hdec

/-- **`PH ⊆ PSPACE`.** The induction on the level leaves two closure properties of `PSPACE`;
complement is `PSPACE_compl`, and the bounded existential is discharged by the witness
enumerator of `PH_enumerator_exists`. -/
theorem PH_subset_PSPACE_internal : PH ⊆ PSPACE :=
  PH_subset_PSPACE_of_enumerator_internal PH_enumerator_exists

end Complexity
