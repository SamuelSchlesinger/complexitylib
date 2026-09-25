/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Foundations.Relation.RelatesInSteps
public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Computability.DFA
public import Complexitylib.Classes.Containments
import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner

/-!
# Interoperability with CSLib and Mathlib

CSLib builds its automata and regular-language theory on Mathlib's
`Language α := Set (List α)`. Complexitylib's `Complexity.Language` is
`Set (List Bool)`, which is definitionally Mathlib's `Language Bool`, so a
Complexitylib language can be passed to any CSLib or Mathlib statement about
binary languages, and conversely, with no conversion. (Mathlib's `Language`
is a separate definition with its own algebra, where `+` is union and `*` is
concatenation; Complexitylib keeps plain set operations.)

This module connects the two libraries' foundations:

- exact-time Turing-machine runs are CSLib's step-indexed `RelatesInSteps` for
  the one-step relation, so CSLib's generic run lemmas apply to them;
- every regular language, in the sense shared by Mathlib and CSLib, is decided
  in linear time by Complexitylib's finite-state scanner machine, so CSLib's
  closure properties of regular languages yield complexity-class memberships.

## Main results

- `Complexity.TM.reachesIn_iff_relatesInSteps` — `reachesIn` is CSLib's
  `RelatesInSteps` for `TM.stepRel`
- `Complexity.mem_DTIME_of_isRegular` — regular languages are in `DTIME(n + 2)`
- `Complexity.mem_P_of_isRegular` — regular languages are in `P`
- `Complexity.mem_P_of_nfa` — languages of CSLib's finite nondeterministic
  automata are in `P`

CSLib's closure properties of regular languages (union, concatenation, Kleene
star, reversal, inverse homomorphic images) combine with `mem_P_of_isRegular`
to give `P`-membership of the resulting languages directly.
-/


public section

namespace Complexity

/-- A run of exactly `t` steps is CSLib's `RelatesInSteps` for the one-step
relation. The two definitions build runs from opposite ends: `reachesIn` adds
steps at the front, `RelatesInSteps` at the back. -/
theorem TM.reachesIn_iff_relatesInSteps {n : ℕ} (tm : TM n) {t : ℕ}
    {c c' : Cfg n tm.Q} :
    tm.reachesIn t c c' ↔ Relation.RelatesInSteps tm.stepRel c c' t := by
  constructor
  · intro h
    induction h with
    | zero => exact .refl _
    | step hstep _ ih => exact .head _ _ _ _ hstep ih
  · intro h
    induction h with
    | refl => exact .zero
    | tail _ _ _ _ hstep ih => exact reachesIn_snoc ih hstep

/-- **Regular languages are decidable in linear time.** Every language that is
regular in the sense shared by Mathlib and CSLib (accepted by a finite
deterministic automaton) is decided in `n + 2` steps by the finite-state
scanner that runs the automaton. -/
theorem mem_DTIME_of_isRegular {L : Language} (hL : Language.IsRegular L) :
    L ∈ DTIME (fun n => n + 2) := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine ⟨0, TM.scannerTM M.start M.step
    (fun s => if decide (s ∈ M.accept) then .one else .zero),
    fun n => n + 2, ?_, BigO.refl _⟩
  exact TM.scannerTM_decidesInTime M.start M.step (fun s => decide (s ∈ M.accept))
    fun x => by
      rw [decide_eq_true_iff]
      exact Iff.rfl

/-- **Regular languages are in `P`.** -/
theorem mem_P_of_isRegular {L : Language} (hL : Language.IsRegular L) : L ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ (mem_DTIME_of_isRegular hL)⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

/-- **Finite nondeterministic automata decide in polynomial time.** Every
language accepted by a finite nondeterministic automaton from CSLib's automata
library is in `P`: CSLib's subset construction makes it regular, and the
scanner runs the resulting deterministic automaton. -/
theorem mem_P_of_nfa {State : Type} [Finite State]
    (nfa : Cslib.Automata.NA.FinAcc State Bool) :
    (Cslib.Automata.Acceptor.language nfa : Language) ∈ P :=
  mem_P_of_isRegular
    (Cslib.Language.IsRegular.iff_nfa.mpr ⟨State, inferInstance, nfa, rfl⟩)

end Complexity
