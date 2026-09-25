/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Foundations.Relation.RelatesInSteps
public import Complexitylib.Models.TuringMachine
public import Complexitylib.Interop.Cslib.Regular

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
  in linear time and zero auxiliary space by Complexitylib's finite-state
  scanner machine, so CSLib's closure properties and characterizations of
  regular languages yield complexity-class memberships. These results live in
  `Complexitylib.Interop.Cslib.Regular`, which this module re-exports.

## Main results

- `Complexity.TM.reachesIn_iff_relatesInSteps` — `reachesIn` is CSLib's
  `RelatesInSteps` for `TM.stepRel`
- `Complexity.mem_P_of_isRegular`, `Complexity.mem_L_of_isRegular` — regular
  languages are in `P` and in `L` (re-exported)
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

end Complexity
