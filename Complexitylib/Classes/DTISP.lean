/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.Space

/-!
# Simultaneous time-space complexity classes

This file defines the simultaneous time-space class `DTISP(T, S)` and **SC**
(Steve's Class).

The key distinction from intersecting separate time and space classes is that
`DTISP` requires a *single* machine satisfying both bounds simultaneously.
-/

@[expose] public section

namespace Complexity


/-- `DTISP(T, S)` is the class of languages decidable by a single deterministic
    TM running in time `O(T(n))` and space `O(S(n))` simultaneously
    (AB Definition 4.11). Space includes work tapes, excess read-only input-head
    travel, and two-way output-head travel beyond the free verdict cell. -/
def DTISP (T S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (t s : ℕ → ℕ),
    tm.DecidesInTimeSpace L t s ∧ t =O T ∧ s =O S}

/-- **SC** (Steve's Class, named after Stephen Cook) is the class of languages
    decidable in polynomial time and polylogarithmic space simultaneously:
    `SC = ⋃_{k,j} DTISP(n^k, (log n)^j)`. -/
def SC : Set Language :=
  ⋃ k : ℕ, ⋃ j : ℕ, DTISP (· ^ k) (fun n => (Nat.log 2 n) ^ j)

end Complexity
