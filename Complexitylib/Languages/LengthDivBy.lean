/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner
public import Complexitylib.Classes.Containments

/-!
# `lengthDivBy k`: length-divisibility language family

Strings whose length is divisible by `k` (for `k ≥ 1`). Decided by a
`(k + 2)`-state `scannerTM` instance: the scan state is the current
length taken `mod k`, incremented by `1` on each bit.

This generalizes `evenLength` (which is `lengthDivBy 2`).

## Main definitions

- `Language.lengthDivBy k`.
- `TM.lengthDivByTM k` — `scannerTM` specialized to `ZMod k` counter.

## Main results

- `lengthDivBy_in_DTIME` — `lengthDivBy k ∈ DTIME(n + 2)`.
- `lengthDivBy_mem_P`.
-/


public section

namespace Complexity

open Complexity

namespace TM

/-- Scanner for "input length is divisible by `k`". Scan state: the current
    length `mod k` (a `ZMod k`). -/
def lengthDivByTM (k : ℕ) [NeZero k] : TM 0 :=
  scannerTM (S := ZMod k) (0 : ZMod k)
    (fun s _ => s + 1)
    (fun s => if decide (s = 0) = true then Γw.one else Γw.zero)

end TM

namespace Language

/-- Strings whose length is divisible by `k`. -/
def lengthDivBy (k : ℕ) : Language := {x | k ∣ x.length}

end Language

-- ════════════════════════════════════════════════════════════════════════
-- Fold characterization
-- ════════════════════════════════════════════════════════════════════════

/-- The "count bits mod k" fold: starting from `seed`, scanning `x` yields
    `seed + x.length` in `ZMod k`. -/
-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
private theorem lengthDivBy_fold (k : ℕ) [NeZero k] :
    ∀ (x : List Bool) (seed : ZMod k),
      x.foldl (fun (s : ZMod k) (_ : Bool) => s + 1) seed =
        seed + (x.length : ZMod k) := by
  intro x
  induction x with
  | nil => intro seed; simp
  | cons b xs ih =>
    intro seed
    rw [List.foldl_cons, ih, List.length_cons]
    push_cast
    ring

private theorem lengthDivBy_fold_zero (k : ℕ) [NeZero k] (x : List Bool) :
    x.foldl (fun (s : ZMod k) (_ : Bool) => s + 1) 0 = (x.length : ZMod k) := by
  rw [lengthDivBy_fold, zero_add]

-- ════════════════════════════════════════════════════════════════════════
-- DTIME memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`lengthDivBy k ∈ DTIME(n + 2)`**. -/
theorem lengthDivBy_in_DTIME (k : ℕ) [NeZero k] :
    Language.lengthDivBy k ∈ DTIME (fun n => n + 2) := by
  refine ⟨0, TM.lengthDivByTM k, fun n => n + 2, ?_, BigO.refl _⟩
  exact TM.scannerTM_decidesInTime (S := ZMod k) 0
    (fun s _ => s + 1) (fun s => decide (s = 0))
    (L := Language.lengthDivBy k)
    (fun x => by
      show (k ∣ x.length) ↔ (decide (x.foldl _ 0 = 0) = true)
      rw [lengthDivBy_fold_zero, decide_eq_true_iff,
          ZMod.natCast_eq_zero_iff x.length k])

-- ════════════════════════════════════════════════════════════════════════
-- P membership
-- ════════════════════════════════════════════════════════════════════════

/-- **`lengthDivBy k ∈ P`**. -/
theorem lengthDivBy_mem_P (k : ℕ) [NeZero k] : Language.lengthDivBy k ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ (lengthDivBy_in_DTIME k)⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Complexity
