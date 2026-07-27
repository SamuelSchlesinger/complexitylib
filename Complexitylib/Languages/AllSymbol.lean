/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Languages.Trivial
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Complement

/-!
# `allZeros` and `allOnes`: single-symbol languages

The strings consisting entirely of `0`s (resp. `1`s), including the empty
string. Decided by a 3-state `scannerTM` instance: the scan state is a
single `Bool` tracking "every bit so far equals target".

## Main definitions

- `Language.allZeros`, `Language.allOnes`.
- `TM.allSymbolTM target` — `scannerTM` specialized to `target : Bool`.

## Main results

- `allZeros_in_DTIME`, `allOnes_in_DTIME` — both in `DTIME(n + 2)`.
- `allZeros_mem_P`, `allOnes_mem_P`.
-/

@[expose] public section

namespace Complexity

open Complexity

namespace TM

/-- Scanner for "all input bits equal `target`". Scan state: a `Bool`
    encoding "all bits seen so far equal `target`". -/
def allSymbolTM (target : Bool) : TM 0 :=
  scannerTM (S := Bool) true
    (fun stillOK b => stillOK && decide (b = target))
    (fun stillOK => if stillOK then Γw.one else Γw.zero)

end TM

namespace Language

/-- Strings consisting entirely of `0`-bits (including `[]`). -/
def allZeros : Language := {x | ∀ b ∈ x, b = false}

/-- Strings consisting entirely of `1`-bits (including `[]`). -/
def allOnes : Language := {x | ∀ b ∈ x, b = true}

end Language

-- ════════════════════════════════════════════════════════════════════════
-- Fold characterization
-- ════════════════════════════════════════════════════════════════════════

/-- The "all-match" fold over `x` yields `true` iff every bit of `x`
    matches `target`. -/
private theorem allSymbol_fold (target : Bool) :
    ∀ x : List Bool,
      x.foldl (fun stillOK b => stillOK && decide (b = target)) true =
        decide (∀ b ∈ x, b = target) := by
  -- Generalize the seed so the induction carries.
  have aux : ∀ (x : List Bool) (seed : Bool),
      x.foldl (fun s b => s && decide (b = target)) seed =
        (seed && decide (∀ b ∈ x, b = target)) := by
    intro x
    induction x with
    | nil => intro seed; simp
    | cons b xs ih =>
      intro seed
      rw [List.foldl_cons, ih]
      by_cases hb : b = target
      · simp only [hb, decide_true, Bool.and_true]
        congr 1
        simp only [List.mem_cons, forall_eq_or_imp, true_and]
      · simp only [hb, decide_false, Bool.and_false, Bool.false_and]
        symm; rw [Bool.and_eq_false_iff]; right
        rw [decide_eq_false_iff_not]
        intro h
        exact hb (h b List.mem_cons_self)
  intro x
  rw [aux x true, Bool.true_and]

/-- `decide (∀ b ∈ x, b = target) = true ↔ x ∈ allSymbol` (Prop form). -/
private theorem decide_forall_mem_iff (target : Bool) (x : List Bool) :
    decide (∀ b ∈ x, b = target) = true ↔ ∀ b ∈ x, b = target :=
  decide_eq_true_iff

-- ════════════════════════════════════════════════════════════════════════
-- DTIME memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`allZeros ∈ DTIME(n + 2)`**. -/
theorem allZeros_in_DTIME :
    Language.allZeros ∈ DTIME (fun n => n + 2) := by
  refine ⟨0, TM.allSymbolTM false, fun n => n + 2, ?_, BigO.refl _⟩
  -- Observe: allSymbolTM false = scannerTM ... (fun s => if s then .one else .zero)
  --                            = scannerTM ... (fun s => if (id s) then .one else .zero)
  exact TM.scannerTM_decidesInTime (S := Bool) true
    (fun stillOK b => stillOK && decide (b = false)) id
    (L := Language.allZeros)
    (fun x => by
      show (∀ b ∈ x, b = false) ↔ (id (x.foldl _ true) = true)
      rw [allSymbol_fold false x, id]
      exact (decide_forall_mem_iff false x).symm)

/-- **`allOnes ∈ DTIME(n + 2)`**. -/
theorem allOnes_in_DTIME :
    Language.allOnes ∈ DTIME (fun n => n + 2) := by
  refine ⟨0, TM.allSymbolTM true, fun n => n + 2, ?_, BigO.refl _⟩
  exact TM.scannerTM_decidesInTime (S := Bool) true
    (fun stillOK b => stillOK && decide (b = true)) id
    (L := Language.allOnes)
    (fun x => by
      show (∀ b ∈ x, b = true) ↔ (id (x.foldl _ true) = true)
      rw [allSymbol_fold true x, id]
      exact (decide_forall_mem_iff true x).symm)

-- ════════════════════════════════════════════════════════════════════════
-- P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`allZeros ∈ P`**. -/
theorem allZeros_mem_P : Language.allZeros ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ allZeros_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

/-- **`allOnes ∈ P`**. -/
theorem allOnes_mem_P : Language.allOnes ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ allOnes_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Complexity
