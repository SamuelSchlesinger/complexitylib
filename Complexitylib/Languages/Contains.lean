/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Languages.Trivial
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `containsZero` and `containsOne`: "contains-a-bit" languages

The strings containing at least one `0`-bit (resp. `1`-bit). Decided by a
3-state `scannerTM` instance: the scan state is a single `Bool` tracking
"some bit seen so far equals target".

## Main definitions

- `Language.containsZero`, `Language.containsOne`.
- `TM.containsTM target` — `scannerTM` specialized to `target : Bool`.

## Main results

- `containsZero_in_DTIME`, `containsOne_in_DTIME` — both in `DTIME(n + 2)`.
- `containsZero_mem_P`, `containsOne_mem_P`.
-/

@[expose] public section

namespace Complexity

open Complexity

namespace TM

/-- Scanner for "some input bit equals `target`". Scan state: a `Bool`
    encoding "some bit seen so far equals `target`". -/
def containsTM (target : Bool) : TM 0 :=
  scannerTM (S := Bool) false
    (fun seen b => seen || decide (b = target))
    (fun seen => if seen then Γw.one else Γw.zero)

end TM

namespace Language

/-- Strings containing at least one `0`-bit. -/
def containsZero : Language := {x | ∃ b ∈ x, b = false}

/-- Strings containing at least one `1`-bit. -/
def containsOne : Language := {x | ∃ b ∈ x, b = true}

end Language

-- ════════════════════════════════════════════════════════════════════════
-- Fold characterization
-- ════════════════════════════════════════════════════════════════════════

/-- The "exists-match" fold over `x` yields `true` iff some bit of `x`
    matches `target`. -/
private theorem contains_fold (target : Bool) :
    ∀ x : List Bool,
      x.foldl (fun seen b => seen || decide (b = target)) false =
        decide (∃ b ∈ x, b = target) := by
  -- Generalize the seed so the induction carries.
  have aux : ∀ (x : List Bool) (seed : Bool),
      x.foldl (fun s b => s || decide (b = target)) seed =
        (seed || decide (∃ b ∈ x, b = target)) := by
    intro x
    induction x with
    | nil => intro seed; simp
    | cons b xs ih =>
      intro seed
      rw [List.foldl_cons, ih, Bool.or_assoc]
      congr 1
      rw [← Bool.decide_or]
      congr 1
      apply propext
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨c, hc, hct⟩)
        · exact ⟨b, Or.inl rfl, h⟩
        · exact ⟨c, Or.inr hc, hct⟩
      · rintro ⟨c, hc | hc, hct⟩
        · exact Or.inl (hc ▸ hct)
        · exact Or.inr ⟨c, hc, hct⟩
  intro x
  rw [aux x false, Bool.false_or]

/-- `decide (∃ b ∈ x, b = target) = true ↔ ∃ b ∈ x, b = target`. -/
private theorem decide_exists_mem_iff (target : Bool) (x : List Bool) :
    decide (∃ b ∈ x, b = target) = true ↔ ∃ b ∈ x, b = target :=
  decide_eq_true_iff

-- ════════════════════════════════════════════════════════════════════════
-- DTIME memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`containsZero ∈ DTIME(n + 2)`**. -/
theorem containsZero_in_DTIME :
    Language.containsZero ∈ DTIME (fun n => n + 2) := by
  refine ⟨0, TM.containsTM false, fun n => n + 2, ?_, BigO.refl _⟩
  exact TM.scannerTM_decidesInTime (S := Bool) false
    (fun seen b => seen || decide (b = false)) id
    (L := Language.containsZero)
    (fun x => by
      show (∃ b ∈ x, b = false) ↔ (id (x.foldl _ false) = true)
      rw [contains_fold false x, id]
      exact (decide_exists_mem_iff false x).symm)

/-- **`containsOne ∈ DTIME(n + 2)`**. -/
theorem containsOne_in_DTIME :
    Language.containsOne ∈ DTIME (fun n => n + 2) := by
  refine ⟨0, TM.containsTM true, fun n => n + 2, ?_, BigO.refl _⟩
  exact TM.scannerTM_decidesInTime (S := Bool) false
    (fun seen b => seen || decide (b = true)) id
    (L := Language.containsOne)
    (fun x => by
      show (∃ b ∈ x, b = true) ↔ (id (x.foldl _ false) = true)
      rw [contains_fold true x, id]
      exact (decide_exists_mem_iff true x).symm)

-- ════════════════════════════════════════════════════════════════════════
-- P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`containsZero ∈ P`**. -/
theorem containsZero_mem_P : Language.containsZero ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ containsZero_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

/-- **`containsOne ∈ P`**. -/
theorem containsOne_mem_P : Language.containsOne ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ containsOne_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Complexity
