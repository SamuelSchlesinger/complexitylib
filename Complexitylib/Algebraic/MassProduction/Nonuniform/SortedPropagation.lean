/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.Propagation

/-!
# Propagation along sorted equal-key runs

In a sorted array, equal keys occupy an interval. Linking adjacent equal
keys therefore propagates a source bit to exactly the later records having
that key, regardless of how many such records there are.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Propagation

/-- Adjacent records are linked exactly when their keys are equal. -/
def keyLinks {Key : Type*} [DecidableEq Key] (key : Nat → Key) (index : Nat) : Bool :=
  if index = 0 then false else decide (key (index - 1) = key index)

/-- The segmented recurrence on sorted keys reports precisely the source
bits in the equal-key run ending at the last processed record. -/
theorem value_sorted_eq_true_iff
    {Key : Type*} [LinearOrder Key]
    (key : Nat → Key) (source : Nat → Bool) (count : Nat)
    (countPositive : 0 < count)
    (sorted : ∀ {left right}, left ≤ right → right < count → key left ≤ key right) :
    value source (keyLinks key) count = true ↔
      ∃ start, start < count ∧ source start = true ∧ key start = key (count - 1) := by
  rw [value_eq_true_iff]
  constructor
  · rintro ⟨start, startBefore, starts, links⟩
    have connected : ∀ index, start ≤ index → index < count → key start = key index := by
      intro index after
      induction index, after using Nat.le_induction with
      | base => intro _; rfl
      | succ index after ih =>
          intro before
          have link := links (index + 1) (by omega) before
          have adjacent : key index = key (index + 1) := by
            simpa [keyLinks] using link
          exact (ih (by omega)).trans adjacent
    exact ⟨start, startBefore, starts, connected (count - 1) (by omega) (by omega)⟩
  · rintro ⟨start, startBefore, starts, sameKey⟩
    refine ⟨start, startBefore, starts, ?_⟩
    intro index after before
    have previousLe : key (index - 1) ≤ key index := sorted (by omega) before
    have firstLe : key start ≤ key (index - 1) := sorted (by omega) (by omega)
    have lastLe : key index ≤ key (count - 1) := sorted (by omega) (by omega)
    have equal : key (index - 1) = key index :=
      le_antisymm previousLe (lastLe.trans (sameKey.symm.le.trans firstLe))
    simp only [keyLinks, ite_eq_right (by omega : index ≠ 0), decide_eq_true_eq]
    exact equal

end Algebraic.MassProduction.Nonuniform.Propagation
