/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Switching.Collection.Defs
public import Complexitylib.Circuits.AC0.Switching.Internal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Simultaneous switching for finite formula collections -- proof internals
-/

@[expose] public section

namespace Complexity

namespace Switching

private theorem eventCount_exists_mul_le
    (event : Fin eventCount → Restriction.On N → Prop)
    [∀ index, DecidablePred (event index)]
    (multiplier bound : ℕ)
    (hindividual :
      ∀ index,
        RandomRestriction.eventCount (q := q) (event index) *
          multiplier ≤ bound) :
    RandomRestriction.eventCount (q := q)
          (fun restriction => ∃ index, event index restriction) *
        multiplier ≤
      eventCount * bound := by
  have hunionRaw :=
    RandomRestriction.eventCount_exists_le_sum_internal
      (q := q) event
  have hunion :
      RandomRestriction.eventCount (q := q)
          (fun restriction => ∃ index, event index restriction) ≤
        ∑ index,
          RandomRestriction.eventCount (q := q) (event index) := by
    simpa [RandomRestriction.eventCount] using hunionRaw
  calc
    RandomRestriction.eventCount (q := q)
          (fun restriction => ∃ index, event index restriction) *
        multiplier ≤
      (∑ index,
        RandomRestriction.eventCount (q := q) (event index)) *
        multiplier :=
      Nat.mul_le_mul_right _ hunion
    _ = ∑ index,
        RandomRestriction.eventCount (q := q) (event index) *
          multiplier := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _index : Fin eventCount, bound := by
      apply Finset.sum_le_sum
      intro index hindex
      exact hindividual index
    _ = eventCount * bound := by simp

end Switching

namespace DNF

theorem switchingAnyBad_width_encoding_bound_internal
    (formulas : Fin formulaCount → DNF N)
    (hconsistent :
      ∀ index, (formulas index).Consistent)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad formulas queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) := by
  have hbound :=
    Switching.eventCount_exists_mul_le
      (q := q)
      (fun index : Fin formulaCount =>
        switchingBad (formulas index) queryCount)
      (q ^ queryCount)
      ((2 * q + 1) ^ N *
        (4 * (width + 1)) ^ queryCount)
      (by
        intro index
        have hindividual :=
          switchingBad_width_encoding_bound_internal
            (formulas index) (hconsistent index)
            q queryCount
        exact hindividual.trans
          (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_left
              (Nat.mul_le_mul_left 4
                (Nat.add_le_add_right
                  (hwidth index) 1))
              _)))
  simpa [RandomRestriction.eventCount,
    switchingAnyBad] using hbound

theorem switchingAnyBad_consistentParts_width_encoding_bound_internal
    (formulas : Fin formulaCount → DNF N)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad (DNF.consistentParts formulas) queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) := by
  apply switchingAnyBad_width_encoding_bound_internal
  · intro index
    exact consistent_consistentPart_internal (formulas index)
  · intro index
    exact (width_consistentPart_le_internal
      (formulas index)).trans (hwidth index)

end DNF

namespace CNF

theorem switchingAnyBad_width_encoding_bound_internal
    (formulas : Fin formulaCount → CNF N)
    (hconsistent :
      ∀ index, (formulas index).Consistent)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad formulas queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) := by
  have hbound :=
    Switching.eventCount_exists_mul_le
      (q := q)
      (fun index : Fin formulaCount =>
        switchingBad (formulas index) queryCount)
      (q ^ queryCount)
      ((2 * q + 1) ^ N *
        (4 * (width + 1)) ^ queryCount)
      (by
        intro index
        have hindividual :=
          switchingBad_width_encoding_bound_internal
            (formulas index) (hconsistent index)
            q queryCount
        exact hindividual.trans
          (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_left
              (Nat.mul_le_mul_left 4
                (Nat.add_le_add_right
                  (hwidth index) 1))
              _)))
  simpa [RandomRestriction.eventCount,
    switchingAnyBad] using hbound

theorem switchingAnyBad_consistentParts_width_encoding_bound_internal
    (formulas : Fin formulaCount → CNF N)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad (CNF.consistentParts formulas) queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) := by
  apply switchingAnyBad_width_encoding_bound_internal
  · intro index
    exact consistent_consistentPart_internal (formulas index)
  · intro index
    exact (width_consistentPart_le_internal
      (formulas index)).trans (hwidth index)

end CNF

end Complexity
