/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonProbeQuery.Defs
import Complexitylib.Circuits.BarringtonProbeQuery.Internal
import Complexitylib.Circuits.BarringtonTokenQuery

/-!
# Direct Barrington queries through canonical formula-code probes

This module replaces the complete encoded formula list by a numeric bit
oracle. With fuel covering the header and every token field, the first/last
occupied addresses and every fixed-address instruction agree exactly with the
reference Barrington compiler.

## Main results

- `barringtonProbeSlotsNonempty_eq` gives exact schedule nonemptiness without
  computing either extreme address.
- `barringtonCompileProbeSlotOccupied_eq` gives exact target-free occupancy at
  every fixed address.
- `barringtonProbeFirstOccupiedScan?_eq` and
  `barringtonProbeLastOccupiedScan?_eq` recover the structural extremes by
  bounded scans of that occupancy kernel.
- `barringtonCompileProbeScannedSlot?_eq_instruction?` gives the exact
  instruction query using only those bounded scans.
- `barringtonProbeFirstOccupiedSlot?_eq` gives the structural first address.
- `barringtonProbeLastOccupiedSlot?_eq` gives the structural last address.
- `barringtonCompileProbeSlot?_eq_instruction?` gives the exact instruction at
  every fixed address.
-/

namespace Complexity

/-- Probe traversal over canonical formula bits computes exact fixed-schedule
nonemptiness without carrying a target permutation. -/
theorem barringtonProbeSlotsNonempty_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonProbeSlotsNonempty fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ =
      barringtonCompileSlotsNonempty fuel formula := by
  simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
    (barringtonProbeSlotOccupancy_correct_context_internal fuel [] [] formula
      bitFuel (by simpa using hheader) (by simpa using hbound)).1

/-- Probe traversal over canonical formula bits computes exact occupancy at
every fixed address, independently of the compiler target. -/
theorem barringtonCompileProbeSlotOccupied_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5)) (slot : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeSlotOccupied fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ slot =
      (BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot).isSome := by
  rw [show barringtonCompileProbeSlotOccupied fuel
      (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
      bitFuel ⟨0, formula.size⟩ slot =
      barringtonCompileSlotOccupied fuel formula slot by
    simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
      (barringtonProbeSlotOccupancy_correct_context_internal fuel [] []
        formula bitFuel (by simpa using hheader)
          (by simpa using hbound)).2 slot]
  exact barringtonCompileSlotOccupied_correct_internal fuel formula target slot
    |>.trans (congrArg Option.isSome
      (barringtonCompileSlot?_correct_internal fuel formula target slot))

/-- Scanning the oracle occupancy kernel from the start recovers the exact
structural first occupied address. -/
theorem barringtonProbeFirstOccupiedScan?_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonProbeFirstOccupiedScan? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ =
      barringtonFirstOccupiedSlot? fuel formula := by
  rw [barringtonProbeFirstOccupiedScan?]
  have hoccupied :
      barringtonCompileProbeSlotOccupied fuel
          (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
          bitFuel ⟨0, formula.size⟩ =
        fun slot => (BPSlots.instruction?
          (barringtonCompileSlots fuel formula target) slot).isSome := by
    funext slot
    exact barringtonCompileProbeSlotOccupied_eq fuel formula bitFuel target
      slot hheader hbound
  rw [hoccupied, ← barringtonCompileSlots_length_internal fuel formula target]
  rw [BPSlots.firstTrueSlot?_instruction_internal]
  exact (barringtonOccupiedSlots_correct_internal fuel formula target).1.symm

/-- Scanning the oracle occupancy kernel through the complete bound recovers
the exact structural last occupied address. -/
theorem barringtonProbeLastOccupiedScan?_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonProbeLastOccupiedScan? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ =
      barringtonLastOccupiedSlot? fuel formula := by
  rw [barringtonProbeLastOccupiedScan?]
  have hoccupied :
      barringtonCompileProbeSlotOccupied fuel
          (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
          bitFuel ⟨0, formula.size⟩ =
        fun slot => (BPSlots.instruction?
          (barringtonCompileSlots fuel formula target) slot).isSome := by
    funext slot
    exact barringtonCompileProbeSlotOccupied_eq fuel formula bitFuel target
      slot hheader hbound
  rw [hoccupied, ← barringtonCompileSlots_length_internal fuel formula target]
  rw [BPSlots.lastTrueSlot?_instruction_internal]
  exact (barringtonOccupiedSlots_correct_internal fuel formula target).2.symm

/-- Every scan-based instruction query through canonical formula bits agrees
with the selected instruction of the list-valued fixed schedule. -/
theorem barringtonCompileProbeScannedSlot?_eq_instruction? (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5)) (slot : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeScannedSlot? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot := by
  calc
    _ = barringtonCompileSlot? fuel formula target slot := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        barringtonCompileProbeScannedSlot?_correct_context_internal fuel [] []
          formula bitFuel target slot (by simpa using hheader)
            (by simpa using hbound)
    _ = _ := barringtonCompileSlot?_correct_internal fuel formula target slot

/-- Probe traversal over canonical formula bits computes the structural first
occupied Barrington address. -/
theorem barringtonProbeFirstOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonProbeFirstOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ =
      barringtonFirstOccupiedSlot? fuel formula := by
  calc
    _ = barringtonTokensFirstOccupiedSlot? fuel
        (FormulaCode.tokens formula) := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        (barringtonProbeOccupiedSlots_correct_context_internal fuel [] []
          formula bitFuel (by simpa using hheader)
            (by simpa using hbound)).1
    _ = _ := barringtonTokensFirstOccupiedSlot?_eq fuel formula

/-- Probe traversal over canonical formula bits computes the structural last
occupied Barrington address. -/
theorem barringtonProbeLastOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonProbeLastOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ =
      barringtonLastOccupiedSlot? fuel formula := by
  calc
    _ = barringtonTokensLastOccupiedSlot? fuel
        (FormulaCode.tokens formula) := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        (barringtonProbeOccupiedSlots_correct_context_internal fuel [] []
          formula bitFuel (by simpa using hheader)
            (by simpa using hbound)).2
    _ = _ := barringtonTokensLastOccupiedSlot?_eq fuel formula

/-- Every direct query through canonical formula-code probes agrees with the
selected instruction of the list-valued fixed Barrington schedule. -/
theorem barringtonCompileProbeSlot?_eq_instruction? (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5)) (slot : ℕ)
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeSlot? fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot := by
  calc
    _ = barringtonCompileTokensSlot? fuel (FormulaCode.tokens formula)
        target slot := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        barringtonCompileProbeSlot?_correct_context_internal fuel [] []
          formula bitFuel target slot (by simpa using hheader)
            (by simpa using hbound)
    _ = _ :=
      barringtonCompileTokensSlot?_eq_instruction? fuel formula target slot

end Complexity
