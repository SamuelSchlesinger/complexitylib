/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PhaseMenu
public import Complexitylib.Algebraic.MassProduction.FiniteParameters

/-!
# Universal phase menus with power-of-two length

Repeat the first candidate in the unused suffix of the next power-of-two
menu. Coverage is preserved, and the number of evaluated candidate lines
increases by a factor of at most two.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open Sorting
open scoped LinearAlgebra.Projectivization

/-- Extend a nonempty fixed menu by repeating its first entry. -/
def padMenu (menu : Fin length → Choice) (positive : 0 < length)
    (_fits : length ≤ paddedLength) (index : Fin paddedLength) : Choice :=
  if before : index.val < length then menu ⟨index.val, before⟩ else menu ⟨0, positive⟩

/-- Every original entry survives padding at the same position. -/
theorem padMenu_original (menu : Fin length → Choice) (positive : 0 < length)
    (fits : length ≤ paddedLength) (index : Fin length) :
    padMenu menu positive fits (Fin.castLE fits index) = menu index := by
  simp only [padMenu, Fin.val_castLE, index.isLt, dite_true]

/-- Padding a covering menu preserves universal coverage. -/
theorem padMenu_covers (good : State → Choice → Prop)
    (menu : Fin length → Choice) (positive : 0 < length) (fits : length ≤ paddedLength)
    (covers : Covers good menu) : Covers good (padMenu menu positive fits) := by
  intro state
  obtain ⟨entry, successful⟩ := covers state
  exact ⟨Fin.castLE fits entry, by simpa only [padMenu_original] using successful⟩

/-- Power-of-two depth for the universal menu at one phase. -/
def phaseMenuDepth (capacity active addressBits : Nat) : Nat :=
  FiniteParameters.binaryDepth (capacity * (1 + 3 * addressBits) / active + 1)

/-- The power-of-two menu still covers every geometric phase state. -/
theorem existsUniversalPowerPhaseMenu
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Fintype V] [Fintype (ℙ K V)] [Nonempty (ℙ K V)]
    (capacity active addressBits : Nat)
    (activePositive : 0 < active) (activeLe : active ≤ capacity)
    (pointsSmall : Fintype.card V ≤ 2 ^ addressBits)
    (directionsSmall : Fintype.card (ℙ K V) ≤ 2 ^ addressBits)
    (budget : 512 * capacity * Nat.card K ≤ Fintype.card (ℙ K V)) :
    ∃ menu : Fin (networkRecords (phaseMenuDepth capacity active addressBits)) → (Fin active → ℙ K V),
      ∀ state : PhaseState V (ℙ K V) capacity active, ∃ entry, HalfClean state (menu entry) := by
  obtain ⟨menu, covers⟩ := existsUniversalPhaseMenu capacity active addressBits
    activePositive activeLe pointsSmall directionsSmall budget
  exact ⟨padMenu menu (Nat.zero_lt_succ _) (FiniteParameters.records_le_networkRecords _),
    padMenu_covers HalfClean menu (Nat.zero_lt_succ _) (FiniteParameters.records_le_networkRecords _) covers⟩

/-- Padding adds at most a factor of two to the linear candidate-line bound. -/
theorem powerPhaseMenuCandidateCount_le (capacity active addressBits : Nat) (activeLe : active ≤ capacity) :
    networkRecords (phaseMenuDepth capacity active addressBits) * active ≤
      2 * (capacity * (2 + 3 * addressBits)) := by
  have padded := (FiniteParameters.networkRecords_binaryDepth_lt_two_mul
    (capacity * (1 + 3 * addressBits) / active + 1) (Nat.zero_lt_succ _)).le
  calc
    _ ≤ (2 * (capacity * (1 + 3 * addressBits) / active + 1)) * active := Nat.mul_le_mul_right _ padded
    _ = 2 * ((capacity * (1 + 3 * addressBits) / active + 1) * active) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (phaseMenuCandidateCount_le capacity active addressBits activeLe)

end Algebraic.MassProduction.Nonuniform
