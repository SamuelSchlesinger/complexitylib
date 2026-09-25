/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.Menu
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CollisionTail
public import Complexitylib.Algebraic.MassProduction.Scheduler

/-!
# Universal menus for a punctured-line scheduling phase

An occupied state is described by at most `capacity` previously accepted
lines and an ordered tuple of `active` targets. This is a finite description
space, including repetitions. A single fixed menu simultaneously contains a
half-clean candidate for every such state whenever the geometric packing
budget holds.

The theorem is nonuniform: the menu depends on the dimensions and request
counts, but is chosen before any occupied state or target tuple is supplied.
This module proves the menu guarantee, not the cost of its circuit evaluator.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped BigOperators LinearAlgebra.Projectivization

/-- A bounded list of optional occupied lines together with ordered active
targets. Empty slots permit every smaller occupied-line collection. -/
abbrev PhaseState (Point Direction : Type*) (capacity active : Nat) :=
  (Fin capacity → Option (Point × Direction)) × (Fin active → Point)

/-- A phase state has at most `capacity * (1 + 3 * addressBits)` bits of
information when points and directions each fit in `addressBits` bits. -/
theorem cardPhaseState_le
    {Point Direction : Type*} [Fintype Point] [Fintype Direction]
    (capacity active addressBits : Nat) (activeLe : active ≤ capacity)
    (pointsSmall : Fintype.card Point ≤ 2 ^ addressBits)
    (directionsSmall : Fintype.card Direction ≤ 2 ^ addressBits) :
    Fintype.card (PhaseState Point Direction capacity active) ≤
      2 ^ (capacity * (1 + 3 * addressBits)) := by
  have oneLe : 1 ≤ (2 : Nat) ^ (2 * addressBits) := by
    have : 0 < (2 : Nat) ^ (2 * addressBits) := by positivity
    omega
  have pairSmall : Fintype.card Point * Fintype.card Direction ≤
      2 ^ (2 * addressBits) := by
    calc
      _ ≤ 2 ^ addressBits * 2 ^ addressBits := Nat.mul_le_mul pointsSmall directionsSmall
      _ = _ := by rw [two_mul, pow_add]
  have slotSmall : Fintype.card Point * Fintype.card Direction + 1 ≤
      2 ^ (1 + 2 * addressBits) := by
    calc
      _ ≤ 2 ^ (2 * addressBits) + 2 ^ (2 * addressBits) := Nat.add_le_add pairSmall oneLe
      _ = _ := by rw [pow_add]; simp; omega
  simp only [PhaseState, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_option]
  calc
    _ ≤ (2 ^ (1 + 2 * addressBits)) ^ capacity * (2 ^ addressBits) ^ capacity := by
      apply Nat.mul_le_mul (Nat.pow_le_pow_left slotSmall capacity)
      exact (Nat.pow_le_pow_left pointsSmall active).trans
        (Nat.pow_le_pow_right (by positivity) activeLe)
    _ = _ := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]

/-- The actual occupied points described by the optional line slots. -/
noncomputable def phaseOccupied
    (state : PhaseState V (ℙ K V) capacity active) : Finset V := by
  classical
  exact Finset.univ.biUnion fun slot =>
    (state.1 slot).elim ∅ fun line => puncturedLine line.1 line.2

/-- A description with `capacity` slots occupies at most
`capacity * (|K| - 1)` points. Overlaps only reduce this number. -/
theorem cardPhaseOccupied_le
    (state : PhaseState V (ℙ K V) capacity active) :
    (phaseOccupied state).card ≤ capacity * (Nat.card K - 1) := by
  classical
  calc
    _ ≤ ∑ slot : Fin capacity,
        ((state.1 slot).elim ∅ fun line => puncturedLine line.1 line.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _slot : Fin capacity, (Nat.card K - 1) := by
      apply Finset.sum_le_sum
      intro slot _
      cases state.1 slot with
      | none => simp
      | some line => simp [card_puncturedLine]
    _ = _ := by simp

/-- A candidate is successful if at least half of the active requests are
clean, with rounding upward for an odd request count. -/
def HalfClean
    (state : PhaseState V (ℙ K V) capacity active)
    (candidate : Fin active → ℙ K V) : Prop :=
  active ≤ 2 * Nat.card {index : Fin active //
    Clean (fun index direction => puncturedLine (state.2 index) direction)
      (phaseOccupied state) candidate index}

/-- Exact single-candidate failure bound under the geometric packing
condition. Repeated targets and overlapping occupied descriptions are allowed. -/
theorem cardNotHalfCleanMulTwoPow_le
    [Fintype V] [Fintype (ℙ K V)]
    (state : PhaseState V (ℙ K V) capacity active)
    (activeLe : active ≤ capacity)
    (budget : 512 * capacity * Nat.card K ≤ Fintype.card (ℙ K V)) :
    Nat.card {candidate : Fin active → ℙ K V // ¬ HalfClean state candidate} *
        2 ^ active ≤ Fintype.card (Fin active → ℙ K V) := by
  classical
  let sets := fun (index : Fin active) (direction : ℙ K V) =>
    puncturedLine (state.2 index) direction
  have totalBudget : 256 * ((phaseOccupied state).card +
      Fintype.card (Fin active) * (Nat.card K - 1)) ≤ Fintype.card (ℙ K V) := by
    calc
      _ ≤ 256 * (capacity * (Nat.card K - 1) + capacity * (Nat.card K - 1)) := by
        exact Nat.mul_le_mul_left _ (Nat.add_le_add (cardPhaseOccupied_le state)
          (Nat.mul_le_mul_right _ (by simpa using activeLe)))
      _ ≤ 512 * capacity * Nat.card K := by
        calc
          _ = 512 * capacity * (Nat.card K - 1) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ _ := budget
  have counted := cardManyCollisionsMulTwoPow_le sets (phaseOccupied state)
    (Nat.card K - 1) (fun index direction => le_of_eq (card_puncturedLine _ _))
    (fun index used => cardIntersectingDirections_le (state.2 index) used) totalBudget
  have failureContained :
      (Finset.univ.filter fun candidate : Fin active → ℙ K V => ¬ HalfClean state candidate) ⊆
      (Finset.univ.filter fun candidate : Fin active → ℙ K V =>
        Fintype.card (Fin active) ≤ 2 * (badRequests sets (phaseOccupied state) candidate).card) := by
    intro candidate membership
    have failed := (Finset.mem_filter.mp membership).2
    have partition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin active)))
      (Clean sets (phaseOccupied state) candidate)
    have tooFew : active > 2 * (Finset.univ.filter
        (Clean sets (phaseOccupied state) candidate)).card := by
      simpa only [HalfClean, Nat.card_eq_fintype_card, Fintype.card_subtype, not_le]
        using failed
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin] at partition ⊢
    change active ≤ 2 * (Finset.univ.filter
      fun index => ¬ Clean sets (phaseOccupied state) candidate index).card
    omega
  have failureCard := Finset.card_le_card failureContained
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply (Nat.mul_le_mul_right (2 ^ active) failureCard).trans
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_fun, Fintype.card_fin] using counted

/-- Universal fixed menus of at most one plus description bits divided by
the active request count. The existential quantifier is outside all states. -/
theorem existsUniversalPhaseMenu
    [Fintype V] [Fintype (ℙ K V)] [Nonempty (ℙ K V)]
    (capacity active addressBits : Nat)
    (activePositive : 0 < active) (activeLe : active ≤ capacity)
    (pointsSmall : Fintype.card V ≤ 2 ^ addressBits)
    (directionsSmall : Fintype.card (ℙ K V) ≤ 2 ^ addressBits)
    (budget : 512 * capacity * Nat.card K ≤ Fintype.card (ℙ K V)) :
    ∃ menu : Fin (capacity * (1 + 3 * addressBits) / active + 1) →
        (Fin active → ℙ K V),
      ∀ state : PhaseState V (ℙ K V) capacity active,
        ∃ entry, HalfClean state (menu entry) := by
  apply existsCoveringMenuOfExponentialBound HalfClean
    (capacity * (1 + 3 * addressBits)) active activePositive
  · exact cardPhaseState_le capacity active addressBits activeLe pointsSmall directionsSmall
  · intro state
    exact cardNotHalfCleanMulTwoPow_le state activeLe budget

/-- Evaluating every menu entry examines a number of candidate lines
linear in `capacity`, apart from the address-width factor. -/
theorem phaseMenuCandidateCount_le
    (capacity active addressBits : Nat) (activeLe : active ≤ capacity) :
    (capacity * (1 + 3 * addressBits) / active + 1) * active ≤
      capacity * (2 + 3 * addressBits) := by
  calc
    _ = (capacity * (1 + 3 * addressBits) / active) * active + active := by ring
    _ ≤ capacity * (1 + 3 * addressBits) + capacity :=
      Nat.add_le_add (Nat.div_mul_le_self _ _) activeLe
    _ = _ := by ring

end Algebraic.MassProduction.Nonuniform
