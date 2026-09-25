/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PhaseMenu

/-!
# Accepting exactly half of a successful phase

The menu guarantee permits a fixed-size acceptance step: choose exactly
`ceil(active/2)` clean requests. Their recovery lines avoid all occupied
points and are pairwise disjoint, while exactly `floor(active/2)` requests
remain. The existential selection here specifies the semantic obligation of
the circuit's first-clean-request selection pass.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped LinearAlgebra.Projectivization

/-- A successful candidate has an exactly half-sized clean subset with
disjoint recovery lines and a fixed-size complement. -/
theorem HalfClean.existsHalfSelection
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (state : PhaseState V (ℙ K V) capacity active)
    (candidate : Fin active → ℙ K V) (successful : HalfClean state candidate) :
    ∃ accepted : Finset (Fin active),
      accepted.card = (active + 1) / 2 ∧
      acceptedᶜ.card = active / 2 ∧
      (∀ index ∈ accepted,
        Disjoint (puncturedLine (state.2 index) (candidate index)) (phaseOccupied state)) ∧
      (accepted : Set (Fin active)).Pairwise (fun left right =>
        Disjoint (puncturedLine (state.2 left) (candidate left))
          (puncturedLine (state.2 right) (candidate right))) := by
  classical
  let clean := Finset.univ.filter fun index =>
    Clean (fun index direction => puncturedLine (state.2 index) direction)
      (phaseOccupied state) candidate index
  have cleanLarge : (active + 1) / 2 ≤ clean.card := by
    have enough : active ≤ 2 * clean.card := by
      simpa only [HalfClean, clean, Nat.card_eq_fintype_card, Fintype.card_subtype] using successful
    omega
  obtain ⟨accepted, acceptedClean, acceptedCard⟩ := Finset.exists_subset_card_eq cleanLarge
  refine ⟨accepted, acceptedCard, ?_, ?_, ?_⟩
  · rw [Finset.card_compl, Fintype.card_fin, acceptedCard]
    omega
  · intro index membership
    exact (Finset.mem_filter.mp (acceptedClean membership)).2.1
  · intro left leftAccepted right _ different
    exact (Finset.mem_filter.mp (acceptedClean leftAccepted)).2.2 right different.symm

end Algebraic.MassProduction.Nonuniform
