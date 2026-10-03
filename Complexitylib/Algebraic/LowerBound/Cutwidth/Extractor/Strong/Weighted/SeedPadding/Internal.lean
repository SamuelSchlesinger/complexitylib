/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Equiv
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Retained-seed extraction after adding unused randomness

Append a fresh independent seed and use the identity output step. The
retained-seed distance bound preserves the original error, including tests
that inspect the unused seed. Splitting a Boolean word into its prefix and
suffix gives the fixed-width padding rule.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_ignoreSeed {α Seed Ω Tail : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Fintype Tail]
    [Nonempty Seed] [Nonempty Ω] [Nonempty Tail]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededExtractor (fun a (seeds : Seed × Tail) => E a seeds.1) K ε := by
  intro p probability cap T
  have uniform := isProbabilityWeight_uniform Ω
  have actual := probability.weightedSeededOutput E
  have ideal := isProbabilityWeight_seedFamilyWeight
    (fun _ : Seed => uniformWeight Ω) (fun _ => uniform)
  have close : weightDist (weightedSeededOutput p E)
      (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) ≤ ε := by
    apply (weightDist_le_iff_tests _ _ (actual.2.trans ideal.2.symm)).mpr
    intro test
    rw [weightTestProb_weightedSeededOutput, weightTestProb_seedFamilyWeight_uniform]
    exact extract p probability cap test
  let step := fun (_ : Seed) (x : Ω) (_ : Tail) => x
  have idealStep : retainedSeedStep step (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) =
      seedFamilyWeight (fun _ : Seed × Tail => uniformWeight Ω) := by
    rw [retainedSeedStep_seedFamilyWeight]
    change seedFamilyWeight (fun _ : Seed × Tail => mapWeight id (uniformWeight Ω)) = _
    rw [mapWeight_id]
  have extended := (retainedSeedStep_dist_le step _ _).trans close
  rw [retainedSeedStep_weightedSeededOutput, idealStep] at extended
  have actualExtended := probability.weightedSeededOutput
    (fun a (seeds : Seed × Tail) => E a seeds.1)
  have idealExtended := isProbabilityWeight_seedFamilyWeight
    (fun _ : Seed × Tail => uniformWeight Ω) (fun _ => uniform)
  have tested := ((weightDist_le_iff_tests _ _
    (actualExtended.2.trans idealExtended.2.symm)).mp extended) T
  simpa only [weightTestProb_weightedSeededOutput, weightTestProb_seedFamilyWeight_uniform]
    using tested

private def splitSeedEquiv (d r : Nat) : (Fin (d + r) → Bool) ≃
    (Fin d → Bool) × (Fin r → Bool) :=
  ((finSumFinEquiv : Fin d ⊕ Fin r ≃ Fin (d + r)).symm.arrowCongr
    (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

private theorem padSeed_add {α Ω : Type*} [Fintype α] [Fintype Ω] [Nonempty Ω]
    {d r K : Nat} {ε : ℝ} {E : α → (Fin d → Bool) → Ω}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededExtractor
      (fun a (seed : Fin (d + r) → Bool) => E a (fun j => seed (Fin.castAdd r j))) K ε := by
  have padded := weightedStrongSeededExtractor_ignoreSeed (Tail := Fin r → Bool) extract
  exact padded.equiv (splitSeedEquiv d r) (Equiv.refl Ω)

theorem weightedStrongSeededExtractor_padSeed {α Ω : Type*}
    [Fintype α] [Fintype Ω] [Nonempty Ω]
    {d r K : Nat} {ε : ℝ} {E : α → (Fin d → Bool) → Ω}
    (extract : WeightedStrongSeededExtractor E K ε) (size : d ≤ r) :
    WeightedStrongSeededExtractor
      (fun a (seed : Fin r → Bool) => E a (fun j => seed (Fin.castLE size j))) K ε := by
  obtain ⟨tail, rfl⟩ := Nat.exists_eq_add_of_le size
  exact padSeed_add extract

end Algebraic.Cutwidth.Extractor.Internal
