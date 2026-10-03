/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Shared-seed extraction from full-entropy block witnesses

Every full-entropy block witness is uniform on its entire tuple space.
The retained-seed total-variation comparison then gives the same bound on
all joint seed-output tests.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedBlockTest_of_uniform_witness {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {t : Nat} (p : α → ℝ) (E : α → Seed → (Fin t → Ω))
    (probability : IsProbabilityWeight p) (q : Seed → (Fin t → Ω) → ℝ)
    (witness : ∀ y, IsBlockSource (q y) (Fintype.card Ω)) {δ : ℝ}
    (close : weightDist (weightedSeededOutput p E) (seedFamilyWeight q) ≤ δ)
    (T : Finset (Seed × (Fin t → Ω))) :
    |weightedSeededTestProb p E T - uniformSeededTestProb T| ≤ δ := by
  have uniform : q = fun _ => uniformWeight (Fin t → Ω) :=
    funext fun y => (witness y).eq_uniform
  rw [uniform] at close
  have actual := probability.weightedSeededOutput E
  have ideal := isProbabilityWeight_seedFamilyWeight
    (fun _ : Seed => uniformWeight (Fin t → Ω))
    (fun _ => isProbabilityWeight_uniform (Fin t → Ω))
  have tests := (weightDist_le_iff_tests _ _ (actual.2.trans ideal.2.symm)).mp close T
  simpa only [weightTestProb_weightedSeededOutput, weightTestProb_seedFamilyWeight_uniform]
    using tests

theorem weightedStrongSeededExtractor_block {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) {t : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K)
    (T : Finset (Seed × (Fin t → Ω))) :
    |weightedSeededTestProb p (fun x y i => E (x i) y) T -
      uniformSeededTestProb T| ≤ (t : ℝ) * ε := by
  obtain ⟨q, witness, close⟩ := extract.weightedStrongSeededCondenser.block source
  exact weightedBlockTest_of_uniform_witness p _ source.probability q witness close T

end Algebraic.Cutwidth.Extractor.Internal
