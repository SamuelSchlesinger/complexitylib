/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep

/-!
# Final extraction after a retained-seed approximation

Full-entropy block witnesses are uniform. Averaging the shared-seed block
extraction bound over the earlier seed gives an ideal final joint law close
to uniform. A previous joint approximation error survives adding the fresh
independent seed and applying the extractor by distance contraction.

This is finite statistical composition of the shared-seed block argument
in Chattopadhyay--Goodman--Liao, Lemma 5.5 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem blockExtraction_uniform_seedFamily {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] :
    seedFamilyWeight (fun _ : Seed => uniformWeight Ω) = uniformWeight (Seed × Ω) := by
  funext yz
  simp [seedFamilyWeight, uniformWeight, Fintype.card_prod, div_eq_mul_inv, mul_comm]

private theorem blockExtraction_fiber_dist {α Fresh Ω : Type*}
    [Fintype α] [Fintype Fresh] [Fintype Ω] [Nonempty Fresh] [Nonempty Ω]
    {E : α → Fresh → Ω} {K t : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) :
    weightDist (weightedSeededOutput p (fun x y i => E (x i) y))
      (seedFamilyWeight (fun _ : Fresh => uniformWeight (Fin t → Ω))) ≤ (t : ℝ) * ε := by
  obtain ⟨q, witness, close⟩ := extract.weightedStrongSeededCondenser.block source
  have uniform : q = fun _ => uniformWeight (Fin t → Ω) :=
    funext fun y => (witness y).eq_uniform
  rwa [uniform] at close

private theorem blockExtraction_ideal_dist {Earlier Fresh α Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype α] [Fintype Ω]
    [Nonempty Earlier] [Nonempty Fresh] [Nonempty Ω]
    {E : α → Fresh → Ω} {K t : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    (p : Earlier → (Fin t → α) → ℝ) (source : ∀ y, IsBlockSource (p y) K) :
    weightDist (retainedSeedStep (fun _ x y i => E (x i) y) (seedFamilyWeight p))
      (uniformWeight ((Earlier × Fresh) × (Fin t → Ω))) ≤ (t : ℝ) * ε := by
  rw [retainedSeedStep_seedFamilyWeight, ← blockExtraction_uniform_seedFamily]
  change weightDist
    (seedFamilyWeight (fun sy : Earlier × Fresh =>
      mapWeight (fun x : Fin t → α => fun i => E (x i) sy.2) (p sy.1)))
    (seedFamilyWeight (fun sy : Earlier × Fresh =>
      (fun _ : Earlier => fun _ : Fresh => uniformWeight (Fin t → Ω)) sy.1 sy.2)) ≤ _
  rw [weightDist_seedFamilyWeight_product
    (fun s y => mapWeight (fun x : Fin t → α => fun i => E (x i) y) (p s))
    (fun _ _ => uniformWeight (Fin t → Ω))]
  have positive : (0 : ℝ) < Fintype.card Earlier :=
    Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ positive).mpr
  calc
    _ ≤ ∑ _y : Earlier, (t : ℝ) * ε := by
      apply Finset.sum_le_sum
      intro y _
      exact blockExtraction_fiber_dist extract (source y)
    _ = _ := by simp [mul_comm]

theorem weightedStrongSeededExtractor_retained_block {Earlier Fresh α Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype α] [Fintype Ω]
    [Nonempty Earlier] [Nonempty Fresh] [Nonempty Ω]
    {E : α → Fresh → Ω} {K t : Nat} {ε η : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    (p : Earlier → (Fin t → α) → ℝ) (actual : Earlier × (Fin t → α) → ℝ)
    (source : ∀ y, IsBlockSource (p y) K)
    (close : weightDist actual (seedFamilyWeight p) ≤ η) :
    weightDist (retainedSeedStep (fun _ x y i => E (x i) y) actual)
      (uniformWeight ((Earlier × Fresh) × (Fin t → Ω))) ≤ η + (t : ℝ) * ε := by
  refine (weightDist_triangle _
    (retainedSeedStep (fun _ x y i => E (x i) y) (seedFamilyWeight p)) _).trans ?_
  exact add_le_add ((retainedSeedStep_dist_le _ actual (seedFamilyWeight p)).trans close)
    (blockExtraction_ideal_dist extract p source)

theorem weightedStrongSeededExtractor_retained_block_tests {Earlier Fresh α Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype α] [Fintype Ω]
    [Nonempty Earlier] [Nonempty Fresh] [Nonempty Ω]
    {E : α → Fresh → Ω} {K t : Nat} {ε η : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    (p : Earlier → (Fin t → α) → ℝ) (actual : Earlier × (Fin t → α) → ℝ)
    (probability : IsProbabilityWeight actual) (source : ∀ y, IsBlockSource (p y) K)
    (close : weightDist actual (seedFamilyWeight p) ≤ η)
    (T : Finset ((Earlier × Fresh) × (Fin t → Ω))) :
    |weightTestProb (retainedSeedStep (fun _ x y i => E (x i) y) actual) T -
      uniformSeededTestProb T| ≤ η + (t : ℝ) * ε := by
  have output := probability.retainedSeedStep (fun _ x y i => E (x i) y)
  have uniform := isProbabilityWeight_uniform ((Earlier × Fresh) × (Fin t → Ω))
  have tests := weightTestProb_sub_le_dist _ _ (output.2.trans uniform.2.symm) T
  have uniformTest : weightTestProb
      (uniformWeight ((Earlier × Fresh) × (Fin t → Ω))) T = uniformSeededTestProb T := by
    rw [← blockExtraction_uniform_seedFamily, weightTestProb_seedFamilyWeight_uniform]
  rw [uniformTest] at tests
  exact tests.trans (weightedStrongSeededExtractor_retained_block extract p actual source close)

end Algebraic.Cutwidth.Extractor.Internal
