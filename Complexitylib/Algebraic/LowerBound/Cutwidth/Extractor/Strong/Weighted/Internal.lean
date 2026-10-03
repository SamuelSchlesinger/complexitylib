/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.FlatMixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Internal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Extending strong extraction from flat to weighted sources

Seeded test probabilities are linear in the source weights. The exact
decomposition into uniform fixed-size supports therefore transfers the
flat-source guarantee without any error loss. Conversely every nonempty
flat support is a normalized capped weighting on the ambient finite type.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem probabilityWeight_flatWeight {α : Type*} [Fintype α]
    (P : Finset α) (nonempty : P.Nonempty) : IsProbabilityWeight (flatWeight P) := by
  have positive : (0 : ℝ) < P.card := by exact_mod_cast nonempty.card_pos
  constructor
  · intro x
    unfold flatWeight
    split_ifs <;> positivity
  · simp only [flatWeight, Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ positive.ne'

theorem cappedWeight_flatWeight {α : Type*} (P : Finset α) {K : Nat}
    (size : K ≤ P.card) : CappedWeight (flatWeight P) K := by
  intro x
  unfold flatWeight
  split_ifs with member
  · have positive : (0 : ℝ) < P.card := by
      exact_mod_cast (Finset.card_pos.mpr ⟨x, member⟩)
    rw [← div_eq_mul_inv]
    exact (div_le_one positive).mpr (by exact_mod_cast size)
  · simp

theorem weightedSeededTestProb_uniformWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (E : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    weightedSeededTestProb (uniformWeight α) E T = seededTestProb E T := by
  rw [weightedSeededTestProb, seededTestProb_eq_sum]
  simp only [uniformWeight, ← Finset.mul_sum, div_eq_mul_inv, mul_inv_rev]
  ring

theorem weightedSeededTestProb_flatWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (E : α → Seed → Ω) (P : Finset α)
    (T : Finset (Seed × Ω)) :
    weightedSeededTestProb (flatWeight P) E T = seededTestProb (fun x : P => E x.val) T := by
  rw [weightedSeededTestProb, seededTestProb_support_eq_sum]
  simp only [flatWeight, ite_mul, zero_mul, Finset.sum_ite_mem_eq, ← Finset.mul_sum,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem weightedSeededTestProb_mixture {α ι Seed Ω : Type*}
    [Fintype α] [Fintype ι] [Fintype Seed]
    (w : ι → ℝ) (p : ι → α → ℝ) (E : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    weightedSeededTestProb (fun x => ∑ i, w i * p i x) E T =
      ∑ i, w i * weightedSeededTestProb (p i) E T := by
  simp only [weightedSeededTestProb, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, mul_div_assoc]

theorem weightedStrong_of_flat {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (positive : 0 < K) :
    WeightedStrongSeededExtractor E K ε := by
  intro p hp cap T
  obtain ⟨w, nonnegative, mass, mixture⟩ :=
    exists_flat_mixture_of_capped_weights p positive hp.1 hp.2 cap
  have identity : p = fun x => ∑ S : {S : Finset α // S.card = K}, w S * flatWeight S.val x := by
    funext x
    have card (S : {S : Finset α // S.card = K}) : S.val.card = K := S.property
    simpa only [flatWeight, card] using mixture x
  rw [identity, weightedSeededTestProb_mixture]
  have baseline : ∑ S, w S * uniformSeededTestProb T = uniformSeededTestProb T := by
    rw [← Finset.sum_mul, mass, one_mul]
  rw [← baseline]
  apply abs_mixture_sub_le w _ _ nonnegative mass
  intro S
  rw [weightedSeededTestProb_flatWeight]
  apply extract S.val
  · exact Finset.card_pos.mp (by simpa only [S.property] using positive)
  · exact S.property.ge

theorem flatStrong_of_weighted {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) : FlatStrongSeededExtractor E K ε := by
  intro P nonempty size T
  have bound := extract (flatWeight P) (probabilityWeight_flatWeight P nonempty)
    (cappedWeight_flatWeight P size) T
  simpa only [weightedSeededTestProb_flatWeight] using bound

end Algebraic.Cutwidth.Extractor.Internal
