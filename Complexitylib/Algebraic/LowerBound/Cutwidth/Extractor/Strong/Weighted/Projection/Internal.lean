/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Equiv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Projecting weighted strong-extractor outputs

Threshold monotonicity uses source nonnegativity directly. Product projection
pulls a joint test back to its product with the discarded alphabet, so the
uniform comparison is unchanged. Splitting a Boolean vector into a prefix
and suffix then gives exact prefix truncation.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_mono_threshold {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    {E : α → Seed → Ω} {K L : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (threshold : K ≤ L) :
    WeightedStrongSeededExtractor E L ε := by
  intro p probability cap T
  apply extract p probability _ T
  intro x
  exact (mul_le_mul_of_nonneg_right
    (by exact_mod_cast threshold) (probability.1 x)).trans (cap x)

theorem weightedStrongSeededExtractor_fst {α Seed Ω Tail : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Fintype Tail] [Nonempty Tail]
    {E : α → Seed → Ω × Tail} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededExtractor (fun a y => (E a y).1) K ε := by
  classical
  intro p probability cap T
  let pull := (T.product (Finset.univ : Finset Tail)).map
    (Equiv.prodAssoc Seed Ω Tail).toEmbedding
  have actual : weightedSeededTestProb p E pull =
      weightedSeededTestProb p (fun a y => (E a y).1) T := by
    simp [weightedSeededTestProb, pull]
  have uniform : uniformSeededTestProb pull = uniformSeededTestProb T := by
    have positive : (Fintype.card Tail : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := Tail)
    simp only [pull, uniformSeededTestProb, Finset.card_map,
      Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
      Fintype.card_prod, Nat.cast_mul]
    rw [← mul_assoc, mul_div_mul_right _ _ positive]
  simpa only [actual, uniform] using extract p probability cap pull

private def splitEquiv (b r : Nat) : (Fin (b + r) → Bool) ≃
    (Fin b → Bool) × (Fin r → Bool) :=
  ((finSumFinEquiv : Fin b ⊕ Fin r ≃ Fin (b + r)).symm.arrowCongr
    (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

private theorem prefix_add {α Seed : Type*} [Fintype α] [Fintype Seed]
    {b r K : Nat} {ε : ℝ} {E : α → Seed → Fin (b + r) → Bool}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededExtractor
      (fun a y (j : Fin b) => E a y (Fin.castAdd r j)) K ε := by
  have transported := extract.equiv (Equiv.refl Seed) (splitEquiv b r)
  have projected := weightedStrongSeededExtractor_fst
    (Ω := Fin b → Bool) (Tail := Fin r → Bool) transported
  have mapping : (fun a y => (splitEquiv b r (E a y)).1) =
      (fun a y (j : Fin b) => E a y (Fin.castAdd r j)) := by
    funext a y j
    rfl
  simp only [Equiv.refl_apply] at projected
  rw [mapping] at projected
  exact projected

theorem weightedStrongSeededExtractor_truncate {α Seed : Type*}
    [Fintype α] [Fintype Seed]
    {b M K : Nat} {ε : ℝ} {E : α → Seed → Fin M → Bool}
    (extract : WeightedStrongSeededExtractor E K ε) (size : b ≤ M) :
    WeightedStrongSeededExtractor
      (fun a y (j : Fin b) => E a y (Fin.castLE size j)) K ε := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le size
  exact prefix_add extract

end Algebraic.Cutwidth.Extractor.Internal
