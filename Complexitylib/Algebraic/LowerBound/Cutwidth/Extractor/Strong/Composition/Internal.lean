/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Composition.Internal.Tests
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Internal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# Composition through seedwise flat mixtures

A fresh independent extractor seed first preserves the condenser's test
error. Conditional flat witnesses then satisfy the strong extractor bound
for each original seed, and averaging the normalized mixture preserves that
bound. Both seeds are retained in the final tests.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem abs_uniform_average_sub_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ) {ε : ℝ} (close : ∀ i, |p i - q i| ≤ ε) :
    |(∑ i, p i) / Fintype.card ι - (∑ i, q i) / Fintype.card ι| ≤ ε := by
  have mass : (∑ _ : ι, ((Fintype.card ι : ℝ))⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  have average := abs_mixture_sub_le (fun _ : ι => (Fintype.card ι : ℝ)⁻¹)
    p q (fun _ => by positivity) mass close
  rw [← Finset.mul_sum, ← Finset.mul_sum] at average
  simpa only [div_eq_mul_inv, mul_comm] using average

theorem strong_extractor_embedding {α Fresh Z Ω : Type*}
    [Fintype α] [Nonempty α] [Fintype Fresh] [Fintype Ω]
    (g : α ↪ Z) (H : Z → Fresh → Ω) {K : Nat} {ε : ℝ}
    (extract : FlatStrongSeededExtractor H K ε) (size : K ≤ Fintype.card α)
    (T : Finset (Fresh × Ω)) :
    |seededTestProb (fun x a => H (g x) a) T - uniformSeededTestProb T| ≤ ε := by
  rw [seededTestProb_embedding g H T]
  apply extract (Finset.univ.map g)
  · exact Finset.univ_nonempty.map
  · simpa only [Finset.card_map, Finset.card_univ] using size

theorem strong_extractor_seedwise_embedding {α Seed Fresh Z Ω : Type*}
    [Fintype α] [Nonempty α] [Fintype Seed] [Nonempty Seed]
    [Fintype Fresh] [Fintype Ω] (g : Seed → (α ↪ Z)) (H : Z → Fresh → Ω)
    {K : Nat} {ε : ℝ} (extract : FlatStrongSeededExtractor H K ε)
    (size : K ≤ Fintype.card α) (T : Finset ((Seed × Fresh) × Ω)) :
    |seededTestProb (fun x ya => H (g ya.1 x) ya.2) T -
      uniformSeededTestProb T| ≤ ε := by
  rw [seededTestProb_comp_slice (fun y x => g y x) H T, uniformSeededTestProb_slice T]
  exact abs_uniform_average_sub_le _ _ fun y =>
    strong_extractor_embedding (g y) H extract size (compositionSlice T y)

theorem seededMixtureTestProb_comp_pullback {ι Seed Fresh Z Ω : Type*}
    [Fintype ι] [Fintype Seed] [Fintype Fresh] [Fintype Z]
    {Source : ι → Type*} [∀ i, Fintype (Source i)] (w : ι → ℝ)
    (C : ∀ i, Source i → Seed → Z) (H : Z → Fresh → Ω)
    (T : Finset ((Seed × Fresh) × Ω)) :
    seededMixtureTestProb w (fun i x ya => H (C i x ya.1) ya.2) T =
      (∑ a, seededMixtureTestProb w C (compositionPullback H T a)) /
        Fintype.card Fresh := by
  simp only [seededMixtureTestProb, seededTestProb_comp_pullback,
    ← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

theorem seededTestProb_comp_of_flat_mixture {α ι Seed Fresh Z Ω : Type*}
    [Fintype α] [Fintype ι] [Fintype Seed] [Nonempty Seed]
    [Fintype Fresh] [Nonempty Fresh] [Fintype Z] [Fintype Ω]
    {Source : ι → Type*} [∀ i, Fintype (Source i)]
    (C : α → Seed → Z) (H : Z → Fresh → Ω)
    (w : ι → ℝ) (g : ∀ i, Seed → (Source i ↪ Z))
    (nonnegative : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1)
    {K : Nat} (positive : 0 < K) (size : ∀ i, K ≤ Fintype.card (Source i))
    {δ ε : ℝ} (extract : FlatStrongSeededExtractor H K ε)
    (close : ∀ T : Finset (Seed × Z),
      |seededTestProb C T -
        seededMixtureTestProb w (fun i x y => g i y x) T| ≤ δ)
    (T : Finset ((Seed × Fresh) × Ω)) :
    |seededTestProb (fun x ya => H (C x ya.1) ya.2) T -
      uniformSeededTestProb T| ≤ δ + ε := by
  let G (i : ι) (x : Source i) (ya : Seed × Fresh) := H (g i ya.1 x) ya.2
  have first : |seededTestProb (fun x ya => H (C x ya.1) ya.2) T -
      seededMixtureTestProb w G T| ≤ δ := by
    rw [seededTestProb_comp_pullback C H T,
      seededMixtureTestProb_comp_pullback w (fun i x y => g i y x) H T]
    exact abs_uniform_average_sub_le _ _ fun a => close (compositionPullback H T a)
  have second : |seededMixtureTestProb w G T - uniformSeededTestProb T| ≤ ε := by
    have each (i : ι) : |seededTestProb (G i) T - uniformSeededTestProb T| ≤ ε := by
      let : Nonempty (Source i) := Fintype.card_pos_iff.mp (positive.trans_le (size i))
      exact strong_extractor_seedwise_embedding (g i) H extract (size i) T
    have average := abs_mixture_sub_le w (fun i => seededTestProb (G i) T)
      (fun _ => uniformSeededTestProb T) nonnegative mass each
    simpa only [← Finset.sum_mul, mass, one_mul, seededMixtureTestProb] using average
  exact (abs_sub_le _ (seededMixtureTestProb w G T) _).trans (add_le_add first second)

theorem flatStrongSeededExtractor_comp_of_flat_mixture {α Seed Fresh Z Ω : Type*}
    [Fintype Seed] [Nonempty Seed] [Fintype Fresh] [Nonempty Fresh]
    [Fintype Z] [Fintype Ω] (C : α → Seed → Z) (H : Z → Fresh → Ω)
    {K : Nat} (positive : 0 < K) {δ ε : ℝ}
    (extract : FlatStrongSeededExtractor H K ε)
    (lossless : ∀ P : Finset α, P.Nonempty → K ≤ P.card →
      ∃ g : ∀ S : P.powersetCard K, Seed → (S.val ↪ Z),
        ∀ T : Finset (Seed × Z),
          |seededTestProb (fun x : P => C x.val) T -
            seededMixtureTestProb (fun _ : P.powersetCard K =>
              ((P.powersetCard K).card : ℝ)⁻¹) (fun S x y => g S y x) T| ≤ δ) :
    FlatStrongSeededExtractor (fun x (ya : Seed × Fresh) => H (C x ya.1) ya.2)
      K (δ + ε) := by
  intro P nonempty threshold T
  obtain ⟨g, close⟩ := lossless P nonempty threshold
  have subset_pos : 0 < (P.powersetCard K).card := by
    simpa only [Finset.card_powersetCard] using Nat.choose_pos threshold
  have mass : (∑ _ : P.powersetCard K, ((P.powersetCard K).card : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  apply seededTestProb_comp_of_flat_mixture (fun x : P => C x.val) H
    (fun _ : P.powersetCard K => ((P.powersetCard K).card : ℝ)⁻¹) g
    (fun _ => by positivity) mass positive ?_ extract close T
  intro S
  rw [Fintype.card_coe, (Finset.mem_powersetCard.mp S.property).2]

end Algebraic.Cutwidth.Extractor.Internal
