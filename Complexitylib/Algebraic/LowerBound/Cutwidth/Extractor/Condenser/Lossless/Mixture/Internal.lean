/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subset averaging and preservation of test discrepancy

Every point of a finite support lies in the same number of its subsets of
a fixed positive size. Double counting gives exact averaging over these
subsets. Nonnegative normalized mixtures preserve a common test-discrepancy
bound by the triangle inequality.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem sum_powersetCard_sum {α M : Type*} [AddCommMonoid M]
    (P : Finset α) {K : Nat} (positive : 0 < K) (f : α → M) :
    ∑ S ∈ P.powersetCard K, ∑ x ∈ S, f x =
      (P.card - 1).choose (K - 1) • ∑ x ∈ P, f x := by
  calc
    _ = ∑ S ∈ P.powersetCard K, ∑ x ∈ P, if x ∈ S then f x else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hS).1]
    _ = ∑ x ∈ P, ∑ S ∈ P.powersetCard K, if x ∈ S then f x else 0 :=
      Finset.sum_comm
    _ = ∑ x ∈ P, (P.card - 1).choose (K - 1) • f x := by
      apply Finset.sum_congr rfl
      intro x hx
      have count := Finset.card_filter_powersetCard_subset {x} P K
        (Finset.singleton_subset_iff.mpr hx)
        (by simpa only [Finset.card_singleton] using Nat.succ_le_of_lt positive)
      rw [← Finset.sum_filter, Finset.sum_const]
      simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
        congrArg (fun n : Nat => n • f x) count
    _ = _ := Finset.sum_nsmul P _ f

theorem seededTestProb_eq_sum {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    (C : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    seededTestProb C T =
      (∑ x, ((Finset.univ.filter fun y => (y, C x y) ∈ T).card : ℝ)) /
        ((Fintype.card α : ℝ) * Fintype.card Seed) := by
  unfold seededTestProb
  congr 1
  rw [Finset.card_filter, Fintype.sum_prod_type, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]

theorem seededTestProb_support_eq_sum {α Seed Ω : Type*} [Fintype Seed]
    (C : α → Seed → Ω) (P : Finset α) (T : Finset (Seed × Ω)) :
    seededTestProb (fun x : P => C x.val) T =
      (∑ x ∈ P, ((Finset.univ.filter fun y => (y, C x y) ∈ T).card : ℝ)) /
        ((P.card : ℝ) * Fintype.card Seed) := by
  rw [seededTestProb_eq_sum, Fintype.card_coe, Finset.univ_eq_attach]
  congr 1
  exact Finset.sum_attach P (fun x =>
    ((Finset.univ.filter fun y => (y, C x y) ∈ T).card : ℝ))

theorem powersetCard_average {α : Type*} (P : Finset α) {K : Nat}
    (positive : 0 < K) (size : K ≤ P.card) (f : α → ℝ) :
    (∑ S ∈ P.powersetCard K, (∑ x ∈ S, f x) / (K : ℝ)) /
      (P.powersetCard K).card = (∑ x ∈ P, f x) / (P.card : ℝ) := by
  have source_pos : 0 < P.card := positive.trans_le size
  have subset_pos : 0 < (P.powersetCard K).card := by
    simpa only [Finset.card_powersetCard] using Nat.choose_pos size
  have count : (P.card : ℝ) * ((P.card - 1).choose (K - 1) : ℝ) =
      ((P.powersetCard K).card : ℝ) * K := by
    have identity := Nat.add_one_mul_choose_eq (P.card - 1) (K - 1)
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt source_pos),
      Nat.sub_add_cancel (Nat.succ_le_of_lt positive)] at identity
    exact_mod_cast (by simpa only [Finset.card_powersetCard] using identity)
  rw [← Finset.sum_div, sum_powersetCard_sum P positive f, nsmul_eq_mul, div_div]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  calc
    _ = (∑ x ∈ P, f x) *
        ((P.card : ℝ) * ((P.card - 1).choose (K - 1) : ℝ)) := by ring
    _ = (∑ x ∈ P, f x) * (((P.powersetCard K).card : ℝ) * K) := by rw [count]
    _ = _ := by ring

theorem seededTestProb_powersetCard {α Seed Ω : Type*} [Fintype Seed]
    (C : α → Seed → Ω) (P : Finset α) {K : Nat}
    (positive : 0 < K) (size : K ≤ P.card) (T : Finset (Seed × Ω)) :
    seededTestProb (fun x : P => C x.val) T =
      (∑ S : P.powersetCard K, seededTestProb (fun x : S.val => C x.val) T) /
        (P.powersetCard K).card := by
  let hits (x : α) := ((Finset.univ.filter fun y => (y, C x y) ∈ T).card : ℝ)
  have component (S : P.powersetCard K) :
      seededTestProb (fun x : S.val => C x.val) T =
        ((∑ x ∈ S.val, hits x) / (K : ℝ)) / Fintype.card Seed := by
    rw [seededTestProb_support_eq_sum, (Finset.mem_powersetCard.mp S.property).2, div_div]
  symm
  calc
    _ = ((∑ S : P.powersetCard K, (∑ x ∈ S.val, hits x) / (K : ℝ)) /
        Fintype.card Seed) / (P.powersetCard K).card := by
      simp_rw [component]
      rw [← Finset.sum_div]
    _ = ((∑ S ∈ P.powersetCard K, (∑ x ∈ S, hits x) / (K : ℝ)) /
        (P.powersetCard K).card) / Fintype.card Seed := by
      rw [Finset.univ_eq_attach, div_right_comm]
      exact congrArg (fun z : ℝ => z / (P.powersetCard K).card / Fintype.card Seed)
        (Finset.sum_attach (P.powersetCard K)
          (fun S : Finset α => (∑ x ∈ S, hits x) / (K : ℝ)))
    _ = ((∑ x ∈ P, hits x) / (P.card : ℝ)) / Fintype.card Seed := by
      rw [powersetCard_average P positive size hits]
    _ = _ := by rw [seededTestProb_support_eq_sum, div_div]

theorem abs_mixture_sub_le {ι : Type*} [Fintype ι] (w p q : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1) {ε : ℝ}
    (close : ∀ i, |p i - q i| ≤ ε) :
    |(∑ i, w i * p i) - ∑ i, w i * q i| ≤ ε := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ i, |w i * (p i - q i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |p i - q i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (nonnegative i)]
    _ ≤ ∑ i, w i * ε :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (close i) (nonnegative i)
    _ = ε := by rw [← Finset.sum_mul, mass, one_mul]

theorem seededMixtureTestProb_sub_le {ι Seed Ω : Type*} [Fintype ι] [Fintype Seed]
    {Source Target : ι → Type*} [∀ i, Fintype (Source i)] [∀ i, Fintype (Target i)]
    (w : ι → ℝ) (C : ∀ i, Source i → Seed → Ω) (G : ∀ i, Target i → Seed → Ω)
    (nonnegative : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1) {ε : ℝ}
    (close : ∀ i, ∀ T : Finset (Seed × Ω),
      |seededTestProb (C i) T - seededTestProb (G i) T| ≤ ε) :
    ∀ T : Finset (Seed × Ω),
      |seededMixtureTestProb w C T - seededMixtureTestProb w G T| ≤ ε := by
  intro T
  exact abs_mixture_sub_le w (fun i => seededTestProb (C i) T)
    (fun i => seededTestProb (G i) T) nonnegative mass (fun i => close i T)

theorem seededTestProb_eq_uniformMixture {α Seed Ω : Type*} [Fintype Seed]
    (C : α → Seed → Ω) (P : Finset α) {K : Nat}
    (positive : 0 < K) (size : K ≤ P.card) (T : Finset (Seed × Ω)) :
    seededTestProb (fun x : P => C x.val) T =
      seededMixtureTestProb (fun _ : P.powersetCard K =>
        ((P.powersetCard K).card : ℝ)⁻¹)
        (fun (S : P.powersetCard K) (x : S.val) => C x.val) T := by
  rw [seededTestProb_powersetCard C P positive size T, seededMixtureTestProb,
    ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem exists_flat_mixture_of_exact_size {α Seed Ω : Type*} [Fintype Seed]
    (C : α → Seed → Ω) (P : Finset α) {K : Nat}
    (positive : 0 < K) (size : K ≤ P.card) {ε : ℝ}
    (lossless : ∀ S : Finset α, S ⊆ P → S.card = K →
      ∃ g : Seed → (S ↪ Ω), ∀ T : Finset (Seed × Ω),
        |seededTestProb (fun x : S => C x.val) T -
          seededTestProb (fun x y => g y x) T| ≤ ε) :
    ∃ g : ∀ S : P.powersetCard K, Seed → (S.val ↪ Ω),
      ∀ T : Finset (Seed × Ω),
        |seededTestProb (fun x : P => C x.val) T -
          seededMixtureTestProb (fun _ : P.powersetCard K =>
            ((P.powersetCard K).card : ℝ)⁻¹)
            (fun S x y => g S y x) T| ≤ ε := by
  have components (S : P.powersetCard K) := lossless S.val
    (Finset.mem_powersetCard.mp S.property).1 (Finset.mem_powersetCard.mp S.property).2
  choose g hg using components
  have subset_pos : 0 < (P.powersetCard K).card := by
    simpa only [Finset.card_powersetCard] using Nat.choose_pos size
  have mass : (∑ _ : P.powersetCard K, ((P.powersetCard K).card : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  refine ⟨g, fun T => ?_⟩
  rw [seededTestProb_eq_uniformMixture C P positive size T]
  exact seededMixtureTestProb_sub_le _ _ _ (fun _ => by positivity) mass hg T

end Algebraic.Cutwidth.Extractor.Internal
