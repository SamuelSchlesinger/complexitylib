/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite mass identities and total variation bounds

Normalization is preserved by marginals and deterministic maps. Total
variation contracts under deterministic maps and bounds every finite test.
For equal total mass, the positive-difference test attains the distance.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem probabilityWeight_exists_pos {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) : ∃ x, 0 < p x := by
  have nonzero : ∑ x, p x ≠ 0 := by rw [hp.2]; norm_num
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact ⟨x, lt_of_le_of_ne (hp.1 x) (Ne.symm hx)⟩

theorem probabilityWeight_le_one {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) (x : α) : p x ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun y _ => hp.1 y) (Finset.mem_univ x)

theorem probabilityWeight_first {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} (hp : IsProbabilityWeight p) : IsProbabilityWeight (firstWeight p) := by
  refine ⟨fun a => Finset.sum_nonneg fun b _ => hp.1 (a, b), ?_⟩
  simpa only [firstWeight, ← Fintype.sum_prod_type] using hp.2

theorem probabilityWeight_map {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f : α → β) :
    IsProbabilityWeight (mapWeight f p) := by
  refine ⟨fun b => Finset.sum_nonneg fun a _ => ?_, ?_⟩
  · split_ifs <;> first | exact hp.1 a | rfl
  · simpa [mapWeight, Finset.sum_comm] using hp.2

theorem probabilityWeight_uniform (α : Type*) [Fintype α] [Nonempty α] :
    IsProbabilityWeight (uniformWeight α) := by
  have positive : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  constructor
  · intro x
    exact inv_nonneg.mpr positive.le
  · simp [uniformWeight, ne_of_gt positive]

theorem mapWeight_id {α : Type*} [Fintype α] (p : α → ℝ) : mapWeight id p = p := by
  funext x
  simp [mapWeight]

theorem mapWeight_equiv_apply {α β : Type*} [Fintype α]
    (e : α ≃ β) (p : α → ℝ) (y : β) : mapWeight e p y = p (e.symm y) := by
  simp only [mapWeight, ← e.eq_symm_apply]
  simp

theorem mapWeight_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → γ) :
    mapWeight g (mapWeight f p) = mapWeight (fun x => g (f x)) p := by
  funext y
  simp only [mapWeight]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have swap (b : β) :
      (if g b = y then (if f x = b then p x else 0) else 0) =
        if f x = b then (if g b = y then p x else 0) else 0 := by
    by_cases h : f x = b <;> by_cases h' : g b = y <;> simp [h, h']
  simp_rw [swap]
  simp

theorem mapWeight_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) : mapWeight Prod.fst p = firstWeight p := by
  funext a
  rw [mapWeight, Fintype.sum_prod_type, Finset.sum_comm]
  simp [firstWeight]

theorem mapWeight_snd_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (b : β) : mapWeight Prod.snd p b = ∑ a, p (a, b) := by
  simp [mapWeight, Fintype.sum_prod_type]

theorem cappedWeight_card_le {α : Type*} [Fintype α] {p : α → ℝ} {K : Nat}
    (hp : IsProbabilityWeight p) (cap : CappedWeight p K) : K ≤ Fintype.card α := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => cap x)
  rw [← Finset.mul_sum, hp.2, mul_one] at h
  simpa using h

theorem cappedWeight_eq_uniform {α : Type*} [Fintype α] {p : α → ℝ}
    (cap : CappedWeight p (Fintype.card α)) (hp : IsProbabilityWeight p) :
    p = uniformWeight α := by
  obtain ⟨x, _⟩ := probabilityWeight_exists_pos hp
  let : Nonempty α := ⟨x⟩
  have positive : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have upper (a : α) : p a ≤ uniformWeight α a := by
    change p a ≤ (Fintype.card α : ℝ)⁻¹
    rw [← one_div]
    apply (le_div_iff₀ positive).mpr
    simpa only [mul_comm] using cap a
  have mass : ∑ a, (uniformWeight α a - p a) = 0 := by
    rw [Finset.sum_sub_distrib, (probabilityWeight_uniform α).2, hp.2, sub_self]
  funext a
  have zero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun b (_ : b ∈ (Finset.univ : Finset α)) => sub_nonneg.mpr (upper b))).mp mass a
      (Finset.mem_univ a)
  exact (sub_eq_zero.mp zero).symm

theorem weightDist_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) :
    0 ≤ weightDist p q := by
  unfold weightDist
  positivity

theorem weightDist_self {α : Type*} [Fintype α] (p : α → ℝ) : weightDist p p = 0 := by
  simp [weightDist]

theorem weightDist_comm {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = weightDist q p := by
  simp only [weightDist, abs_sub_comm]

theorem weightDist_triangle {α : Type*} [Fintype α] (p q r : α → ℝ) :
    weightDist p r ≤ weightDist p q + weightDist q r := by
  have bound := Finset.sum_le_sum
    (fun x (_ : x ∈ (Finset.univ : Finset α)) => abs_sub_le (p x) (q x) (r x))
  rw [Finset.sum_add_distrib] at bound
  unfold weightDist
  linarith

theorem weightDist_eq_zero_iff {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = 0 ↔ p = q := by
  constructor
  · intro zero
    have sumZero : ∑ x, |p x - q x| = 0 := by
      unfold weightDist at zero
      linarith
    funext x
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_ : y ∈ (Finset.univ : Finset α)) => abs_nonneg (p y - q y))).mp sumZero x
        (Finset.mem_univ x)
    exact sub_eq_zero.mp (abs_eq_zero.mp this)
  · rintro rfl
    exact weightDist_self p

theorem weightDist_le_one {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q) : weightDist p q ≤ 1 := by
  have bound : ∑ x, |p x - q x| ≤ ∑ x, (p x + q x) := by
    apply Finset.sum_le_sum
    intro x _
    exact (abs_sub (p x) (q x)).trans_eq (by rw [abs_of_nonneg (hp.1 x), abs_of_nonneg (hq.1 x)])
  rw [Finset.sum_add_distrib, hp.2, hq.2] at bound
  unfold weightDist
  linarith

theorem weightDist_map_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (f : α → β) : weightDist (mapWeight f p) (mapWeight f q) ≤ weightDist p q := by
  have bound (y : β) : |mapWeight f p y - mapWeight f q y| ≤
      ∑ x, if f x = y then |p x - q x| else 0 := by
    rw [mapWeight, mapWeight, ← Finset.sum_sub_distrib]
    convert Finset.abs_sum_le_sum_abs (fun x : α =>
      (if f x = y then p x else 0) - (if f x = y then q x else 0)) Finset.univ using 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  have total := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset β)) => bound y)
  have partition : (∑ y : β, ∑ x : α, if f x = y then |p x - q x| else 0) =
      ∑ x : α, |p x - q x| := by
    rw [Finset.sum_comm]
    simp
  rw [partition] at total
  unfold weightDist
  linarith

theorem weightTestProb_sub_le_dist {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) (T : Finset α) :
    |weightTestProb p T - weightTestProb q T| ≤ weightDist p q := by
  have balance : (∑ x ∈ T, (p x - q x)) + (∑ x ∈ Tᶜ, (p x - q x)) = 0 := by
    rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, mass, sub_self]
  have complement : |∑ x ∈ Tᶜ, (p x - q x)| = |∑ x ∈ T, (p x - q x)| := by
    have equality : (∑ x ∈ Tᶜ, (p x - q x)) = -(∑ x ∈ T, (p x - q x)) := by
      linarith
    rw [equality, abs_neg]
  have bound := add_le_add
    (Finset.abs_sum_le_sum_abs (fun x => p x - q x) T)
    (Finset.abs_sum_le_sum_abs (fun x => p x - q x) Tᶜ)
  rw [Finset.sum_add_sum_compl, complement] at bound
  unfold weightTestProb weightDist
  rw [← Finset.sum_sub_distrib]
  linarith

theorem weightDist_le_iff_tests {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) {ε : ℝ} :
    weightDist p q ≤ ε ↔ ∀ T : Finset α,
      |weightTestProb p T - weightTestProb q T| ≤ ε := by
  constructor
  · exact fun bound T => (weightTestProb_sub_le_dist p q mass T).trans bound
  · intro tests
    let T := (Finset.univ : Finset α).filter fun x => q x ≤ p x
    have posSum : ∑ x ∈ T, |p x - q x| = ∑ x ∈ T, (p x - q x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hx).2)
    have negSum : ∑ x ∈ Tᶜ, |p x - q x| = -(∑ x ∈ Tᶜ, (p x - q x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      apply abs_of_nonpos
      have h : ¬q x ≤ p x := by simpa only [T, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and] using hx
      exact sub_nonpos.mpr (le_of_lt (lt_of_not_ge h))
    have balance : (∑ x ∈ T, (p x - q x)) + (∑ x ∈ Tᶜ, (p x - q x)) = 0 := by
      rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, mass, sub_self]
    have attained : weightDist p q = weightTestProb p T - weightTestProb q T := by
      unfold weightDist weightTestProb
      rw [← Finset.sum_add_sum_compl T (fun x => |p x - q x|), posSum, negSum,
        ← Finset.sum_sub_distrib]
      linarith
    rw [attained]
    exact (le_abs_self _).trans (tests T)

theorem weightTestProb_map {α β : Type*} [Fintype α] (p : α → ℝ)
    (f : α → β) (T : Finset β) :
    weightTestProb (mapWeight f p) T = ∑ x, if f x ∈ T then p x else 0 := by
  unfold weightTestProb mapWeight
  rw [Finset.sum_comm]
  simp

theorem weightDist_map_map_le {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f g : α → β) :
    weightDist (mapWeight f p) (mapWeight g p) ≤ ∑ x with f x ≠ g x, p x := by
  apply (weightDist_le_iff_tests _ _
    ((probabilityWeight_map hp f).2.trans (probabilityWeight_map hp g).2.symm)).mpr
  intro T
  rw [weightTestProb_map, weightTestProb_map, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  by_cases same : f x = g x
  · simp [same]
  · by_cases hf : f x ∈ T <;> by_cases hg : g x ∈ T <;>
      simp [same, hf, hg, abs_of_nonneg (hp.1 x), hp.1 x]

end Algebraic.Cutwidth.Extractor.Internal
