/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite expansions of low-order sign moments

Repeated sign coordinates cancel in pairs. After separating those equality
patterns, the parity-bias assumption bounds each remaining term.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem mean_congr {α : Type*} {s : Finset α} {w X Y : α → ℝ}
    (h : ∀ a ∈ s, X a = Y a) : weightedMean s w X = weightedMean s w Y := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [h a ha]

private theorem mean_sum {α ι : Type*} [Fintype ι]
    (s : Finset α) (w : α → ℝ) (X : α → ι → ℝ) :
    weightedMean s w (fun a => ∑ i, X a i) =
      ∑ i, weightedMean s w (fun a => X a i) := by
  unfold weightedMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem abs_sum_le_mul {m : Nat} {f : Fin m → ℝ} {δ : ℝ}
    (h : ∀ i, |f i| ≤ δ) : |∑ i, f i| ≤ m * δ := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin m, δ := Finset.sum_le_sum fun i _ => h i
    _ = m * δ := by simp

private theorem bias_one {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (h : ParityBiasBound s w σ δ) (i : Fin m) :
    |weightedMean s w (fun a => σ a i)| ≤ δ := by
  simpa using h {i} (by simp) (by simp)

private theorem bias_two {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (h : ParityBiasBound s w σ δ)
    {i j : Fin m} (hij : i ≠ j) :
    |weightedMean s w (fun a => σ a i * σ a j)| ≤ δ := by
  simpa [Finset.prod_pair hij] using h {i, j} (by simp) (by simp [hij])

private theorem mean_sign_square {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1) (i : Fin m) :
    weightedMean s w (fun a => σ a i * σ a i) = 1 := by
  calc
    _ = weightedMean s w (fun _ => 1) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> norm_num
    _ = 1 := by simpa [weightedMean] using hmass

private theorem bias_two_centered {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) (i j : Fin m) :
    |weightedMean s w (fun a => σ a i * σ a j) - if i = j then 1 else 0| ≤ δ := by
  by_cases hij : i = j
  · subst j
    simpa [mean_sign_square hmass hσ] using hδ
  · simpa [hij] using bias_two h hij

theorem signSum_first_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (signSum σ)| ≤ m * δ := by
  change |weightedMean s w (fun a => ∑ i, σ a i)| ≤ m * δ
  rw [mean_sum]
  exact abs_sum_le_mul (bias_one h)

theorem signSum_second_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (fun a => signSum σ a ^ 2) - m| ≤ (m : ℝ) ^ 2 * δ := by
  have hexpand : weightedMean s w (fun a => signSum σ a ^ 2) =
      ∑ i, ∑ j, weightedMean s w (fun a => σ a i * σ a j) := by
    simp only [signSum, pow_two, Finset.sum_mul_sum, mean_sum]
  have hdiag : (∑ i : Fin m, ∑ j : Fin m, if i = j then (1 : ℝ) else 0) = m := by
    simp
  conv_lhs => rw [hexpand, ← hdiag, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ (m : ℝ) * (m * δ) :=
      abs_sum_le_mul fun i => abs_sum_le_mul (bias_two_centered hδ hmass hσ h i)
    _ = (m : ℝ) ^ 2 * δ := by ring

private theorem bias_three {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ}
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) (i j k : Fin m) :
    |weightedMean s w (fun a => σ a i * σ a j * σ a k)| ≤ δ := by
  by_cases hij : i = j
  · subst j
    have heq : weightedMean s w (fun a => σ a i * σ a i * σ a k) =
        weightedMean s w (fun a => σ a k) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_one h k
  by_cases hik : i = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a i) =
        weightedMean s w (fun a => σ a j) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_one h j
  by_cases hjk : j = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a j) =
        weightedMean s w (fun a => σ a i) := mean_congr fun a ha => by
      rcases hσ a ha j with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_one h i
  simpa [hij, hik, hjk, mul_assoc] using h {i, j, k} (by simp) (by simp [hij, hik, hjk])

private theorem indicator_nonneg (p : Prop) [Decidable p] :
    (0 : ℝ) ≤ if p then 1 else 0 := by
  split_ifs <;> norm_num

private theorem mean_four_le {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) (i j k l : Fin m) :
    weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a l) ≤
      δ + (if i = j ∧ k = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0) := by
  by_cases hij : i = j
  · subst j
    have heq : weightedMean s w (fun a => σ a i * σ a i * σ a k * σ a l) =
        weightedMean s w (fun a => σ a k * σ a l) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    simp only [true_and]
    have hkl := (abs_le.mp (bias_two_centered hδ hmass hσ h k l)).2
    have h2 := indicator_nonneg (i = k ∧ i = l)
    have h3 := indicator_nonneg (i = l ∧ i = k)
    linarith
  by_cases hik : i = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a i * σ a l) =
        weightedMean s w (fun a => σ a j * σ a l) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    simp only [hij, false_and, ite_false, add_zero, true_and]
    have hjl := (abs_le.mp (bias_two_centered hδ hmass hσ h j l)).2
    have h3 := indicator_nonneg (i = l ∧ j = i)
    linarith
  by_cases hil : i = l
  · subst l
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a i) =
        weightedMean s w (fun a => σ a j * σ a k) := mean_congr fun a ha => by
      rcases hσ a ha i with h | h <;> rw [h] <;> ring
    rw [heq]
    simp only [hij, hik, false_and, ite_false, add_zero, true_and]
    have hjk := (abs_le.mp (bias_two_centered hδ hmass hσ h j k)).2
    linarith
  simp only [hij, hik, hil, false_and, ite_false, add_zero]
  apply (le_abs_self _).trans
  by_cases hjk : j = k
  · subst k
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a j * σ a l) =
        weightedMean s w (fun a => σ a i * σ a l) := mean_congr fun a ha => by
      rcases hσ a ha j with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_two h hil
  by_cases hjl : j = l
  · subst l
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a j) =
        weightedMean s w (fun a => σ a i * σ a k) := mean_congr fun a ha => by
      rcases hσ a ha j with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_two h hik
  by_cases hkl : k = l
  · subst l
    have heq : weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a k) =
        weightedMean s w (fun a => σ a i * σ a j) := mean_congr fun a ha => by
      rcases hσ a ha k with h | h <;> rw [h] <;> ring
    rw [heq]
    exact bias_two h hij
  simpa [hij, hik, hil, hjk, hjl, hkl, mul_assoc] using
    h {i, j, k, l} (by simp) (by simp [hij, hik, hil, hjk, hjl, hkl])

theorem signSum_third_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ}
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (fun a => signSum σ a ^ 3)| ≤ (m : ℝ) ^ 3 * δ := by
  have hexpand : weightedMean s w (fun a => signSum σ a ^ 3) =
      ∑ i, ∑ j, ∑ k, weightedMean s w (fun a => σ a i * σ a j * σ a k) := by
    simp only [signSum, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum, mean_sum]
    simp only [mul_comm, mul_left_comm]
  rw [hexpand]
  calc
    _ ≤ (m : ℝ) * (m * (m * δ)) :=
      abs_sum_le_mul fun i => abs_sum_le_mul fun j => abs_sum_le_mul (bias_three hσ h i j)
    _ = (m : ℝ) ^ 3 * δ := by ring

theorem signSum_fourth_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    weightedMean s w (fun a => signSum σ a ^ 4) ≤
      3 * (m : ℝ) ^ 2 + (m : ℝ) ^ 4 * δ := by
  have hexpand : weightedMean s w (fun a => signSum σ a ^ 4) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        weightedMean s w (fun a => σ a i * σ a j * σ a k * σ a l) := by
    simp only [signSum, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum, mean_sum]
    simp only [mul_comm, mul_left_comm]
  rw [hexpand]
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ l : Fin m,
        (δ + (if i = j ∧ k = l then 1 else 0) +
          (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          mean_four_le hδ hmass hσ h i j k l
    _ = 3 * (m : ℝ) ^ 2 + (m : ℝ) ^ 4 * δ := by
      simp only [Finset.sum_add_distrib]
      simp [ite_and]
      ring

end Algebraic.Cutwidth.Extractor.Internal
