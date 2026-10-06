/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Internal.Rectangle
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Correlation through rectangle classes

Suppose the inputs are partitioned into classes, each a rectangle for one fixed cut `X`, and a
predictor `g` is constant on every class. Lindsey's lemma bounds the signed sum of the
quadratic form on each class, and Cauchy–Schwarz over the classes gives

`(2 · agreement(f, g) - 1)² · 2^{cutRank Q X} ≤ #classes`.
-/

@[expose] public section

namespace Complexity.Correlation

open Finset Complexity.Frontier

variable {α : Type*}

/-- Twice the agreement minus one is the normalized signed correlation. -/
theorem two_mul_agreement_sub_one [Fintype α] [Nonempty α] (f g : α → Bool) :
    2 * agreement f g - 1 = (∑ x, boolSign (f x) * boolSign (g x)) / Fintype.card α := by
  have h := sign_sum_eq f g
  have huniv : (Set.toFinite (Set.univ : Set α)).toFinset = Finset.univ := by
    ext x; simp
  have hsum : sumOn (fun x => boolSign (f x) * boolSign (g x)) Set.univ =
      ∑ x, boolSign (f x) * boolSign (g x) := by
    unfold sumOn
    rw [huniv]
  have hpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [hsum, Nat.card_eq_fintype_card] at h
  unfold agreement
  rw [h, Nat.card_eq_fintype_card]
  field_simp

/-- **Cauchy–Schwarz over classes.** If the squared sum over every class is at most its size
times `Λ`, the squared total is at most the number of classes times `|α| Λ`. -/
theorem sq_sum_le_of_classes [Fintype α] {M : Type*} [Fintype M] [DecidableEq M]
    (w : α → ℝ) (msg : α → M) (Λ : ℝ)
    (h : ∀ x₀, (∑ x ∈ univ.filter (fun x => msg x = msg x₀), w x) ^ 2 ≤
      (univ.filter (fun x => msg x = msg x₀)).card * Λ) :
    (∑ x, w x) ^ 2 ≤ Fintype.card M * (Fintype.card α * Λ) := by
  have hfib : ∀ μ : M, (∑ x ∈ univ.filter (fun x => msg x = μ), w x) ^ 2 ≤
      (univ.filter (fun x => msg x = μ)).card * Λ := by
    intro μ
    by_cases hμ : ∃ x₀, msg x₀ = μ
    · obtain ⟨x₀, rfl⟩ := hμ
      exact h x₀
    · push Not at hμ
      have : univ.filter (fun x => msg x = μ) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun x _ => hμ x
      simp [this]
  rw [← Finset.sum_fiberwise univ msg w]
  calc (∑ μ : M, ∑ x ∈ univ.filter (fun x => msg x = μ), w x) ^ 2
      ≤ (univ : Finset M).card * ∑ μ : M, (∑ x ∈ univ.filter (fun x => msg x = μ), w x) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (univ : Finset M).card * ∑ μ : M, (univ.filter (fun x => msg x = μ)).card * Λ := by
        gcongr with μ
        exact hfib μ
    _ = Fintype.card M * (Fintype.card α * Λ) := by
        rw [← Finset.sum_mul, Finset.card_univ]
        congr 2
        have := Finset.card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := msg)
          (fun _ _ => mem_univ _)
        rw [Finset.card_univ] at this
        exact_mod_cast this.symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Correlation through rectangle classes.** Let every class of `msg` be a rectangle for the
cut `X`, and let `g` be constant on the classes. Then the correlation of `g` with the quadratic
form of `Q` satisfies `(2 · agreement - 1)² · 2^{cutRank Q X} ≤ |M|`. -/
theorem sq_two_mul_agreement_sub_one_mul_le (Q : Matrix ι ι (ZMod 2)) (g : (ι → Bool) → Bool)
    {M : Type*} [Fintype M] [DecidableEq M] (msg : (ι → Bool) → M) (X : Set ι)
    (hg : ∀ x y, msg x = msg y → g x = g y)
    (hrect : ∀ x₀, ∃ (A : Set (X → Bool)) (B : Set (↥Xᶜ → Bool)),
      {x | msg x = msg x₀} = rectangle X A B) :
    (2 * agreement (quadForm Q) g - 1) ^ 2 * 2 ^ cutRank Q X ≤ Fintype.card M := by
  classical
  have hN : (Fintype.card (ι → Bool) : ℝ) = 2 ^ Fintype.card ι := by
    simp [Fintype.card_bool]
  have hρ : (0 : ℝ) < 2 ^ cutRank Q X := by positivity
  set Λ : ℝ := 2 ^ Fintype.card ι / 2 ^ cutRank Q X
  have hclass : ∀ x₀, (∑ x ∈ univ.filter (fun x => msg x = msg x₀),
      boolSign (quadForm Q x) * boolSign (g x)) ^ 2 ≤
        (univ.filter (fun x => msg x = msg x₀)).card * Λ := by
    intro x₀
    obtain ⟨A, B, hAB⟩ := hrect x₀
    have hs : ∀ x, x ∈ univ.filter (fun x => msg x = msg x₀) ↔
        X.domRestrict x ∈ (Set.toFinite A).toFinset ∧
          Xᶜ.domRestrict x ∈ (Set.toFinite B).toFinset := by
      intro x
      simp only [mem_filter, mem_univ, true_and, Set.Finite.mem_toFinset]
      change x ∈ {x | msg x = msg x₀} ↔ _
      rw [hAB]
      rfl
    have hL := sq_sum_boolSign_quadForm_mul_le Q hs
    have hconst : ∑ x ∈ univ.filter (fun x => msg x = msg x₀),
        boolSign (quadForm Q x) * boolSign (g x) =
          boolSign (g x₀) * ∑ x ∈ univ.filter (fun x => msg x = msg x₀),
            boolSign (quadForm Q x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hg x x₀ (mem_filter.mp hx).2, mul_comm]
    rw [hconst, mul_pow, ← sq_abs (boolSign _), abs_boolSign, one_pow, one_mul]
    simp only [Λ]
    rw [mul_div_assoc', le_div_iff₀ hρ]
    exact hL
  have H := sq_sum_le_of_classes _ msg Λ hclass
  have hΛ : Λ * 2 ^ cutRank Q X = Fintype.card (ι → Bool) := by
    simp only [Λ]
    rw [hN]
    field_simp
  have hpos : (0 : ℝ) < Fintype.card (ι → Bool) := by rw [hN]; positivity
  rw [two_mul_agreement_sub_one, div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc (∑ x, boolSign (quadForm Q x) * boolSign (g x)) ^ 2 * 2 ^ cutRank Q X
      ≤ Fintype.card M * (Fintype.card (ι → Bool) * Λ) * 2 ^ cutRank Q X :=
        mul_le_mul_of_nonneg_right H hρ.le
    _ = Fintype.card M * (Fintype.card (ι → Bool) : ℝ) ^ 2 := by
        rw [mul_assoc, mul_assoc, hΛ]
        ring

end Complexity.Correlation
