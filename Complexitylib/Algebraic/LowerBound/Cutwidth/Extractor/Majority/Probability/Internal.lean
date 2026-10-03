/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Tails

/-!
# Weighted majority from selected sign coordinates

The selected coordinates are indexed by an embedding, so their sign sum is
the existing integer vote margin. The remaining coordinates may depend
arbitrarily on the selected ones; only their number enters the margin bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem signSum_eq_voteMargin {α : Type*} {m n : Nat}
    (good : Fin m ↪ Fin n) (x : α → Fin n → Bool) (a : α) :
    signSum (fun a i => if x a (good i) then 1 else -1) a =
      (voteMargin (Finset.univ.map good) (x a) : ℝ) := by
  unfold signSum
  calc
    _ = ∑ i, (2 * (if x a (good i) then (1 : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : x a (good i) <;> norm_num [h]
    _ = 2 * ((Finset.univ.filter fun i => x a (good i) = true).card : ℝ) - m := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = _ := by simp [voteMargin, Finset.filter_map]

theorem majority_eq_true_of_signSum {α : Type*} {m n : Nat} (good : Fin m ↪ Fin n)
    (x : α → Fin n → Bool) (a : α)
    (margin : (n - m : Nat) < signSum (fun a i => if x a (good i) then 1 else -1) a) :
    Complexity.majority (x a) = true := by
  apply majority_eq_true_of_margin (good := Finset.univ.map good)
  have h := margin
  rw [signSum_eq_voteMargin] at h
  exact_mod_cast (by simpa using h :
    (((n - (Finset.univ.map good).card : Nat) : Int) : ℝ) <
      (voteMargin (Finset.univ.map good) (x a) : ℝ))

theorem majority_eq_false_of_signSum {α : Type*} {m n : Nat} (good : Fin m ↪ Fin n)
    (x : α → Fin n → Bool) (a : α)
    (margin : signSum (fun a i => if x a (good i) then 1 else -1) a ≤
      -((n - m : Nat) : ℝ)) : Complexity.majority (x a) = false := by
  apply majority_eq_false_of_margin (good := Finset.univ.map good)
  have h := margin
  rw [signSum_eq_voteMargin] at h
  exact_mod_cast (by simpa using h :
    (voteMargin (Finset.univ.map good) (x a) : ℝ) ≤
      -((((n - (Finset.univ.map good).card : Nat) : Int) : ℝ)))

theorem majority_mass_ge_of_signSum_tails {α : Type*} {m n : Nat}
    (good : Fin m ↪ Fin n) (x : α → Fin n → Bool) (s : Finset α) (w : α → ℝ)
    {t ρ : ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (bad : ((n - m : Nat) : ℝ) ≤ t)
    (positive : ρ ≤ ∑ a ∈ s,
      if t < signSum (fun a i => if x a (good i) then 1 else -1) a then w a else 0)
    (negative : ρ ≤ ∑ a ∈ s,
      if signSum (fun a i => if x a (good i) then 1 else -1) a < -t then w a else 0)
    (b : Bool) : ρ ≤ ∑ a ∈ s, if Complexity.majority (x a) = b then w a else 0 := by
  cases b
  · apply negative.trans
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : signSum (fun a i => if x a (good i) then 1 else -1) a < -t
    · have verdict := majority_eq_false_of_signSum good x a
        (h.le.trans (neg_le_neg bad))
      simp [h, verdict]
    · simp only [ite_eq_right h]
      split <;> simp_all
  · apply positive.trans
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : t < signSum (fun a i => if x a (good i) then 1 else -1) a
    · have verdict := majority_eq_true_of_signSum good x a (bad.trans_lt h)
      simp [h, verdict]
    · simp only [ite_eq_right h]
      split <;> simp_all

theorem majority_mass_ge_of_parityBias {α : Type*} {m n : Nat}
    {s : Finset α} {w : α → ℝ} (good : Fin m ↪ Fin n) (x : α → Fin n → Bool)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 ≤ δ) (budget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (bias : ParityBiasBound s w (fun a i => if x a (good i) then 1 else -1) δ)
    (bad : ((n - m : Nat) : ℝ) ≤ Real.sqrt (m : ℝ) / 8) (b : Bool) :
    (1 / 36 : ℝ) ≤ ∑ a ∈ s, if Complexity.majority (x a) = b then w a else 0 := by
  have signs : ∀ a ∈ s, ∀ i,
      (if x a (good i) then (1 : ℝ) else -1) = 1 ∨
        (if x a (good i) then (1 : ℝ) else -1) = -1 := by
    intro a _ i
    split <;> simp
  exact majority_mass_ge_of_signSum_tails good x s w hw bad
    (signSum_positive_tail_of_parityBias hw hmass hm signs hδ budget bias)
    (signSum_negative_tail_of_parityBias hw hmass hm signs hδ budget bias) b

end Algebraic.Cutwidth.Extractor.Internal
