/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Sweep
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Rectangle bias and prediction agreement -/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {α ι U : Type*}

theorem sumOn_congr [Finite α] {w w' : α → ℝ} {S : Set α}
    (h : ∀ x ∈ S, w x = w' x) : sumOn w S = sumOn w' S :=
  Finset.sum_congr rfl fun x hx => h x ((toFinite S).mem_toFinset.mp hx)

@[simp] theorem sumOn_const [Finite α] (a : ℝ) (S : Set α) :
    sumOn (fun _ => a) S = a * S.ncard := by
  simp [sumOn, ← ncard_eq_toFinset_card, mul_comm]

/-- A Boolean value as a sign, positive at `true`. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by cases b <;> norm_num [boolSign]

/-- Uniform prediction agreement, normalized by the full input domain. -/
noncomputable def agreement (f g : α → Bool) : ℝ :=
  ({x | f x = g x}.ncard : ℝ) / Nat.card α

/-- Bias at most `β` on every coordinate rectangle with both sides of size at least `K`. -/
def RectangleBias [Finite ι] [Finite U] (f : (ι → U) → Bool) (K : ℕ) (β : ℝ) : Prop :=
  RectangleBudget (fun x => boolSign (f x)) (fun _ => β) K K

/-- Signed correlation is twice agreement minus one, before normalization. -/
theorem sign_sum_eq [Finite α] (f g : α → Bool) :
    sumOn (fun x => boolSign (f x) * boolSign (g x)) univ =
      2 * ({x | f x = g x}.ncard : ℝ) - Nat.card α := by
  let S := {x | f x = g x}
  have hS : sumOn (fun x => boolSign (f x) * boolSign (g x)) S = S.ncard := by
    calc _ = sumOn (fun _ => (1 : ℝ)) S := sumOn_congr fun x hx => by
          change f x = g x at hx
          rw [hx]; cases g x <;> norm_num [boolSign]
      _ = _ := by simp
  have hT : sumOn (fun x => boolSign (f x) * boolSign (g x)) (univ \ S) = -(Sᶜ.ncard : ℝ) := by
    calc _ = sumOn (fun _ => (-1 : ℝ)) (univ \ S) := sumOn_congr fun x hx => by
          have hne : f x ≠ g x := hx.2
          cases hf : f x <;> cases hg : g x <;> simp_all [boolSign]
      _ = _ := by simp [← compl_eq_univ_sdiff]
  rw [sumOn_sdiff _ (subset_univ S), hS, hT]
  have hcard : (S.ncard : ℝ) + Sᶜ.ncard = Nat.card α := by
    exact_mod_cast ncard_add_ncard_compl S
  dsimp [S] at *
  linarith

/-- Splitting by the predicted bit gives the two signed output-class sums. -/
theorem sign_sum_split [Finite α] (f g : α → Bool) :
    sumOn (fun x => boolSign (f x) * boolSign (g x)) univ =
      sumOn (fun x => boolSign (f x)) {x | g x = true} -
        sumOn (fun x => boolSign (f x)) {x | g x = false} := by
  classical
  let S := {x | g x = true}
  have hcomp : univ \ S = {x | g x = false} := by ext x; cases g x <;> simp [S]
  rw [sumOn_sdiff _ (subset_univ S), hcomp]
  have h1 : sumOn (fun x => boolSign (f x) * boolSign (g x)) S =
      sumOn (fun x => boolSign (f x)) S := sumOn_congr fun x hx => by
    change g x = true at hx
    simp [hx, boolSign]
  have h0 : sumOn (fun x => boolSign (f x) * boolSign (g x)) {x | g x = false} =
      -sumOn (fun x => boolSign (f x)) {x | g x = false} := by
    calc _ = sumOn (fun x => -boolSign (f x)) {x | g x = false} :=
          sumOn_congr fun x hx => by
            change g x = false at hx
            simp [hx, boolSign]
      _ = _ := by simp [sumOn]
  rw [h1, h0]
  rfl

/-- Two output-class bias bounds give the agreement bound with the correct factor of two. -/
theorem agreement_le_of_output_bias [Finite α] [Nonempty α] (f g : α → Bool) {β R : ℝ}
    (h : ∀ b : Bool, |sumOn (fun x => boolSign (f x)) {x | g x = b}| ≤
      β * ({x | g x = b}.ncard : ℝ) + R) :
    agreement f g ≤ (1 + β) / 2 + R / Nat.card α := by
  have htotal : ({x | g x = true}.ncard : ℝ) + {x | g x = false}.ncard = Nat.card α := by
    have he : {x | g x = false} = {x | g x = true}ᶜ := by ext x; cases g x <;> simp
    rw [he]
    exact_mod_cast ncard_add_ncard_compl {x | g x = true}
  have hsign := sign_sum_eq f g
  rw [sign_sum_split] at hsign
  have htrue := h true
  have hfalse := h false
  have hnum : 2 * ({x | f x = g x}.ncard : ℝ) ≤ (1 + β) * Nat.card α + 2 * R := by
    have ht := le_abs_self (sumOn (fun x => boolSign (f x)) {x | g x = true})
    have hf := neg_le_abs (sumOn (fun x => boolSign (f x)) {x | g x = false})
    have hβtotal := congrArg (fun z : ℝ => β * z) htotal
    nlinarith
  have hpos : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  unfold agreement
  apply (div_le_iff₀ hpos).2
  field_simp
  nlinarith

/-- If many inputs are unused, an output class is either a thick rectangle or has only
`q K²` inputs. This is the weighted replacement for the support lemma. -/
theorem RectangleBias.abs_sumOn_le_of_dependsOn [Finite ι] [Finite U]
    {f : (ι → U) → Bool} {K : ℕ} {β : ℝ} (hf : RectangleBias f K β)
    (hK : 1 < K) (hβ : 0 ≤ β) {S : Set (ι → U)} {R : Set ι}
    (hR : DependsOn (· ∈ S) R) (hle : K ≤ Nat.card U ^ Rᶜ.ncard) :
    |sumOn (fun x => boolSign (f x)) S| ≤ β * S.ncard + (Nat.card U * K ^ 2 : ℕ) := by
  have hex : ∃ d, K ≤ Nat.card U ^ d := ⟨_, hle⟩
  obtain ⟨d, hdK, hdmin⟩ : ∃ d, K ≤ Nat.card U ^ d ∧ ∀ d' < d, Nat.card U ^ d' < K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun d' hd' => not_le.mp (Nat.find_min hex hd')⟩
  have hdR : d ≤ Rᶜ.ncard := by
    by_contra! h
    exact absurd hle (not_le.mpr (hdmin _ h))
  obtain ⟨D, hDR, rfl⟩ := exists_subset_card_eq hdR
  let B := Dᶜ.domRestrict '' S
  have hD := hR.mono (subset_compl_comm.mp hDR)
  have heq : S = rectangle D univ B := by
    apply subset_antisymm
    · intro x hx
      exact ⟨mem_univ _, x, hx, rfl⟩
    · rintro z ⟨-, y, hy, hyz⟩
      have h : (y ∈ S) = (z ∈ S) := hD fun i hi => congrFun hyz ⟨i, hi⟩
      exact h ▸ hy
  have hA : (univ : Set (D → U)).ncard = Nat.card U ^ D.ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
  by_cases hB : K ≤ B.ncard
  · have H := hf D univ B (hA.symm ▸ hdK) hB
    rw [← heq, sumOn_const] at H
    exact H.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · have hcard : S.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := by
      calc S.ncard ≤ ((univ : Set (D → U)) ×ˢ B).ncard :=
            ncard_le_ncard_of_injOn _ (fun x hx => ⟨mem_univ _, x, hx, rfl⟩)
              (domRestrict_prod_injective D).injOn
        _ = Nat.card U ^ D.ncard * B.ncard := by rw [ncard_prod, hA]
        _ ≤ _ := Nat.mul_le_mul_left _ (by lia)
    have hd : 0 < D.ncard := by
      by_contra! hz
      have : D.ncard = 0 := by lia
      rw [this, pow_zero] at hdK
      lia
    have hlt := hdmin (D.ncard - 1) (by lia)
    have hpow : Nat.card U ^ D.ncard = Nat.card U * Nat.card U ^ (D.ncard - 1) := by
      rw [← pow_succ']; congr 1; lia
    have hcard' : S.ncard ≤ Nat.card U * K ^ 2 := by
      calc S.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := hcard
        _ ≤ Nat.card U * K * K := by rw [hpow]; gcongr; lia
        _ = _ := by ring
    have H := abs_sumOn_le (fun x => (abs_boolSign (f x)).le) S
    simp only [one_mul] at H
    have hc : (S.ncard : ℝ) ≤ (Nat.card U * K ^ 2 : ℕ) := by exact_mod_cast hcard'
    nlinarith [mul_nonneg hβ (Nat.cast_nonneg (α := ℝ) S.ncard)]

@[simp] theorem boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by
  cases b <;> norm_num [boolSign]

/-- Complementing the target preserves its rectangle-bias guarantee. -/
theorem RectangleBias.not [Finite ι] [Finite U] {f : (ι → U) → Bool} {K : ℕ} {β : ℝ}
    (hf : RectangleBias f K β) : RectangleBias (fun x => !(f x)) K β := by
  intro X A B hA hB
  simpa only [boolSign_not, sumOn, Finset.sum_neg_distrib, abs_neg] using hf X A B hA hB

/-- Exactly one of a target and its complement agrees with a Boolean prediction. -/
theorem agreement_not [Finite α] [Nonempty α] (f g : α → Bool) :
    agreement (fun x => !(f x)) g = 1 - agreement f g := by
  have he : {x | Bool.not (f x) = g x} = {x | f x = g x}ᶜ := by
    ext x
    change (Bool.not (f x) = g x) ↔ ¬(f x = g x)
    cases f x <;> cases g x <;> decide
  have hcard : ({x | f x = g x}.ncard : ℝ) + {x | f x = g x}ᶜ.ncard = Nat.card α := by
    exact_mod_cast ncard_add_ncard_compl {x | f x = g x}
  have hpos : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  unfold agreement
  rw [he]
  apply (div_eq_iff (ne_of_gt hpos)).2
  field_simp
  linarith

end Complexity.Frontier
