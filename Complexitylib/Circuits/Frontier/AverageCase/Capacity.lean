/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Pruning
public import Mathlib.Analysis.Real.Sqrt

/-!
# Transition capacity from the distribution of traces

Optimizing the existing pruning inequality charges each used transition by the smaller
of its frontier allowance and the absolute weight of its inputs. This is a one-shot
quantity: low average Shannon entropy alone does not bound it. A square-root moment
provides a convenient sufficient bound without assuming independent boundary signals.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {α β ι U M : Type*}

theorem sumOn_fibers [Finite α] (w : α → ℝ) (S : Set α) (f : α → β)
    (T : Finset β) :
    (∑ y ∈ T, sumOn w {x ∈ S | f x = y}) = sumOn w {x ∈ S | f x ∈ T} := by
  classical
  unfold sumOn
  calc
    _ = ∑ y ∈ T, ∑ x ∈ (toFinite S).toFinset with f x = y, w x := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      ext x
      simp
    _ = ∑ x ∈ (toFinite S).toFinset with f x ∈ T, w x :=
      Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by congr 1; ext x; simp

/-- Keep a fiber exactly when its weight exceeds the cost of describing it. The resulting
description cost plus discarded weight is the sum of the capped fiber weights. -/
theorem exists_capped_codebook [Finite α] (w : α → ℝ) (S : Set α) (f : α → β)
    (c : ℝ) :
    ∃ T : Finset β, c * T.card + sumOn w {x ∈ S | f x ∉ T} =
      ∑ y ∈ (toFinite (f '' S)).toFinset, min c (sumOn w {x ∈ S | f x = y}) := by
  classical
  let E := (toFinite (f '' S)).toFinset
  let m := fun y => sumOn w {x ∈ S | f x = y}
  let T := E.filter fun y => c ≤ m y
  refine ⟨T, ?_⟩
  have hdrop : sumOn w {x ∈ S | f x ∉ T} =
      ∑ y ∈ E.filter (fun y => ¬ c ≤ m y), m y := by
    rw [sumOn_fibers]
    congr 1
    ext x
    have hx : x ∈ S → f x ∈ E := fun hx => (toFinite _).mem_toFinset.mpr ⟨x, hx, rfl⟩
    simp only [T, Finset.mem_filter, Set.mem_ofPred_eq]
    tauto
  rw [hdrop]
  calc
    c * T.card + ∑ y ∈ E.filter (fun y => ¬ c ≤ m y), m y =
        (∑ y ∈ E.filter (fun y => c ≤ m y), min c (m y)) +
        ∑ y ∈ E.filter (fun y => ¬ c ≤ m y), min c (m y) := by
      congr 1
      · rw [Finset.sum_congr rfl (fun y hy => min_eq_left (Finset.mem_filter.mp hy).2)]
        simp [T, mul_comm]
      · exact Finset.sum_congr rfl fun y hy =>
          (min_eq_right (le_of_not_ge (Finset.mem_filter.mp hy).2)).symm
    _ = _ := Finset.sum_filter_add_sum_filter_not _ _ _

namespace Sweep

variable [Finite ι] [Finite U] {S : Set (ι → U)} (P : Sweep S M)

/-- The capped mass of the transition fibers, summed over all steps. -/
noncomputable def cappedCapacity (w : (ι → U) → ℝ) (c : ℝ) : ℝ :=
  ∑ t ∈ Finset.range P.length, ∑ e ∈ (toFinite (P.transition t '' S)).toFinset,
    min c (sumOn w {x ∈ S | P.transition t x = e})

/-- **Distribution-sensitive frontier bound.** A transition costs at most either its
frontier allowance or the absolute weight of all inputs using it. -/
theorem abs_sumOn_le_capped (hP : P.Coherent) (hmono : Monotone P.revealed)
    (hL : 0 < P.length) {KL KR : ℕ} (hKL : 1 < KL) (hKR : 1 < KR)
    {w cost : (ι → U) → ℝ} {a : ℝ} (ha : 0 ≤ a) (hw : ∀ x, |w x| ≤ a)
    (hc : ∀ x, 0 ≤ cost x) (hrect : RectangleBudget w cost KL KR) :
    |sumOn w S| ≤ sumOn cost S +
      P.cappedCapacity (fun x => |w x|) (a * ((KL - 1) * (KR - 1) : ℕ)) := by
  classical
  let c := a * ((KL - 1) * (KR - 1) : ℕ)
  choose T hT using fun t => exists_capped_codebook (fun x => |w x|) S (P.transition t) c
  let keep : ∀ t, Set (M × M × (P.newly t → U)) := fun t => ↑(T t)
  have H := P.abs_sumOn_le_pruned hP hmono hL keep
    (fun t _ => (T t).finite_toSet) hKL hKR ha hw hc hrect
  have Htail := P.sumOn_discarded_le keep (fun x => abs_nonneg (w x))
  have heq : a * ((KL - 1) * (KR - 1) *
        ∑ t ∈ Finset.range P.length, (keep t).ncard : ℕ) +
      ∑ t ∈ Finset.range P.length, sumOn (fun x => |w x|) {x ∈ S | P.transition t x ∉ T t} =
      P.cappedCapacity (fun x => |w x|) c := by
    simp only [keep, Set.ncard_coe_finset, Nat.cast_mul, Nat.cast_sum]
    rw [← mul_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by simpa only [c, Nat.cast_mul] using hT t
  apply H.trans
  rw [← heq, ← add_assoc]
  exact add_le_add le_rfl Htail

/-- The sum of square roots of transition fiber weights. After normalizing a single
layer to probability one, twice its base-two logarithm is Renyi entropy of order `1/2`. -/
noncomputable def rootCapacity (w : (ι → U) → ℝ) : ℝ :=
  ∑ t ∈ Finset.range P.length, ∑ e ∈ (toFinite (P.transition t '' S)).toFinset,
    Real.sqrt (sumOn w {x ∈ S | P.transition t x = e})

theorem cappedCapacity_le_root {w : (ι → U) → ℝ} (hw : ∀ x, 0 ≤ w x)
    {c : ℝ} (hc : 0 ≤ c) : P.cappedCapacity w c ≤ Real.sqrt c * P.rootCapacity w := by
  unfold cappedCapacity rootCapacity
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro e _
  let m := sumOn w {x ∈ S | P.transition t x = e}
  have hm : 0 ≤ m := sumOn_nonneg hw _
  change min c m ≤ Real.sqrt c * Real.sqrt m
  rcases le_total c m with h | h
  · calc
      min c m = c := min_eq_left h
      _ = Real.sqrt c * Real.sqrt c := (Real.mul_self_sqrt hc).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg c)
  · calc
      min c m = m := min_eq_right h
      _ = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt hm).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg m)

end Sweep

/-- Capped transition masses of both output classes control prediction agreement. -/
theorem agreement_le_capped_sweeps [Finite ι] [Finite U] [Nonempty U]
    {f g : (ι → U) → Bool} {K : ℕ} {β : ℝ}
    (hf : RectangleBias f K β) (hK : 1 < K) (hβ : 0 ≤ β)
    {Msg : Bool → Type*} (P : ∀ b, Sweep {x | g x = b} (Msg b))
    (hP : ∀ b, (P b).Coherent) (hmono : ∀ b, Monotone (P b).revealed)
    (hL : ∀ b, 0 < (P b).length) :
    agreement f g ≤ (1 + β) / 2 +
      ((P true).cappedCapacity (fun _ => 1) ((K - 1) ^ 2 : ℕ) +
        (P false).cappedCapacity (fun _ => 1) ((K - 1) ^ 2 : ℕ)) /
      (2 * Nat.card (ι → U)) := by
  refine agreement_le_of_output_errors f g
    (fun b => (P b).cappedCapacity (fun _ => 1) ((K - 1) ^ 2 : ℕ)) fun b => ?_
  have H := (P b).abs_sumOn_le_capped (hP b) (hmono b) (hL b) hK hK
    (a := 1) (by norm_num) (fun x => (abs_boolSign (f x)).le) (fun _ => hβ) hf
  simpa only [abs_boolSign, one_mul, sumOn_const, pow_two] using H

/-- A square-root moment of the complete transition replaces its support size.
No independence between coordinates, boundary signals, or layers is assumed. -/
theorem agreement_le_root_sweeps [Finite ι] [Finite U] [Nonempty U]
    {f g : (ι → U) → Bool} {K : ℕ} {β : ℝ}
    (hf : RectangleBias f K β) (hK : 1 < K) (hβ : 0 ≤ β)
    {Msg : Bool → Type*} (P : ∀ b, Sweep {x | g x = b} (Msg b))
    (hP : ∀ b, (P b).Coherent) (hmono : ∀ b, Monotone (P b).revealed)
    (hL : ∀ b, 0 < (P b).length) :
    agreement f g ≤ (1 + β) / 2 +
      Real.sqrt ((K - 1) ^ 2 : ℕ) *
        ((P true).rootCapacity (fun _ => 1) + (P false).rootCapacity (fun _ => 1)) /
      (2 * Nat.card (ι → U)) := by
  have H := agreement_le_capped_sweeps hf hK hβ P hP hmono hL
  apply H.trans
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [mul_add]
  exact add_le_add ((P true).cappedCapacity_le_root (fun _ => zero_le_one) (by positivity))
    ((P false).cappedCapacity_le_root (fun _ => zero_le_one) (by positivity))

end Complexity.Frontier
