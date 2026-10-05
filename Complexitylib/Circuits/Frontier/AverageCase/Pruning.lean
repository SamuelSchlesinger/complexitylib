/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Bias
public import Complexitylib.Circuits.Frontier.AverageCase.Network
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Pruning a coherent sweep

Deleting transitions, rather than arbitrary inputs, preserves the rectangular structure
needed for weighted peeling. A nested reveal order is essential here: a splice inherits
each transition from one of its two parents. The resulting error is the weight of inputs
using a deleted transition, which can be bounded by a union bound on transition tails.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {α ι U M : Type*}

/-- A finite union bound for nonnegative weights, allowing overlapping exceptional sets. -/
theorem sumOn_le_sum_of_cover [Finite α] {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {S : Set α} {T : ℕ} {B : ℕ → Set α}
    (hcover : ∀ x ∈ S, ∃ t < T, x ∈ B t) :
    sumOn w S ≤ ∑ t ∈ Finset.range T, sumOn w (B t) := by
  classical
  let := Fintype.ofFinite α
  have hsum (A : Set α) : sumOn w A = ∑ x, if x ∈ A then w x else 0 := by
    unfold sumOn
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp
  simp only [hsum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : x ∈ S
  · obtain ⟨t, ht, hxt⟩ := hcover x hx
    simp only [ite_eq_left hx]
    exact (show w x = if x ∈ B t then w x else 0 by simp [hxt]).le.trans
      (Finset.single_le_sum (f := fun u => if x ∈ B u then w x else 0)
        (fun u _ => by split_ifs <;> first | exact hw x | exact le_rfl)
        (Finset.mem_range.mpr ht))
  · simp only [ite_eq_right hx]
    exact Finset.sum_nonneg fun t _ => by split_ifs <;> first | exact hw x | exact le_rfl

namespace Sweep

variable {S : Set (ι → U)} (P : Sweep S M)

/-- Inputs all of whose transitions survive the selected pruning. -/
def kept (T : ∀ t, Set (M × M × (P.newly t → U))) : Set (ι → U) :=
  {x ∈ S | ∀ t < P.length, P.transition t x ∈ T t}

/-- A splice in a nested coherent sweep inherits each entire transition from a parent. -/
theorem transition_splice (hP : P.Coherent) (hmono : Monotone P.revealed)
    (t : ℕ) {x y : ι → U} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : P.message t x = P.message t y) (z : ι → U)
    (hzx : EqOn z x (P.revealed t)) (hzy : EqOn z y (P.revealed t)ᶜ) (u : ℕ) :
    P.transition u z = P.transition u x ∨ P.transition u z = P.transition u y := by
  have H := hP t x hx y hy hxy z hzx hzy
  by_cases hut : u < t
  · left
    simp only [transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff]
    exact ⟨H.1 u (by lia), H.1 (u + 1) (by lia),
      hzx.mono (sdiff_subset.trans (hmono (by lia)))⟩
  · right
    have htu : t ≤ u := by lia
    simp only [transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff]
    refine ⟨H.2 u htu, H.2 (u + 1) (by lia), hzy.mono ?_⟩
    intro i hi hit
    exact hi.2 (hmono htu hit)

/-- Delete any collection of transitions. Accepted inputs are exactly the surviving paths. -/
def prune (hP : P.Coherent) (hmono : Monotone P.revealed)
    (T : ∀ t, Set (M × M × (P.newly t → U))) : Sweep (P.kept T) M where
  length := P.length
  revealed := P.revealed
  revealed_zero := P.revealed_zero
  revealed_length := P.revealed_length
  message := P.message
  message_length x hx y hy := P.message_length x hx.1 y hy.1
  splice t x hx y hy hxy z hzx hzy := by
    refine ⟨P.splice t x hx.1 y hy.1 hxy z hzx hzy, fun u hu => ?_⟩
    rcases P.transition_splice hP hmono t hx.1 hy.1 hxy z hzx hzy u with h | h
    · rw [h]; exact hx.2 u hu
    · rw [h]; exact hy.2 u hu

theorem Coherent.prune (hP : P.Coherent) (hmono : Monotone P.revealed)
    (T : ∀ t, Set (M × M × (P.newly t → U))) : (P.prune hP hmono T).Coherent := by
  intro t x hx y hy hxy z hzx hzy
  exact hP t x hx.1 y hy.1 hxy z hzx hzy

theorem transitionCount_prune_le
    (hP : P.Coherent) (hmono : Monotone P.revealed)
    (T : ∀ t, Set (M × M × (P.newly t → U)))
    (hT : ∀ t < P.length, (T t).Finite) :
    (P.prune hP hmono T).transitionCount ≤ ∑ t ∈ Finset.range P.length, (T t).ncard := by
  refine Finset.sum_le_sum fun t ht => ?_
  exact ncard_le_ncard (by rintro _ ⟨x, hx, rfl⟩; exact hx.2 t (Finset.mem_range.mp ht))
    (hT t (Finset.mem_range.mp ht))

/-- Lost probability or weight is at most the sum of the individual transition tails. -/
theorem sumOn_discarded_le [Finite ι] [Finite U]
    (T : ∀ t, Set (M × M × (P.newly t → U))) {w : (ι → U) → ℝ}
    (hw : ∀ x, 0 ≤ w x) :
    sumOn w (S \ P.kept T) ≤
      ∑ t ∈ Finset.range P.length, sumOn w {x ∈ S | P.transition t x ∉ T t} := by
  apply sumOn_le_sum_of_cover hw
  rintro x ⟨hx, hnot⟩
  have : ¬ ∀ t < P.length, P.transition t x ∈ T t := fun h => hnot ⟨hx, h⟩
  push Not at this
  obtain ⟨t, ht, hxt⟩ := this
  exact ⟨t, ht, hx, hxt⟩

/-- **Approximate pruning bound.** Retained transitions pay the frontier cost; discarded
inputs pay their actual absolute weight. No independence assumption is required. -/
theorem abs_sumOn_le_pruned [Finite ι] [Finite U]
    (hP : P.Coherent) (hmono : Monotone P.revealed) (hL : 0 < P.length)
    (T : ∀ t, Set (M × M × (P.newly t → U)))
    (hT : ∀ t < P.length, (T t).Finite)
    {KL KR : ℕ} (hKL : 1 < KL) (hKR : 1 < KR)
    {w cost : (ι → U) → ℝ} {a : ℝ} (ha : 0 ≤ a) (hw : ∀ x, |w x| ≤ a)
    (hc : ∀ x, 0 ≤ cost x) (hrect : RectangleBudget w cost KL KR) :
    |sumOn w S| ≤ sumOn cost S +
      a * ((KL - 1) * (KR - 1) * ∑ t ∈ Finset.range P.length, (T t).ncard : ℕ) +
      sumOn (fun x => |w x|) (S \ P.kept T) := by
  have hkeep : P.kept T ⊆ S := fun _ hx => hx.1
  have H := (P.prune hP hmono T).abs_sumOn_le_of_budget
    (Coherent.prune P hP hmono T) hL hKL hKR ha hw hc hrect
  have hcount := P.transitionCount_prune_le hP hmono T hT
  have hmul : a * ((KL - 1) * (KR - 1) * (P.prune hP hmono T).transitionCount : ℕ) ≤
      a * ((KL - 1) * (KR - 1) * ∑ t ∈ Finset.range P.length, (T t).ncard : ℕ) := by
    apply mul_le_mul_of_nonneg_left _ ha
    exact_mod_cast Nat.mul_le_mul_left _ hcount
  have hcost : sumOn cost (P.kept T) ≤ sumOn cost S := by
    rw [sumOn_sdiff cost hkeep]
    exact le_add_of_nonneg_right (sumOn_nonneg hc _)
  rw [sumOn_sdiff w hkeep]
  have hrest : |sumOn w (S \ P.kept T)| ≤ sumOn (fun x => |w x|) (S \ P.kept T) :=
    Finset.abs_sum_le_sum_abs _ _
  exact (abs_add_le _ _).trans (by linarith)

end Sweep

namespace Network

variable {V E : Type*} (N : Network U ι V E) (π : Layout V) [Nonempty U]

/-- Network sweeps reveal inputs monotonically, including the final unused-input step. -/
theorem sweep_revealed_mono : Monotone (N.sweep π).revealed := by
  intro a b hab i hi
  change i ∈ N.revealedBy π a at hi
  change i ∈ N.revealedBy π b
  unfold revealedBy at *
  split_ifs at * with ha hb
  · obtain ⟨v, hv, hsite⟩ := hi
    exact ⟨v, (show (π v : ℕ) < b from lt_of_lt_of_le hv hab), hsite⟩
  · lia
  · trivial
  · trivial

end Network

/-- Unequal error budgets on the two prediction classes are added before normalization. -/
theorem agreement_le_of_output_errors [Finite α] [Nonempty α] (f g : α → Bool)
    {β : ℝ} (R : Bool → ℝ)
    (h : ∀ b, |sumOn (fun x => boolSign (f x)) {x | g x = b}| ≤
      β * ({x | g x = b}.ncard : ℝ) + R b) :
    agreement f g ≤ (1 + β) / 2 + (R true + R false) / (2 * Nat.card α) := by
  have htotal : ({x | g x = true}.ncard : ℝ) + {x | g x = false}.ncard = Nat.card α := by
    have he : {x | g x = false} = {x | g x = true}ᶜ := by ext x; cases g x <;> simp
    rw [he]
    exact_mod_cast ncard_add_ncard_compl {x | g x = true}
  have hsign := sign_sum_eq f g
  rw [sign_sum_split] at hsign
  have ht := (le_abs_self _).trans (h true)
  have hf := (neg_le_abs _).trans (h false)
  have hnum : 2 * ({x | f x = g x}.ncard : ℝ) ≤
      (1 + β) * Nat.card α + (R true + R false) := by
    have he := congrArg (fun z : ℝ => β * z) htotal
    nlinarith
  have hp : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  unfold agreement
  apply (div_le_iff₀ hp).mpr
  have he : ((1 + β) / 2 + (R true + R false) / (2 * Nat.card α)) * Nat.card α =
      ((1 + β) * Nat.card α + R true + R false) / 2 := by field_simp; ring
  rw [he]
  linarith

/-- **Pruned prediction bound.** `D b` counts the retained transitions for output `b`,
and `lost b` counts the discarded inputs. Their contribution to agreement has the factor
`1/(2 |domain|)`, so discarding probability mass `δ` costs at most `δ/2`. -/
theorem agreement_le_pruned_sweeps [Finite ι] [Finite U] [Nonempty U]
    {f g : (ι → U) → Bool} {K : ℕ} {β : ℝ}
    (hf : RectangleBias f K β) (hK : 1 < K) (hβ : 0 ≤ β)
    {Msg : Bool → Type*} (P : ∀ b, Sweep {x | g x = b} (Msg b))
    (hP : ∀ b, (P b).Coherent) (hmono : ∀ b, Monotone (P b).revealed)
    (hL : ∀ b, 0 < (P b).length)
    (T : ∀ b t, Set (Msg b × Msg b × ((P b).newly t → U)))
    (hT : ∀ b t, t < (P b).length → (T b t).Finite) :
    let D := fun b => ∑ t ∈ Finset.range (P b).length, (T b t).ncard
    let lost := fun b => ({x | g x = b} \ (P b).kept (T b)).ncard
    agreement f g ≤ (1 + β) / 2 +
      (((K - 1) ^ 2 * (D true + D false) + lost true + lost false : ℕ) : ℝ) /
        (2 * Nat.card (ι → U)) := by
  dsimp only
  have H (b : Bool) := (P b).abs_sumOn_le_pruned (hP b) (hmono b) (hL b)
    (T b) (hT b) hK hK (a := 1) (by norm_num)
    (fun x => (abs_boolSign (f x)).le) (fun _ => hβ) hf
  simp only [abs_boolSign, sumOn_const, one_mul] at H
  have A := agreement_le_of_output_errors f g
    (fun b => (((K - 1) * (K - 1) *
      ∑ t ∈ Finset.range (P b).length, (T b t).ncard : ℕ) : ℝ) +
        ({x | g x = b} \ (P b).kept (T b)).ncard)
    (fun b => by simpa only [add_assoc] using H b)
  convert A using 1
  push_cast
  ring

end Complexity.Frontier
