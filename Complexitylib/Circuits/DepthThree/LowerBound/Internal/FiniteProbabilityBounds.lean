/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: finite probability bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/FiniteProbabilityBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

/-- Uniform probability of a predicate on a finite type. -/
def finiteProb {Ω : Type uDepth1} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  finiteAvg (fun ω => if P ω then 1 else 0)

variable {Ω : Type uDepth2} {Λ : Type uDepth3} [Fintype Ω] [Fintype Λ]

theorem finiteProb_nonneg (P : Ω → Prop) : 0 ≤ finiteProb P := by
  apply finiteAvg_nonneg
  intro ω
  split_ifs <;> norm_num

theorem finiteProb_le_one [Nonempty Ω] (P : Ω → Prop) : finiteProb P ≤ 1 := by
  have h : finiteProb P ≤ finiteAvg (fun _ : Ω => (1 : ℝ)) := by
    apply finiteAvg_mono
    intro ω
    split_ifs <;> norm_num
  simpa using h

theorem finiteProb_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    finiteProb P ≤ finiteProb Q := by
  apply finiteAvg_mono
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [hp, ite_false]
    split_ifs <;> norm_num

theorem finiteAvg_exists_le [Nonempty Ω] (f : Ω → ℝ) :
    ∃ ω, f ω ≤ finiteAvg f := by
  obtain ⟨ω, hω, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have h := finiteAvg_mono (fun x => hmin x (Finset.mem_univ x))
  simpa using h

theorem finiteAvg_exists_le_of_le [Nonempty Ω] (f : Ω → ℝ) (c : ℝ)
    (h : finiteAvg f ≤ c) : ∃ ω, f ω ≤ c := by
  obtain ⟨ω, hω⟩ := finiteAvg_exists_le f
  exact ⟨ω, hω.trans h⟩

theorem finiteProb_gt_le {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    finiteProb (fun ω => a < f ω) ≤ finiteAvg f / a := by
  have h : finiteAvg (fun ω => a * (if a < f ω then 1 else 0)) ≤ finiteAvg f := by
    apply finiteAvg_mono
    intro ω
    by_cases hω : a < f ω
    · simpa [hω] using hω.le
    · simpa [hω] using hf ω
  rw [finiteAvg_const_mul] at h
  apply (le_div_iff₀ ha).mpr
  simpa only [finiteProb, mul_comm] using h

theorem finiteProb_exists_le_sum {ι : Type uDepth4} (s : Finset ι) (P : ι → Ω → Prop) :
    finiteProb (fun ω => ∃ i ∈ s, P i ω) ≤ ∑ i ∈ s, finiteProb (P i) := by
  have h : finiteProb (fun ω => ∃ i ∈ s, P i ω) ≤
      finiteAvg (fun ω => ∑ i ∈ s, if P i ω then (1 : ℝ) else 0) := by
    apply finiteAvg_mono
    intro ω
    by_cases he : ∃ i ∈ s, P i ω
    · obtain ⟨i, hi, hPi⟩ := he
      have hs : (if P i ω then (1 : ℝ) else 0) ≤
          ∑ j ∈ s, if P j ω then (1 : ℝ) else 0 := by
        apply Finset.single_le_sum _ hi
        intro j hj
        split_ifs <;> norm_num
      simpa [show ∃ i ∈ s, P i ω from ⟨i, hi, hPi⟩, hPi] using hs
    · simp only [he, ite_false]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> norm_num
  simpa only [finiteAvg_sum, finiteProb] using h

theorem finiteProb_abs_gt_le_moment (f : Ω → ℝ) (t : ℕ) (ht : 0 < t)
    (a C : ℝ) (ha : 0 < a)
    (hM : finiteAvg (fun ω => |f ω| ^ t) ≤ C) :
    finiteProb (fun ω => a < |f ω|) ≤ C / a ^ t := by
  have he : finiteProb (fun ω => a < |f ω|) ≤
      finiteProb (fun ω => a ^ t < |f ω| ^ t) := by
    apply finiteProb_mono
    intro ω hω
    exact pow_lt_pow_left₀ hω ha.le (Nat.ne_of_gt ht)
  have hmark := finiteProb_gt_le (fun ω => pow_nonneg (abs_nonneg (f ω)) t)
    (pow_pos ha t)
  exact he.trans (hmark.trans (div_le_div_of_nonneg_right hM (pow_nonneg ha.le t)))

theorem finiteAvg_restrictionAvg {V : Type uDepth5} [Fintype V] (p : ℝ)
    (F : Ω → Restriction V → ℝ) :
    finiteAvg (fun ω => restrictionAvg p (F ω)) =
      restrictionAvg p (fun σ => finiteAvg (fun ω => F ω σ)) := by
  unfold restrictionAvg
  rw [finiteAvg_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact finiteAvg_const_mul _ _

end DepthThreeLowerBound

end

end Complexity
