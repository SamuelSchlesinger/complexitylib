/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Cube
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Order properties of the harmonic mean transform

The three parts of Corollary 1 in Korten (2026): concavity, decrease under
revealing more coordinates, and the upper bound by the ordinary mean.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

theorem harmonicPair_le_midpoint_internal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * a * b / (a + b) ≤ (a + b) / 2 := by
  by_cases hz : a + b = 0
  · simp [hz]
  have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (a - b)]

theorem harmonicPair_mono_internal {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) : 2 * a * b / (a + b) ≤ 2 * c * d / (c + d) := by
  have hc := ha.trans hac
  have hd := hb.trans hbd
  by_cases hz : a + b = 0
  · rw [hz, div_zero]
    positivity
  have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  have hq : 0 < c + d := hp.trans_le (add_le_add hac hbd)
  apply (div_le_div_iff₀ hp hq).mpr
  nlinarith [mul_nonneg (mul_nonneg ha hc) (sub_nonneg.mpr hbd),
    mul_nonneg (mul_nonneg hb hd) (sub_nonneg.mpr hac)]

theorem harmonicTransform_concave_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (selected : ι → Bool) :
    t * harmonicTransform f selected + (1 - t) * harmonicTransform g selected ≤
      harmonicTransform (fun x => t * f x + (1 - t) * g x) selected := by
  have he : projectionAverage (fun x => t * f x + (1 - t) * g x) selected =
      fun x => t * projectionAverage f selected x +
        (1 - t) * projectionAverage g selected x := by
    funext x
    simp only [projectionAverage, expect_add_distrib, ← mul_expect]
  unfold harmonicTransform
  rw [he]
  exact harmonicMean_concave_internal (projectionAverage_nonneg_internal hf selected)
    (projectionAverage_nonneg_internal hg selected) ht ht'

theorem harmonicTransform_antitone_internal {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) {r s : Fin n → Bool}
    (hrs : ∀ i, r i = true → s i = true) : harmonicTransform f s ≤ harmonicTransform f r := by
  induction n with
  | zero => exact le_of_eq (congrArg (harmonicTransform f) (Subsingleton.elim _ _))
  | succ n ih =>
    obtain ⟨⟨rb, r⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective r
    obtain ⟨⟨sb, s⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective s
    change harmonicTransform f (Fin.cons sb s) ≤ harmonicTransform f (Fin.cons rb r)
    have htail : ∀ i, r i = true → s i = true := fun i => hrs i.succ
    have h0 := fun x => hf (Fin.cons false x)
    have h1 := fun x => hf (Fin.cons true x)
    have havg : ∀ x, 0 ≤ (f (Fin.cons false x) + f (Fin.cons true x)) / 2 :=
      fun x => div_nonneg (add_nonneg (h0 x) (h1 x)) (by norm_num)
    cases rb <;> cases sb
    · rw [harmonicTransform_cons_false_internal, harmonicTransform_cons_false_internal]
      exact ih havg htail
    · rw [harmonicTransform_cons_true_internal hf, harmonicTransform_cons_false_internal]
      exact (harmonicPair_le_midpoint_internal (harmonicTransform_nonneg_internal h0 s)
        (harmonicTransform_nonneg_internal h1 s)).trans
        ((harmonicTransform_midpoint_internal h0 h1 s).trans (ih havg htail))
    · have h := hrs 0 rfl
      contradiction
    · rw [harmonicTransform_cons_true_internal hf, harmonicTransform_cons_true_internal hf]
      exact harmonicPair_mono_internal (harmonicTransform_nonneg_internal h0 s)
        (harmonicTransform_nonneg_internal h1 s) (ih h0 htail) (ih h1 htail)

theorem harmonicTransform_empty_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : harmonicTransform f (fun _ => false) = 𝔼 x, f x := by
  have he : projectionAverage f (fun _ => false) = fun _ => 𝔼 x, f x := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he, harmonicMean_const_internal]

theorem harmonicTransform_full_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : harmonicTransform f (fun _ => true) = harmonicMean f := by
  have he : projectionAverage f (fun _ => true) = f := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he]

theorem harmonicTransform_le_expect_internal {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : Fin n → Bool) :
    harmonicTransform f selected ≤ 𝔼 x, f x := by
  rw [← harmonicTransform_empty_internal f]
  exact harmonicTransform_antitone_internal hf (by simp)

end Complexity.BooleanAnalysis
