/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli
public import Complexitylib.BooleanAnalysis.HarmonicMean.Defs
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Density
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Projection

/-!
# Korten's harmonic mean transform

This module formalizes Definition 5, Lemmas 11--12, and Corollary 1 of Oliver
Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.

`harmonicMean_variational` works on any nonempty finite type. The coordinate
transform uses Boolean membership functions for sets and real nonnegative
densities. `harmonicTransform_eq_harmonicMean_coordinateMarginal` identifies
the convenient full-cube representation with the harmonic mean over actual
projected patterns. Zero entries give harmonic mean zero, as in the paper.

`expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform` is Lemma 12, including
dimension zero. `harmonicTransform_good_probability` supplies the intermediate
1/4-sampling estimate in the proof of Lemma 10, using a density bound `B` in
place of `2 ^ k`. The sparse-sampling conclusion and pattern count of Lemma 10
are proved in `Complexitylib.BooleanAnalysis.LightPatterns`.
The top-down communication and circuit lower bounds of Theorem 3 remain open
formalization work.
-/

public section

namespace Complexity.BooleanAnalysis

open scoped BigOperators

section Mean

variable {α : Type*} [Fintype α]

/-- A zero entry makes the harmonic mean zero, implementing `0⁻¹ = ∞`
inside the average rather than Lean's real inverse at zero. -/
theorem harmonicMean_eq_zero_of_exists {f : α → ℝ} (hf : ∃ x, f x = 0) :
    harmonicMean f = 0 := by
  rw [harmonicMean, ite_eq_left hf]

/-- Harmonic means of nonnegative entries are nonnegative. -/
theorem harmonicMean_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ harmonicMean f := harmonicMean_nonneg_internal hf

variable [Nonempty α]

/-- The harmonic mean of a constant on a nonempty finite set is that constant. -/
theorem harmonicMean_const (c : ℝ) : harmonicMean (fun _ : α => c) = c :=
  harmonicMean_const_internal c

/-- Every weight with mean one bounds the harmonic mean by its quadratic energy.
The weight need not be nonnegative for this direction. -/
theorem harmonicMean_le_energy {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hw : (𝔼 x, w x) = 1) : harmonicMean f ≤ 𝔼 x, f x * w x ^ 2 :=
  harmonicMean_le_energy_internal hf hw

/-- A nonnegative weight of mean one attains the variational minimum,
including when an entry of `f` is zero. -/
theorem harmonicMean_exists_weight {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∃ w : α → ℝ, (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧
      (𝔼 x, f x * w x ^ 2) = harmonicMean f :=
  harmonicMean_exists_weight_internal hf

/-- Korten's Lemma 11, generalized to every nonempty finite type. -/
theorem harmonicMean_variational {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f = sInf {a : ℝ | ∃ w : α → ℝ,
      (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧ (𝔼 x, f x * w x ^ 2) = a} :=
  harmonicMean_variational_internal hf

/-- Harmonic means are monotone in their nonnegative entries. -/
theorem harmonicMean_mono {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hfg : ∀ x, f x ≤ g x) : harmonicMean f ≤ harmonicMean g :=
  harmonicMean_mono_internal hf hfg

/-- Harmonic means are concave on nonnegative functions. -/
theorem harmonicMean_concave {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    t * harmonicMean f + (1 - t) * harmonicMean g ≤
      harmonicMean (fun x => t * f x + (1 - t) * g x) :=
  harmonicMean_concave_internal hf hg ht ht'

/-- The harmonic mean is at most the arithmetic mean. -/
theorem harmonicMean_le_expect {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f ≤ 𝔼 x, f x := harmonicMean_le_expect_internal hf

/-- A positive harmonic-mean lower bound controls the fraction of small entries.
This is the reciprocal-density Markov step used for light patterns. -/
theorem harmonicMean_light_fraction_le {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {a b : ℝ} (ha : 0 < a) (ha' : a ≤ harmonicMean f) (hb : 0 ≤ b) :
    (𝔼 x, if f x ≤ b then (1 : ℝ) else 0) ≤ b / a :=
  harmonicMean_light_fraction_le_internal hf ha ha' hb

end Mean

section Projection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full-cube projection depends exactly on the selected input pattern. -/
theorem projectionAverage_eq_coordinateMarginal (f : (ι → Bool) → ℝ)
    (selected x : ι → Bool) :
    projectionAverage f selected x = coordinateMarginal f selected (fun i => x i) :=
  projectionAverage_eq_coordinateMarginal_internal f selected x

/-- Marginalization preserves the uniform mean, hence also density normalization. -/
theorem expect_coordinateMarginal (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    (𝔼 z, coordinateMarginal f selected z) = 𝔼 x, f x :=
  expect_coordinateMarginal_internal f selected

/-- The transform agrees with Definition 5 on the actual projected cube;
repeating each pattern on the full cube does not change its harmonic mean. -/
theorem harmonicTransform_eq_harmonicMean_coordinateMarginal
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    harmonicTransform f selected = harmonicMean (coordinateMarginal f selected) :=
  harmonicTransform_eq_harmonicMean_coordinateMarginal_internal f selected

/-- Lemma 11 on the selected-coordinate cube, with nonnegative weights of mean one. -/
theorem harmonicTransform_variational {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) :
    harmonicTransform f selected = sInf {a : ℝ |
      ∃ w : ({i // selected i = true} → Bool) → ℝ,
        (∀ z, 0 ≤ w z) ∧ (𝔼 z, w z) = 1 ∧
          (𝔼 z, coordinateMarginal f selected z * w z ^ 2) = a} := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal]
  exact harmonicMean_variational fun _ => Finset.expect_nonneg fun _ _ => hf _

/-- A positive transform lower bound bounds the fraction of light projected
patterns. The expectation ranges over the actual selected-coordinate cube. -/
theorem coordinateMarginal_light_fraction_le {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : ι → Bool) {a b : ℝ} (ha : 0 < a)
    (ha' : a ≤ harmonicTransform f selected) (hb : 0 ≤ b) :
    (𝔼 z, if coordinateMarginal f selected z ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal] at ha'
  exact harmonicMean_light_fraction_le
    (fun _ => Finset.expect_nonneg fun _ _ => hf _) ha ha' hb

/-- The harmonic transform is nonnegative on nonnegative functions. -/
theorem harmonicTransform_nonneg {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) : 0 ≤ harmonicTransform f selected :=
  harmonicTransform_nonneg_internal hf selected

/-- Corollary 1(1): the transform is pointwise concave in its input function. -/
theorem harmonicTransform_concave {f g : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (selected : ι → Bool) :
    t * harmonicTransform f selected + (1 - t) * harmonicTransform g selected ≤
      harmonicTransform (fun x => t * f x + (1 - t) * g x) selected :=
  harmonicTransform_concave_internal hf hg ht ht' selected

/-- Selecting no coordinates gives the ordinary mean. -/
theorem harmonicTransform_empty (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => false) = 𝔼 x, f x :=
  harmonicTransform_empty_internal f

/-- Selecting all coordinates gives the harmonic mean of the original function. -/
theorem harmonicTransform_full (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => true) = harmonicMean f :=
  harmonicTransform_full_internal f

/-- Constants are fixed by the harmonic transform. -/
theorem harmonicTransform_const (c : ℝ) (selected : ι → Bool) :
    harmonicTransform (fun _ => c) selected = c := harmonicTransform_const_internal c selected

end Projection

/-- Corollary 1(2): revealing more coordinates decreases the harmonic transform.
The hypothesis is inclusion of the two sets represented by Boolean masks. -/
theorem harmonicTransform_antitone {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) {r s : Fin n → Bool} (hrs : ∀ i, r i = true → s i = true) :
    harmonicTransform f s ≤ harmonicTransform f r := harmonicTransform_antitone_internal hf hrs

/-- Corollary 1(3): the harmonic transform is at most the ordinary mean. -/
theorem harmonicTransform_le_expect {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : Fin n → Bool) :
    harmonicTransform f selected ≤ 𝔼 x, f x := harmonicTransform_le_expect_internal hf selected

/-- Korten's Lemma 12: on the `1/4`-biased coordinate cube, the mean square root
of the harmonic transform dominates the uniform mean square root of `f`. -/
theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform {n : ℕ}
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, Real.sqrt (f x)) ≤
      bernoulliAverage (1 / 4) (fun selected => Real.sqrt (harmonicTransform f selected)) :=
  expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_internal hf

/-- Intermediate estimate in the proof of Lemma 10: a normalized density bounded
by `B` has harmonic transform at least `1 / (4 * B)` with probability at least
`1 / (2 * sqrt B)` under `1/4`-coordinate sampling. The `LightPatterns` module
transfers this estimate to sparse sampling. -/
theorem harmonicTransform_good_probability {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {B : ℝ} (hB : 1 ≤ B)
    (hbound : ∀ x, f x ≤ B) :
    1 / (2 * Real.sqrt B) ≤ bernoulliAverage (1 / 4)
      (fun selected => if 1 / (4 * B) ≤ harmonicTransform f selected then 1 else 0) :=
  harmonicTransform_good_probability_internal hf hmean hB hbound

end Complexity.BooleanAnalysis
