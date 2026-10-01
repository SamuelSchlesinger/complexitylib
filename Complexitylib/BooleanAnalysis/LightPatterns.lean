/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.LightPatterns.Defs
public import Complexitylib.BooleanAnalysis.LightPatterns.Internal

/-!
# Korten's improved light-patterns lemma

Lemma 10 of Oliver Korten, *Top-Down Lower Bounds for All Depths*,
ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.

`improved_light_patterns` uses an arbitrary nonnegative real probability mass
function summing to one. The pointwise bound `mass x ≤ 2 ^ (k - n)` expresses
min-entropy deficit at most `k`. With probability at least `63/64` over
independent coordinate sampling of rate `r ≤ 1/(512*k)`, at most `2^(|R|-k)`
patterns have marginal probability at most `2^(-|R|-2*k-2)`.

`improved_light_patterns_density` gives the equivalent fraction statement for
normalized densities. `coordinateMarginal_normalize` verifies the passage from
probability masses to normalized marginal densities. All results include
dimension zero, zero masses, and sampling rate zero. The subsequent mirror-set
and communication arguments for Theorem 3 are not yet formalized.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

/-- Marginalization preserves total probability mass. -/
theorem sum_coordinateMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mass : (ι → Bool) → ℝ) (s : ι → Bool) :
    (∑ z, coordinateMass mass s z) = ∑ x, mass x :=
  sum_coordinateMass_internal mass s

/-- Marginal masses of a nonnegative mass function are nonnegative. -/
theorem coordinateMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {mass : (ι → Bool) → ℝ} (hm : ∀ x, 0 ≤ mass x) (s : ι → Bool)
    (z : {i // s i = true} → Bool) : 0 ≤ coordinateMass mass s z :=
  sum_nonneg fun _ _ => hm _

/-- Normalizing the input mass by `2^n` normalizes each marginal by `2^|R|`. -/
theorem coordinateMarginal_normalize {n : ℕ} (mass : (Fin n → Bool) → ℝ)
    (s : Fin n → Bool) (z : {i // s i = true} → Bool) :
    coordinateMarginal (fun x => (2 : ℝ) ^ n * mass x) s z =
      (2 : ℝ) ^ Fintype.card {i // s i = true} * coordinateMass mass s z :=
  coordinateMarginal_normalize_internal mass s z

/-- Sparse-sampling estimate for the harmonic transform in the proof of Lemma 10. -/
theorem harmonicTransform_sparse_good_probability {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k) (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r
      (fun s => if 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s then 1 else 0) :=
  harmonicTransform_sparse_good_probability_internal hf hmean hk hbound hr hr'

/-- Lemma 10 for normalized densities: with probability at least `63/64`, the
fraction of patterns with marginal density at most `2^(-2*k-2)` is at most `2^-k`. -/
theorem improved_light_patterns_density {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k) (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k) then 1 else 0) :=
  improved_light_patterns_density_internal hf hmean hk hbound hr hr'

/-- Korten's improved light-patterns lemma (Lemma 10), with its exact constants
and pattern count. Nonnegative masses summing to one represent a distribution;
the pointwise bound is min-entropy deficit at most the real parameter `k`. -/
theorem improved_light_patterns {n : ℕ} {mass : (Fin n → Bool) → ℝ}
    (hm : ∀ x, 0 ≤ mass x) (hmean : (∑ x, mass x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, mass x ≤ (2 : ℝ) ^ (k - n))
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if ((univ.filter fun z => coordinateMass mass s z ≤
          (2 : ℝ) ^ (-(Fintype.card {i // s i = true} : ℝ) - 2 * k - 2)).card : ℝ) ≤
        (2 : ℝ) ^ ((Fintype.card {i // s i = true} : ℝ) - k) then 1 else 0) :=
  improved_light_patterns_internal hm hmean hk hbound hr hr'

end Complexity.BooleanAnalysis
