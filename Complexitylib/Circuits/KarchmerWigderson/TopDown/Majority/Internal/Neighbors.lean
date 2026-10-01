/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Internal.Layers
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Rectangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Density limits from many single-bit neighbors

At rate `16/n`, a mask hits any set of at least `n/2` coordinates with
probability at least `8/9`. Its expected size is `16`, so the probability
that it has more than `128` coordinates is at most `1/8`. A selected
single-bit neighbor then gives fiber density at least `2^(-128)`.

Applying this to the two middle Hamming layers initializes Korten's
top-down adversary for majority. This is an extension of his parity
initialization in ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

theorem bernoulliAverage_popCount_internal {n : ℕ} (p : ℝ) :
    bernoulliAverage p (fun P : Fin n → Bool => (popCount P : ℝ)) = n * p := by
  have he (P : Fin n → Bool) : (popCount P : ℝ) = ∑ i, if P i then (1 : ℝ) else 0 := by
    simp [popCount]
  unfold bernoulliAverage
  simp_rw [he, mul_sum]
  rw [sum_comm]
  have hc (i : Fin n) := bernoulliAverage_coordinate_internal p i
  simp only [bernoulliAverage] at hc
  simp_rw [hc]
  simp

theorem bernoulliAverage_hits_internal {n : ℕ} (p : ℝ) (s : Fin n → Bool) :
    bernoulliAverage p (fun P : Fin n → Bool =>
      if ∃ i, s i = true ∧ P i = true then (1 : ℝ) else 0) =
        1 - (1 - p) ^ popCount s := by
  let f (P : {i // s i = true} → Bool) : ℝ := if ∃ i, P i = true then 1 else 0
  calc
    _ = bernoulliAverage p (fun P : Fin n → Bool => f (fun i => P i)) := by
      congr 1
      funext P
      simp [f]
    _ = bernoulliAverage p f := bernoulliAverage_restrict p s f
    _ = _ := by
      simpa only [f, Fintype.card_subtype, popCount] using
        bernoulliAverage_nonempty_internal (ι := {i // s i = true}) p

theorem coordinateDensity_of_neighbor_internal {n : ℕ} (X : Finset (Fin n → Bool))
    (P x : Fin n → Bool) (i : Fin n) (hi : P i = true)
    (hx : Function.update x i (!x i) ∈ X) (hsmall : popCount P ≤ 128) :
    (2 : ℝ) ^ (-(128 : ℝ)) ≤ coordinateDensity X P x := by
  have he : completePattern P x (fun j => Function.update x i (!x i) j) =
      Function.update x i (!x i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [completePattern, hi]
    · by_cases hP : P j = true <;> simp [completePattern, hP, Function.update_of_ne hj]
  have hne : (coordinateFiber X P x).Nonempty := by
    refine ⟨(fun j => Function.update x i (!x i) j), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rwa [he]
  have hc : (1 : ℝ) ≤ (coordinateFiber X P x).card := by
    exact_mod_cast card_pos.mpr hne
  unfold coordinateDensity
  rw [Fintype.card_subtype]
  change (2 : ℝ) ^ (-(128 : ℝ)) ≤
    (coordinateFiber X P x).card / (2 : ℝ) ^ popCount P
  apply (le_div_iff₀ (by positivity)).mpr
  have hpw := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsmall
  calc
    _ ≤ (2 : ℝ) ^ (-(128 : ℝ)) * (2 : ℝ) ^ (128 : ℕ) :=
      mul_le_mul_of_nonneg_left hpw (by positivity)
    _ = 1 := by rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]; norm_num
    _ ≤ _ := hc

theorem isDensityLimit_of_many_neighbors_internal {n : ℕ} (hn : 16 ≤ n)
    (X : Finset (Fin n → Bool)) (x s : Fin n → Bool) (hs : n ≤ 2 * popCount s)
    (hneighbor : ∀ i, s i = true → Function.update x i (!x i) ∈ X) :
    IsDensityLimit X (16 / n) 128 x := by
  let p : ℝ := 16 / n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp' : p ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hn)
  have hmean : (n : ℝ) * p = 16 := by dsimp [p]; field_simp
  have hs' : (n : ℝ) ≤ 2 * popCount s := by exact_mod_cast hs
  have hhit : 8 ≤ (popCount s : ℝ) * p := by
    nlinarith [mul_le_mul_of_nonneg_right hs' hp]
  have hnone : (1 - p) ^ popCount s ≤ 1 / 9 := by
    have hh := one_sub_pow_bound_internal hp' (popCount s)
    have hnon : 0 ≤ (1 - p) ^ popCount s := pow_nonneg (sub_nonneg.mpr hp') _
    nlinarith
  have hpoint (P : Fin n → Bool) :
      (if ∃ i, s i = true ∧ P i = true then (1 : ℝ) else 0) -
        (1 / 128) * (popCount P : ℝ) ≤
      if (2 : ℝ) ^ (-(128 : ℝ)) ≤ coordinateDensity X P x then 1 else 0 := by
    by_cases hhit : ∃ i, s i = true ∧ P i = true
    · rw [ite_eq_left hhit]
      by_cases hsmall : popCount P ≤ 128
      · obtain ⟨i, hi, hPi⟩ := hhit
        rw [ite_eq_left
          (coordinateDensity_of_neighbor_internal X P x i hPi (hneighbor i hi) hsmall)]
        have := Nat.cast_nonneg (α := ℝ) (popCount P)
        linarith
      · have hlarge : (128 : ℝ) < popCount P := by exact_mod_cast (Nat.lt_of_not_ge hsmall)
        split_ifs <;> linarith
    · rw [ite_eq_right hhit]
      have := Nat.cast_nonneg (α := ℝ) (popCount P)
      split_ifs <;> linarith
  have hh := bernoulliAverage_mono hp hp' hpoint
  rw [bernoulliAverage_sub_internal, bernoulliAverage_hits_internal,
    bernoulliAverage_mul_internal, bernoulliAverage_popCount_internal, hmean] at hh
  unfold IsDensityLimit
  change (3 : ℝ) / 4 ≤ bernoulliAverage p _
  linarith

theorem majority_layers_limits_internal {n : ℕ} (hn : 16 ≤ n) :
    (∀ x ∈ weightLayer n (n / 2),
      IsDensityLimit (weightLayer n (n / 2 + 1)) (16 / n) (majorityDeficitBound n) x) ∧
    (∀ y ∈ weightLayer n (n / 2 + 1),
      IsDensityLimit (weightLayer n (n / 2)) (16 / n) (majorityDeficitBound n) y) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (16 : ℝ) / n ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hn)
  constructor
  · intro x hx
    have hx' : popCount x = n / 2 := (mem_filter.mp hx).2
    have hl := isDensityLimit_of_many_neighbors_internal hn (weightLayer n (n / 2 + 1)) x
      (fun i => !x i) (by rw [popCount_not, hx']; omega) ?_
    · exact hl.mono_deficit_internal (by positivity) hp (le_majorityDeficitBound_internal n)
    intro i hi
    have hi' : x i = false := by simpa using hi
    simp only [weightLayer, mem_filter, mem_univ, true_and, hi', Bool.not_false]
    rw [popCount_update_true_internal x i hi', hx']
  · intro y hy
    have hy' : popCount y = n / 2 + 1 := (mem_filter.mp hy).2
    have hl := isDensityLimit_of_many_neighbors_internal hn (weightLayer n (n / 2)) y
      y (by rw [hy']; omega) ?_
    · exact hl.mono_deficit_internal (by positivity) hp (le_majorityDeficitBound_internal n)
    intro i hi
    have hc := popCount_update_false_internal y i hi
    simp only [weightLayer, mem_filter, mem_univ, true_and, hi, Bool.not_true]
    omega

end Complexity.BooleanAnalysis
