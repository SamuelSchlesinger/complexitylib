/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Dissociated.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Periodic
public import Mathlib.Data.Nat.Size

/-!
# Uniform periodic tensor estimates

The checked paired-cluster lower bound supplies the rank estimate; a finite search
chooses all parameters uniformly while keeping every coefficient's binary length linear.
-/

@[expose] public section

namespace Algebraic.Tensor3.Dissociated.Internal

open Finset Filter

/-- Every fixed positive order eventually passes all finite checks. -/
theorem eventually_admissible {p : ℕ} (hp : 1 ≤ p) : ∀ᶠ k in atTop, Admissible k p := by
  filter_upwards [eventually_ge_atTop (blockLength p),
    eventually_ge_atTop (2 ^ p),
    eventually_ge_atTop (2 ^ (rowPeriod p * columnPeriod p)),
    eventually_ge_atTop ((p + 1) * (16 * (p + 1) * blockLength p + 2))]
    with k hL hpLog hperiod hcost
  exact ⟨hp, Nat.le_log_of_pow_le (by decide) (by lia), hL,
    Nat.le_log_of_pow_le (by decide) (by lia), by lia⟩

/-- An admissible order is present in the actual bounded search. -/
theorem mem_candidates {k p : ℕ} (hp : Admissible k p) : p ∈ candidates k := by
  exact mem_filter.mpr ⟨mem_range.mpr (by have := hp.2.1; lia), hp⟩

/-- The chosen order is at least any admissible order. -/
theorem le_order {k p : ℕ} (hp : Admissible k p) : p ≤ order k :=
  Finset.le_sup (f := id) (mem_candidates hp)

/-- If any order is admissible, the maximal selected order is admissible. -/
theorem admissible_order {k p : ℕ} (hp : Admissible k p) : Admissible k (order k) := by
  have h := Finset.sup_mem_of_nonempty (f := id) ⟨p, mem_candidates hp⟩
  obtain ⟨q, hq, heq⟩ := h
  have hq := (mem_filter.mp hq).2
  exact (show q = order k from heq) ▸ hq

/-- The selected orders tend to infinity; the tensor does not depend on epsilon. -/
theorem eventually_le_order (p : ℕ) : ∀ᶠ k in atTop, p ≤ order k := by
  filter_upwards [eventually_admissible (p := max p 1) (by lia)] with k hk
  exact (le_max_left p 1).trans (le_order hk)

/-- The selected order always lies in the logarithmic search range. -/
theorem order_le_log (k : ℕ) : order k ≤ Nat.log 2 (2 * k + 1) := by
  apply Finset.sup_le
  intro p hp
  exact (mem_filter.mp hp).2.2.1

/-- Above the cutoff the tensor is exactly an existing periodic tensor. -/
theorem oddTensor_eq {k : ℕ} (hk : Admissible k (order k)) :
    oddTensor k = periodicLMTensor k (rowPeriod (order k)) (columnPeriod (order k)) := by
  funext a j l
  simp only [oddTensor, oddEntry, hk, ↓reduceIte, periodicLMTensor, lmTensor, weightedShifts]
  split_ifs <;> simp [periodicWeight]

/-- Every integer coefficient has at most the dimension plus one binary digits. -/
theorem oddEntry_size_le (k a j l : ℕ) : (oddEntry k a j l).size ≤ 2 * k + 2 := by
  unfold oddEntry
  split_ifs with hk hsupport
  · rw [Nat.size_pow]
    have hrow := Nat.mod_lt a
      (show 0 < rowPeriod (order k) by unfold rowPeriod; lia)
    have hcolumn := Nat.mod_lt j
      (show 0 < columnPeriod (order k) by unfold columnPeriod; lia)
    have hcode : a % rowPeriod (order k) * columnPeriod (order k) +
        j % columnPeriod (order k) < rowPeriod (order k) * columnPeriod (order k) := by
      nlinarith [Nat.mul_le_mul_right (columnPeriod (order k)) hrow]
    have hpow : 2 ^ (a % rowPeriod (order k) * columnPeriod (order k) +
        j % columnPeriod (order k)) ≤ 2 * k + 1 :=
      Nat.pow_le_of_le_log (by lia) (hcode.le.trans hk.2.2.2.1)
    lia
  all_goals simp

/-- The finite lower bound of the uniformly selected tensor. -/
theorem lowerBound_of_admissible {k : ℕ} (hk : Admissible k (order k)) :
    (7 / 3 - 8 / (3 * ((order k : ℝ) + 1))) * (2 * k + 1) ≤ (oddTensor k).borderRank := by
  let p := order k
  have hp : 1 ≤ p := hk.1
  have hL : selectionSize p ≤ blockLength p := by
    unfold blockLength
    exact Nat.le_mul_of_pos_left _ (by lia)
  have main := le_borderRank_periodicLMTensor (k := k) (p := p)
    (L := blockLength p) (A := rowPeriod p) (M := columnPeriod p)
    hp hL hk.2.2.1 (by unfold rowPeriod; lia) (by unfold columnPeriod; lia)
  have hP : 0 < (p : ℝ) + 1 := by positivity
  have hR : 0 < (selectionSize p : ℝ) := by
    exact_mod_cast (show 0 < selectionSize p by unfold selectionSize; positivity)
  have hLreal : (blockLength p : ℝ) = ((p : ℝ) + 1) * selectionSize p := by
    simp only [blockLength, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hcost : ((p : ℝ) + 1) * (16 * ((p : ℝ) + 1) * blockLength p + 2) ≤ 2 * k + 1 := by
    exact_mod_cast hk.2.2.2.2
  have cost : 16 * ((p : ℝ) + 1) * blockLength p + 2 ≤ (2 * k + 1) / ((p : ℝ) + 1) :=
    (le_div_iff₀ hP).mpr (by nlinarith [hcost])
  have quotient : (selectionSize p : ℝ) * (2 * k + 1) / blockLength p =
      (2 * k + 1) / ((p : ℝ) + 1) := by
    rw [hLreal]
    field_simp
  have selection : (selectionSize p : ℝ) = 3 ^ (2 * p) + 1 := by
    simp [selectionSize]
  rw [← oddTensor_eq hk, ← selection, quotient] at main
  have arithmetic :
      (7 / 3 - 8 / (3 * ((p : ℝ) + 1))) * (2 * k + 1) =
      (7 / 3 - 2 / (3 * ((p : ℝ) + 1))) * (2 * k + 1) -
        2 * ((2 * k + 1) / ((p : ℝ) + 1)) := by
    field_simp
    ring
  change (7 / 3 - 8 / (3 * ((p : ℝ) + 1))) * (2 * k + 1) ≤ _
  rw [arithmetic]
  linarith

/-- The one odd-dimensional family approaches the paired-cluster coefficient. -/
theorem eventually_odd_lowerBound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - ε) * (2 * k + 1 : ℝ) ≤ (oddTensor k).borderRank := by
  obtain ⟨P, hP⟩ := exists_nat_gt (8 / (3 * ε))
  filter_upwards [eventually_le_order P, eventually_admissible (p := 1) (by decide)]
    with k horder hfirst
  have hk := admissible_order hfirst
  have main := lowerBound_of_admissible hk
  have hP' : 8 < (P : ℝ) * (3 * ε) := (div_lt_iff₀ (by positivity)).mp hP
  have horder' : (P : ℝ) ≤ order k := by exact_mod_cast horder
  have saving : 8 / (3 * ((order k : ℝ) + 1)) < ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hdim : 0 ≤ (2 * k + 1 : ℝ) := by positivity
  nlinarith

/-- The padded core loses at most one dimension. -/
theorem core_bounds {m : ℕ} (hm : 0 < m) :
    2 * coreIndex m + 1 ≤ m ∧ m ≤ 2 * coreIndex m + 2 := by
  unfold coreIndex
  lia

/-- Each valid coordinate has a linear bound on its binary output size. -/
theorem entry_size_le {m a : ℕ} (ha : a < m) (j l : ℕ) :
    (entry m a j l).size ≤ m + 1 := by
  unfold entry
  split_ifs
  · exact (oddEntry_size_le _ _ _ _).trans (by have := core_bounds (by lia : 0 < m); lia)
  · simp

/-- Coordinate restriction recovers the whole odd core exactly. -/
theorem odd_borderRank_le {m : ℕ} (hm : 0 < m) :
    (oddTensor (coreIndex m)).borderRank ≤ (tensor m).borderRank := by
  let inclusion := Fin.castLE (core_bounds hm).1
  have sub : (tensor m).subtensor inclusion inclusion inclusion = oddTensor (coreIndex m) := by
    funext a j l
    simp [subtensor, tensor, entry, oddTensor, inclusion, a.isLt, j.isLt, l.isLt]
  rw [← sub]
  exact borderRank_subtensor_le inclusion inclusion inclusion (tensor m)

/-- Growing ambient dimension also grows the odd core. -/
theorem coreIndex_tendsto : Tendsto coreIndex atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2 * k + 1)] with m hm
  unfold coreIndex
  lia

/-- Padding preserves the limiting coefficient, with an explicit small epsilon guard. -/
theorem eventually_lowerBound_small {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∀ᶠ m : ℕ in atTop, (7 / 3 - ε) * (m : ℝ) ≤ (tensor m).borderRank := by
  obtain ⟨N, hN⟩ := exists_nat_gt (6 / ε)
  filter_upwards [coreIndex_tendsto.eventually (eventually_odd_lowerBound
      (show 0 < ε / 2 by positivity)), eventually_ge_atTop N, eventually_ge_atTop 1]
    with m hcore hm hpositive
  have hN' : 6 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hdim : (m : ℝ) ≤ 2 * coreIndex m + 2 := by
    exact_mod_cast (core_bounds (by lia : 0 < m)).2
  have hpadding : ((oddTensor (coreIndex m)).borderRank : ℝ) ≤ (tensor m).borderRank := by
    exact_mod_cast odd_borderRank_le (by lia : 0 < m)
  have hcoefficient : 0 ≤ 7 / 3 - ε / 2 := by linarith
  have hsmall := mul_le_mul_of_nonneg_left hdim hcoefficient
  nlinarith

/-- A single family, independent of epsilon, attains coefficient `7/3-o(1)`. -/
theorem eventually_lowerBound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (7 / 3 - ε) * (m : ℝ) ≤ (tensor m).borderRank := by
  filter_upwards [eventually_lowerBound_small (ε := min ε 1)
    (lt_min hε (by norm_num)) (min_le_right _ _)] with m hm
  have hmin := min_le_left ε 1
  have hdim : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

end Algebraic.Tensor3.Dissociated.Internal
