/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite reserve and resource bounds for the near-halving schedule

The exact entropy gap pays the full rounded field width and the splitting
error. Induction bounds every actual block by the initial width, allowing
one logarithmic budget to control all levels. The final seed pair is included
in the resource bound, with its one-step larger condenser error exponent.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem nearHalvingBlockEntropy_succ (h Q : Nat) {i : Nat} (level : i < h) :
    nearHalvingBlockEntropy h Q i = 2 * nearHalvingBlockEntropy h Q (i + 1) + 2 ^ (h - i) * Q := by
  unfold nearHalvingBlockEntropy
  rw [show h - i = h - (i + 1) + 1 by lia, pow_succ]
  ring

theorem nearHalvingBlockEntropy_le_initial (h Q i : Nat) :
    nearHalvingBlockEntropy h Q i ≤ nearHalvingBlockEntropy h Q 0 := by
  unfold nearHalvingBlockEntropy
  simp only [Nat.sub_zero]
  apply Nat.mul_le_mul_right Q
  exact Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le h i)) (by lia)

theorem nearHalvingBlockEntropy_last (h Q : Nat) :
    nearHalvingBlockEntropy h Q h = (8 * h + 8) * Q := by
  simp [nearHalvingBlockEntropy]

theorem nearHalvingBlock_split_numeric (h Q B E : Nat) (reserve : 2 * (B + 2 * E) ≤ Q)
    {i : Nat} (level : i < h) :
    nearHalvingBlockRate h * (B + 2 * (nearHalvingBlockEntropy h Q (i + 1) + E)) ≤
      (nearHalvingBlockRate h - 1) * nearHalvingBlockEntropy h Q i := by
  have distance : h - i ≤ h := Nat.sub_le h i
  have power : 2 ≤ 2 ^ (h - i) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ h - i by lia)
  have distance_scaled := Nat.mul_le_mul_right (2 ^ (h - i)) distance
  have power_scaled := Nat.mul_le_mul_left (7 * h + 8) power
  have coefficient : 8 * h + 8 + (8 * h + 8 + (h - i)) * 2 ^ (h - i) ≤
      16 * (h + 1) * 2 ^ (h - i) := by
    nlinarith only [distance_scaled, power_scaled]
  have margin : (8 * h + 8) * Q + nearHalvingBlockEntropy h Q i ≤
      nearHalvingBlockRate h * (2 ^ (h - i) * Q) := by
    have scaled := Nat.mul_le_mul_right Q coefficient
    dsimp only [nearHalvingBlockEntropy, nearHalvingBlockRate]
    nlinarith only [scaled]
  have paid : nearHalvingBlockRate h * (B + 2 * E) ≤ (8 * h + 8) * Q := by
    have scaled := Nat.mul_le_mul_left (8 * h + 8) reserve
    dsimp only [nearHalvingBlockRate]
    nlinarith only [scaled]
  have pre : nearHalvingBlockRate h * (B + 2 * (nearHalvingBlockEntropy h Q (i + 1) + E)) +
      nearHalvingBlockEntropy h Q i ≤
      nearHalvingBlockRate h * nearHalvingBlockEntropy h Q i := by
    rw [nearHalvingBlockEntropy_succ h Q level] at margin ⊢
    nlinarith only [margin, paid]
  have pred : nearHalvingBlockRate h - 1 + 1 = nearHalvingBlockRate h :=
    Nat.sub_add_cancel (by dsimp [nearHalvingBlockRate]; lia)
  have pred_scaled := congrArg (fun z => z * nearHalvingBlockEntropy h Q i) pred
  nlinarith only [pre, pred_scaled]

theorem nearHalvingBlockSeedWidth_le_of_width (N h Q E i : Nat)
    (bounded : nearHalvingBlockWidth N h Q E i ≤ N) :
    nearHalvingBlockSeedWidth N h Q E i ≤
      6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E := by
  calc
    nearHalvingBlockSeedWidth N h Q E i ≤ 6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget (nearHalvingBlockWidth N h Q E i)
          (nearHalvingBlockEntropy h Q i) E :=
      explicitCondenser_fieldBits_le _ _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _
      (explicitCondenserBudget_mono
        bounded (nearHalvingBlockEntropy_le_initial h Q i))

theorem nearHalvingBlock_step (N h Q E : Nat)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i < h) (bounded : nearHalvingBlockWidth N h Q E i ≤ N) :
    nearHalvingBlockEntropy h Q (i + 1) ≤ nearHalvingBlockWidth N h Q E (i + 1) ∧
      nearHalvingBlockWidth N h Q E (i + 1) + nearHalvingBlockEntropy h Q (i + 1) + E ≤
        nearHalvingBlockEntropy h Q i := by
  have seed := nearHalvingBlockSeedWidth_le_of_width N h Q E i bounded
  have numeric := nearHalvingBlock_split_numeric h Q _ E reserve level
  apply explicitCondenserPair_split_budget (nearHalvingBlockWidth N h Q E i)
    (nearHalvingBlockEntropy h Q i) E (nearHalvingBlockRate h)
    (nearHalvingBlockEntropy h Q (i + 1)) E (by dsimp [nearHalvingBlockRate]; lia)
  exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right seed _)).trans numeric

theorem nearHalvingBlockWidth_bounds (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i ≤ h) :
    nearHalvingBlockEntropy h Q i ≤ nearHalvingBlockWidth N h Q E i ∧
      nearHalvingBlockWidth N h Q E i ≤ N := by
  induction i with
  | zero => exact ⟨capacity, le_rfl⟩
  | succ i ih =>
    have previous := ih (by lia)
    have split := nearHalvingBlock_step N h Q E reserve (by lia : i < h) previous.2
    have upper : nearHalvingBlockWidth N h Q E (i + 1) ≤ nearHalvingBlockEntropy h Q i := by lia
    exact ⟨split.1, upper.trans ((nearHalvingBlockEntropy_le_initial h Q i).trans capacity)⟩

theorem nearHalvingBlock_split_budget (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i < h) :
    nearHalvingBlockEntropy h Q (i + 1) ≤ nearHalvingBlockWidth N h Q E (i + 1) ∧
      nearHalvingBlockWidth N h Q E (i + 1) + nearHalvingBlockEntropy h Q (i + 1) + E ≤
        nearHalvingBlockEntropy h Q i :=
  nearHalvingBlock_step N h Q E reserve level
    (nearHalvingBlockWidth_bounds N h Q E capacity reserve level.le).2

theorem nearHalvingBlock_split_budget_of_bound (N h Q E T : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (common : explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E ≤ T)
    (reserve : 12 * (nearHalvingBlockRate h + 1) * T + 4 * E ≤ Q) {i : Nat} (level : i < h) :
    nearHalvingBlockEntropy h Q (i + 1) ≤ nearHalvingBlockWidth N h Q E (i + 1) ∧
      nearHalvingBlockWidth N h Q E (i + 1) + nearHalvingBlockEntropy h Q (i + 1) + E ≤
        nearHalvingBlockEntropy h Q i := by
  apply nearHalvingBlock_split_budget N h Q E capacity (level := level)
  have scaled := Nat.mul_le_mul_left (12 * (nearHalvingBlockRate h + 1)) common
  nlinarith only [scaled, reserve]

theorem nearHalvingBlockLeafLength_budget (h Q E : Nat) (reserve : 2 * E ≤ Q) :
    nearHalvingBlockLeafLength h Q + 2 * E ≤ nearHalvingBlockEntropy h Q h := by
  rw [nearHalvingBlockEntropy_last]
  dsimp only [nearHalvingBlockLeafLength]
  nlinarith only [reserve]

theorem nearHalvingBlockEntropy_mass (h Q : Nat) {i : Nat} (level : i ≤ h) :
    2 ^ i * nearHalvingBlockEntropy h Q i = 2 ^ h * (8 * h + 8 + (h - i)) * Q := by
  dsimp only [nearHalvingBlockEntropy]
  calc
    _ = (2 ^ i * 2 ^ (h - i)) * (8 * h + 8 + (h - i)) * Q := by ring
    _ = _ := by rw [← pow_add, show i + (h - i) = h by lia]

theorem nearHalvingBlockEntropy_mass_le (h Q : Nat) {i : Nat} (level : i ≤ h) :
    2 ^ i * nearHalvingBlockEntropy h Q i ≤ nearHalvingBlockEntropy h Q 0 := by
  rw [nearHalvingBlockEntropy_mass h Q level]
  simpa only [nearHalvingBlockEntropy, Nat.sub_zero] using
    Nat.mul_le_mul_right Q (Nat.mul_le_mul_left (2 ^ h)
      (show 8 * h + 8 + (h - i) ≤ 8 * h + 8 + h by lia))

theorem nearHalvingBlock_payload_le (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i ≤ h) : 2 ^ i * nearHalvingBlockWidth N h Q E i ≤ 2 * N := by
  cases i with
  | zero => simp only [pow_zero, nearHalvingBlockWidth, one_mul]; lia
  | succ i =>
    have split := nearHalvingBlock_split_budget N h Q E capacity reserve (by lia : i < h)
    calc
      2 ^ (i + 1) * nearHalvingBlockWidth N h Q E (i + 1) ≤
          2 ^ (i + 1) * nearHalvingBlockEntropy h Q i :=
        Nat.mul_le_mul_left _ (by lia)
      _ = 2 * (2 ^ i * nearHalvingBlockEntropy h Q i) := by rw [pow_succ]; ring
      _ ≤ 2 * nearHalvingBlockEntropy h Q 0 :=
        Nat.mul_le_mul_left 2 (nearHalvingBlockEntropy_mass_le h Q (by lia))
      _ ≤ 2 * N := Nat.mul_le_mul_left 2 capacity

theorem nearHalvingBlock_seed_sum_le (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q) :
    (Finset.range h).sum (nearHalvingBlockSeedWidth N h Q E) ≤
      h * (6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E) := by
  calc
    _ ≤ (Finset.range h).sum (fun _ =>
        6 * (nearHalvingBlockRate h + 1) *
          explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E) := by
      apply Finset.sum_le_sum
      intro i hi
      exact nearHalvingBlockSeedWidth_le_of_width N h Q E i
        (nearHalvingBlockWidth_bounds N h Q E capacity reserve (Finset.mem_range.mp hi).le).2
    _ = _ := by simp

theorem nearHalvingBlockOutputBits_accounting (h Q : Nat) :
    9 * nearHalvingBlockOutputBits h Q + 2 ^ h * Q = 8 * nearHalvingBlockEntropy h Q 0 := by
  simp only [nearHalvingBlockOutputBits, nearHalvingBlockLeafLength,
    nearHalvingBlockEntropy, Nat.sub_zero]
  ring

theorem nearHalvingBlockOutputBits_lower (h Q : Nat) :
    7 * nearHalvingBlockEntropy h Q 0 ≤ 8 * nearHalvingBlockOutputBits h Q := by
  simp only [nearHalvingBlockOutputBits, nearHalvingBlockLeafLength,
    nearHalvingBlockEntropy, Nat.sub_zero]
  nlinarith only [Nat.zero_le (h * 2 ^ h * Q)]

theorem nearHalvingBlock_count_le (h Q : Nat) (positive : 0 < Q) {i : Nat} (level : i ≤ h) :
    2 ^ i ≤ nearHalvingBlockEntropy h Q 0 := by
  have lower : Q ≤ nearHalvingBlockEntropy h Q i :=
    Nat.le_mul_of_pos_left Q
      (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) (by lia))
  calc
    2 ^ i = 2 ^ i * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ i * nearHalvingBlockEntropy h Q i := Nat.mul_le_mul_left _ (by lia)
    _ ≤ _ := nearHalvingBlockEntropy_mass_le h Q level

theorem nearHalvingBlock_leaf_seed_le (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q) :
    let ell := nearHalvingBlockLeafLength h Q
    2 * 3 ^ oneShotCondenserExponent (nearHalvingBlockWidth N h Q E h) ell E +
      2 * 3 ^ oneShotHashExponent (nearHalvingBlockWidth N h Q E h) ell E ≤
        84 * (explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 1) +
          18 * ell + 24 * E + 6 := by
  let ell := nearHalvingBlockLeafLength h Q
  change 2 * 3 ^ oneShotCondenserExponent (nearHalvingBlockWidth N h Q E h) ell E +
    2 * 3 ^ oneShotHashExponent (nearHalvingBlockWidth N h Q E h) ell E ≤
      84 * (explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 1) + 18 * ell + 24 * E + 6
  have width_le := (nearHalvingBlockWidth_bounds N h Q E capacity reserve (i := h) le_rfl).2
  have entropy_le : ell + 2 * E ≤ nearHalvingBlockEntropy h Q 0 :=
    (nearHalvingBlockLeafLength_budget h Q E (by lia)).trans
      (nearHalvingBlockEntropy_le_initial h Q h)
  have budget : explicitCondenserBudget (nearHalvingBlockWidth N h Q E h) (ell + 2 * E) (E + 1) ≤
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 1 := by
    calc
      _ ≤ explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) (E + 1) :=
        explicitCondenserBudget_mono width_le entropy_le
      _ = _ := by simp only [explicitCondenserBudget]; ring
  have condenser : 2 * 3 ^ oneShotCondenserExponent (nearHalvingBlockWidth N h Q E h) ell E ≤
      12 * (explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 1) := by
    have field := explicitCondenser_fieldBits_le
      (nearHalvingBlockWidth N h Q E h) (ell + 2 * E) (E + 1) 1
    have scaled := Nat.mul_le_mul_left 12 budget
    change 2 * 3 ^ sparseFieldExponent 1 _ ≤ _ at field
    dsimp only [oneShotCondenserExponent]
    nlinarith only [field, scaled]
  have seed := oneShotSeedBits_le (nearHalvingBlockWidth N h Q E h) ell E
  nlinarith only [seed, condenser]

theorem nearHalvingBlockSeedBits_le (N h Q E : Nat) (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q) :
    nearHalvingBlockSeedBits N h Q E ≤
      h * (6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E) +
        (84 * (explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 1) +
          18 * nearHalvingBlockLeafLength h Q + 24 * E + 6) :=
  Nat.add_le_add (nearHalvingBlock_seed_sum_le N h Q E capacity reserve)
    (nearHalvingBlock_leaf_seed_le N h Q E capacity reserve)

theorem nearHalvingBlockSeedWidth_le (N h Q E : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (reserve : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)
    {i : Nat} (level : i ≤ h) :
    nearHalvingBlockSeedWidth N h Q E i ≤
      6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E :=
  nearHalvingBlockSeedWidth_le_of_width N h Q E i
    (nearHalvingBlockWidth_bounds N h Q E capacity reserve level).2

theorem nearHalvingBlockSeedBits_le_of_bound (N h Q E T : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ N)
    (common : explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E ≤ T)
    (reserve : 12 * (nearHalvingBlockRate h + 1) * T + 4 * E ≤ Q) :
    nearHalvingBlockSeedBits N h Q E ≤
      h * (6 * (nearHalvingBlockRate h + 1) * T) +
        (84 * (T + 1) + 18 * nearHalvingBlockLeafLength h Q + 24 * E + 6) := by
  have enough : 2 * (6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q := by
    have scaled := Nat.mul_le_mul_left (12 * (nearHalvingBlockRate h + 1)) common
    nlinarith only [scaled, reserve]
  apply (nearHalvingBlockSeedBits_le N h Q E capacity enough).trans
  have internal_seeds := Nat.mul_le_mul_left (h * (6 * (nearHalvingBlockRate h + 1))) common
  have leaf_seeds := Nat.mul_le_mul_left 84 common
  nlinarith only [internal_seeds, leaf_seeds]

end Algebraic.Cutwidth.Extractor.Internal
