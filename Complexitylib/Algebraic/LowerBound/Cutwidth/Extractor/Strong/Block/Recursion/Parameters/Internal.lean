/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounds for the constant-rate block schedule

Monotonicity of the logarithmic budget bounds every field seed using the
initial parameters. The leaf reserve then pays the split budget at every
executed level, and induction controls the actual rounded block widths.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem recursiveBlockEntropy_last (h Q : Nat) : recursiveBlockEntropy h Q h = Q := by
  simp [recursiveBlockEntropy]

theorem recursiveBlockEntropy_succ (h Q : Nat) {i : Nat} (level : i < h) :
    recursiveBlockEntropy h Q i = 4 * recursiveBlockEntropy h Q (i + 1) := by
  unfold recursiveBlockEntropy
  rw [show h - i = h - (i + 1) + 1 by lia, pow_succ]
  ring

theorem recursiveBlockEntropy_reserve_le (h Q i : Nat) :
    Q ≤ recursiveBlockEntropy h Q i :=
  Nat.le_mul_of_pos_left Q (Nat.pow_pos (by decide : 0 < 4))

theorem recursiveBlockEntropy_le_initial (h Q i : Nat) :
    recursiveBlockEntropy h Q i ≤ recursiveBlockEntropy h Q 0 := by
  simpa only [recursiveBlockEntropy, Nat.sub_zero] using
    Nat.mul_le_mul_right Q (Nat.pow_le_pow_right (by decide : 0 < 4) (Nat.sub_le h i))

theorem explicitCondenserBudget_mono {n k n' k' E : Nat} (width : n ≤ n')
    (entropy : k ≤ k') :
    explicitCondenserBudget n k E ≤ explicitCondenserBudget n' k' E := by
  have logarithm := Nat.clog_mono_right 2
    (Nat.mul_le_mul (Nat.mul_le_mul_left 9 (Nat.add_le_add_right width 1))
      (Nat.add_le_add_right entropy 1))
  unfold explicitCondenserBudget
  lia

theorem recursiveBlockSeedWidth_le_of_width (initial h Q E i : Nat)
    (width : recursiveBlockWidth initial h Q E i ≤ initial) :
    recursiveBlockSeedWidth initial h Q E i ≤
      24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E := by
  calc
    recursiveBlockSeedWidth initial h Q E i ≤
        24 * explicitCondenserBudget (recursiveBlockWidth initial h Q E i)
          (recursiveBlockEntropy h Q i) E :=
      explicitCondenser_fieldBits_le _ _ E 3
    _ ≤ 24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E :=
      Nat.mul_le_mul_left 24
        (explicitCondenserBudget_mono width (recursiveBlockEntropy_le_initial h Q i))

theorem recursiveBlock_step (initial h Q E : Nat)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i < h)
    (width : recursiveBlockWidth initial h Q E i ≤ initial) :
    recursiveBlockEntropy h Q (i + 1) ≤ recursiveBlockWidth initial h Q E (i + 1) ∧
      recursiveBlockWidth initial h Q E (i + 1) +
        recursiveBlockEntropy h Q (i + 1) + E ≤ recursiveBlockEntropy h Q i := by
  have seed := recursiveBlockSeedWidth_le_of_width initial h Q E i width
  have reserve := recursiveBlockEntropy_reserve_le h Q (i + 1)
  have ratio := recursiveBlockEntropy_succ h Q level
  apply explicitCondenserPair_split_budget (recursiveBlockWidth initial h Q E i)
    (recursiveBlockEntropy h Q i) E 3 (recursiveBlockEntropy h Q (i + 1)) E (by decide)
  change 3 * (recursiveBlockSeedWidth initial h Q E i +
    2 * (recursiveBlockEntropy h Q (i + 1) + E)) ≤ _
  lia

theorem recursiveBlockWidth_bounds (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i ≤ h) :
    recursiveBlockEntropy h Q i ≤ recursiveBlockWidth initial h Q E i ∧
      recursiveBlockWidth initial h Q E i ≤ initial := by
  induction i with
  | zero => exact ⟨capacity, le_rfl⟩
  | succ i ih =>
    have previous := ih (by lia)
    have step := recursiveBlock_step initial h Q E budget (by lia : i < h) previous.2
    refine ⟨step.1, ?_⟩
    have upper : recursiveBlockWidth initial h Q E (i + 1) ≤ recursiveBlockEntropy h Q i :=
      by lia
    exact upper.trans ((recursiveBlockEntropy_le_initial h Q i).trans capacity)

theorem recursiveBlock_split_budget (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i < h) :
    recursiveBlockEntropy h Q (i + 1) ≤ recursiveBlockWidth initial h Q E (i + 1) ∧
      recursiveBlockWidth initial h Q E (i + 1) +
        recursiveBlockEntropy h Q (i + 1) + E ≤ recursiveBlockEntropy h Q i :=
  recursiveBlock_step initial h Q E budget level
    (recursiveBlockWidth_bounds initial h Q E capacity budget (Nat.le_of_lt level)).2

theorem recursiveBlockSeedWidth_le (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i ≤ h) :
    recursiveBlockSeedWidth initial h Q E i ≤
      24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E :=
  recursiveBlockSeedWidth_le_of_width initial h Q E i
    (recursiveBlockWidth_bounds initial h Q E capacity budget level).2

theorem recursiveBlock_entropy_mass_le (h Q : Nat) {i : Nat} (level : i ≤ h) :
    2 ^ i * recursiveBlockEntropy h Q i ≤ recursiveBlockEntropy h Q 0 := by
  induction i with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ i ih =>
    have ratio := recursiveBlockEntropy_succ h Q (by lia : i < h)
    calc
      2 ^ (i + 1) * recursiveBlockEntropy h Q (i + 1) =
          2 ^ i * (2 * recursiveBlockEntropy h Q (i + 1)) := by
        rw [pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ i * (4 * recursiveBlockEntropy h Q (i + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide : 2 ≤ 4))
      _ = 2 ^ i * recursiveBlockEntropy h Q i := by rw [← ratio]
      _ ≤ recursiveBlockEntropy h Q 0 := ih (by lia)

theorem recursiveBlock_payload_le (initial h Q E : Nat)
    (capacity : recursiveBlockEntropy h Q 0 ≤ initial)
    (budget : 3 * (24 * explicitCondenserBudget initial (recursiveBlockEntropy h Q 0) E) +
      6 * E ≤ 2 * Q) {i : Nat} (level : i ≤ h) :
    2 ^ i * recursiveBlockWidth initial h Q E i ≤ 2 * initial := by
  cases i with
  | zero =>
    change 1 * initial ≤ 2 * initial
    lia
  | succ i =>
    have split := recursiveBlock_split_budget initial h Q E capacity budget (by lia : i < h)
    have upper : recursiveBlockWidth initial h Q E (i + 1) ≤ recursiveBlockEntropy h Q i :=
      by lia
    calc
      2 ^ (i + 1) * recursiveBlockWidth initial h Q E (i + 1) ≤
          2 ^ (i + 1) * recursiveBlockEntropy h Q i := Nat.mul_le_mul_left _ upper
      _ = 2 * (2 ^ i * recursiveBlockEntropy h Q i) := by rw [pow_succ]; ring
      _ ≤ 2 * recursiveBlockEntropy h Q 0 :=
        Nat.mul_le_mul_left 2 (recursiveBlock_entropy_mass_le h Q (by lia))
      _ ≤ 2 * initial := Nat.mul_le_mul_left 2 capacity

theorem recursiveBlock_count_le (h Q : Nat) {i : Nat} (positive : 0 < Q) (level : i ≤ h) :
    2 ^ i ≤ recursiveBlockEntropy h Q 0 := by
  have retained : 1 ≤ recursiveBlockEntropy h Q i :=
    (Nat.succ_le_of_lt positive).trans (recursiveBlockEntropy_reserve_le h Q i)
  calc
    2 ^ i = 2 ^ i * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ i * recursiveBlockEntropy h Q i := Nat.mul_le_mul_left _ retained
    _ ≤ recursiveBlockEntropy h Q 0 := recursiveBlock_entropy_mass_le h Q level

end Algebraic.Cutwidth.Extractor.Internal
