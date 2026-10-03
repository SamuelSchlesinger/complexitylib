/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic depth selection and ceiling-reserve estimates

Exact power bounds from the size guard control both the reserve and the
output rounding quantum. The reserve pays the full sparse-field width;
the final seed estimate includes the one-shot pair shared by all leaves.
The offset and constants are deductions for this library's rounded fields.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem gammaBlock_pos {b : Nat} (guard : GammaBlockSizeGuard b) : 0 < b := by
  by_contra positive
  have zero : b = 0 := by lia
  simp [GammaBlockSizeGuard, zero] at guard

theorem gammaBlockDepth_le (b : Nat) : gammaBlockDepth b ≤ gammaBlockLog b := by
  have floor := (Nat.log_le_clog 2 b).trans (Nat.clog_mono_right 2 (Nat.le_succ b))
  dsimp only [gammaBlockDepth, gammaBlockLog]
  lia

private theorem gammaBlockDepth_add {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockDepth b + 3 * Nat.clog 2 (gammaBlockLog b + 1) + 15 = Nat.log 2 b := by
  dsimp only [GammaBlockSizeGuard] at guard
  dsimp only [gammaBlockDepth]
  lia

private theorem pow_clog_succ_le (L : Nat) : 2 ^ Nat.clog 2 (L + 1) ≤ 2 * (L + 1) := by
  by_cases zero : L = 0
  · simp [zero]
  have positive := Nat.clog_pos (by decide : 1 < 2) (show 1 < L + 1 by lia)
  have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (show 1 < L + 1 by lia)
  calc
    2 ^ Nat.clog 2 (L + 1) = 2 * 2 ^ (Nat.clog 2 (L + 1) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel positive]
    _ ≤ 2 * (L + 1) := Nat.mul_le_mul_left 2 (Nat.le_of_lt previous)

theorem gammaBlock_power_lower {b : Nat} (guard : GammaBlockSizeGuard b) :
    2 ^ gammaBlockDepth b * 32768 * (gammaBlockLog b + 1) ^ 3 ≤ b := by
  have lower := Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < 2) (gammaBlockLog b + 1)) 3
  calc
    _ ≤ 2 ^ gammaBlockDepth b * 32768 *
        (2 ^ Nat.clog 2 (gammaBlockLog b + 1)) ^ 3 := Nat.mul_le_mul_left _ lower
    _ = 2 ^ Nat.log 2 b := by
      rw [← gammaBlockDepth_add guard]
      simp only [pow_add, Nat.mul_comm 3 (Nat.clog 2 (gammaBlockLog b + 1)), pow_mul]
      norm_num
      ring
    _ ≤ b := Nat.pow_log_le_self 2 (Nat.ne_of_gt (gammaBlock_pos guard))

theorem gammaBlock_power_upper {b : Nat} (guard : GammaBlockSizeGuard b) :
    b < 2 ^ gammaBlockDepth b * 524288 * (gammaBlockLog b + 1) ^ 3 := by
  have upper := Nat.pow_le_pow_left (pow_clog_succ_le (gammaBlockLog b)) 3
  calc
    b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by decide) b
    _ = 2 ^ gammaBlockDepth b * 65536 *
        (2 ^ Nat.clog 2 (gammaBlockLog b + 1)) ^ 3 := by
      rw [← gammaBlockDepth_add guard]
      simp only [pow_add, Nat.mul_comm 3 (Nat.clog 2 (gammaBlockLog b + 1)), pow_mul]
      norm_num
      ring
    _ ≤ 2 ^ gammaBlockDepth b * 65536 * (2 * (gammaBlockLog b + 1)) ^ 3 :=
      Nat.mul_le_mul_left _ upper
    _ = _ := by ring

theorem gammaBlockOutputQuantum_pos (b : Nat) : 0 < gammaBlockOutputQuantum b := by
  unfold gammaBlockOutputQuantum
  positivity

theorem gammaBlock_output_ge (b : Nat) :
    b ≤ 2 ^ gammaBlockDepth b * gammaBlockLeafLength b := by
  simpa only [gammaBlockReserve, gammaBlockOutputQuantum, gammaBlockLeafLength, Nat.mul_assoc]
    using condenserCoordinates_capacity (k := b) (gammaBlockOutputQuantum_pos b)

private theorem gammaBlock_rounding_le (b : Nat) :
    2 ^ gammaBlockDepth b * gammaBlockLeafLength b ≤ b + gammaBlockOutputQuantum b := by
  have rounded := Nat.mul_div_le (b + gammaBlockOutputQuantum b - 1)
    (gammaBlockOutputQuantum b)
  simpa only [gammaBlockLeafLength, gammaBlockReserve, gammaBlockOutputQuantum,
    condenserCoordinates, Nat.mul_assoc] using rounded.trans (Nat.sub_le _ _)

private theorem le_cube_succ (L : Nat) : L + 1 ≤ (L + 1) ^ 3 := by
  calc
    L + 1 = (L + 1) * 1 * 1 := by ring
    _ ≤ (L + 1) * (L + 1) * (L + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by lia)) (by lia)
    _ = _ := by ring

theorem gammaBlockOutputQuantum_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    2 * gammaBlockOutputQuantum b ≤ b := by
  have depth := gammaBlockDepth_le b
  have cube := le_cube_succ (gammaBlockLog b)
  have coefficient : 2 * (8 * gammaBlockDepth b + 7) ≤
      32768 * (gammaBlockLog b + 1) ^ 3 := by nlinarith only [depth, cube]
  calc
    _ = 2 ^ gammaBlockDepth b * (2 * (8 * gammaBlockDepth b + 7)) := by
      unfold gammaBlockOutputQuantum
      ring
    _ ≤ 2 ^ gammaBlockDepth b * (32768 * (gammaBlockLog b + 1) ^ 3) :=
      Nat.mul_le_mul_left _ coefficient
    _ ≤ b := by simpa only [Nat.mul_assoc] using gammaBlock_power_lower guard

theorem gammaBlockInputEntropy_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockInputEntropy b ≤ 2 * b := by
  have ratio : 7 * gammaBlockInputEntropy b ≤
      8 * (2 ^ gammaBlockDepth b * gammaBlockLeafLength b) := by
    dsimp only [gammaBlockInputEntropy, gammaBlockLeafLength]
    nlinarith only [Nat.zero_le
      (2 ^ gammaBlockDepth b * gammaBlockDepth b * gammaBlockReserve b)]
  have rounding := gammaBlock_rounding_le b
  have quantum := gammaBlockOutputQuantum_le guard
  lia

theorem gammaBlockReserve_lower {b : Nat} (guard : GammaBlockSizeGuard b) :
    4096 * (gammaBlockLog b + 1) ^ 2 ≤ gammaBlockReserve b := by
  have base : 32768 * (gammaBlockLog b + 1) ^ 3 ≤
      (8 * gammaBlockDepth b + 7) * gammaBlockReserve b := by
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ gammaBlockDepth b) _ (by positivity)
    simpa only [gammaBlockLeafLength, Nat.mul_assoc] using
      (gammaBlock_power_lower guard).trans (gammaBlock_output_ge b)
  have coefficient : 8 * gammaBlockDepth b + 7 ≤ 8 * (gammaBlockLog b + 1) := by
    have := gammaBlockDepth_le b
    lia
  apply Nat.le_of_mul_le_mul_left (c := 8 * (gammaBlockLog b + 1)) _ (by positivity)
  calc
    _ = 32768 * (gammaBlockLog b + 1) ^ 3 := by ring
    _ ≤ (8 * gammaBlockDepth b + 7) * gammaBlockReserve b := base
    _ ≤ _ := Nat.mul_le_mul_right _ coefficient

theorem gammaBlockReserve_pos {b : Nat} (guard : GammaBlockSizeGuard b) :
    0 < gammaBlockReserve b := by
  have lower := gammaBlockReserve_lower guard
  have positive : 0 < 4096 * (gammaBlockLog b + 1) ^ 2 := by positivity
  lia

theorem gammaBlockBudget_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    explicitCondenserBudget (8 * b) (gammaBlockInputEntropy b) (gammaBlockErrorExponent b) ≤
      13 * (gammaBlockLog b + 1) := by
  have input := Nat.le_pow_clog (by decide : 1 < 2) (b + 1)
  have entropy := gammaBlockInputEntropy_le guard
  have first : 8 * b + 1 ≤ 8 * 2 ^ gammaBlockLog b := by
    change b + 1 ≤ 2 ^ gammaBlockLog b at input
    lia
  have second : gammaBlockInputEntropy b + 1 ≤ 2 * 2 ^ gammaBlockLog b := by
    change b + 1 ≤ 2 ^ gammaBlockLog b at input
    lia
  have product := Nat.mul_le_mul first second
  have power : 2 ^ (2 * gammaBlockLog b + 8) = 256 * (2 ^ gammaBlockLog b) ^ 2 := by
    rw [pow_add, Nat.mul_comm 2 (gammaBlockLog b), pow_mul]
    norm_num
    ring
  have target : 9 * (8 * b + 1) * (gammaBlockInputEntropy b + 1) ≤
      2 ^ (2 * gammaBlockLog b + 8) := by
    rw [power]
    nlinarith only [product, Nat.zero_le ((2 ^ gammaBlockLog b) ^ 2)]
  have logarithm := Nat.clog_le_of_le_pow target
  have depth := gammaBlockDepth_le b
  dsimp only [explicitCondenserBudget, gammaBlockErrorExponent]
  lia

theorem gammaBlock_split_budget {b : Nat} (guard : GammaBlockSizeGuard b) :
    12 * (16 * (gammaBlockDepth b + 1) + 1) *
        explicitCondenserBudget (8 * b) (gammaBlockInputEntropy b) (gammaBlockErrorExponent b) +
      4 * gammaBlockErrorExponent b ≤ gammaBlockReserve b := by
  have depth := gammaBlockDepth_le b
  have budget := gammaBlockBudget_le guard
  have reserve := gammaBlockReserve_lower guard
  have rate : 16 * (gammaBlockDepth b + 1) + 1 ≤ 17 * (gammaBlockLog b + 1) := by lia
  have product := Nat.mul_le_mul rate budget
  dsimp only [gammaBlockErrorExponent] at budget product ⊢
  nlinarith

theorem gammaBlockLeafLength_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockLeafLength b ≤ 524296 * (gammaBlockLog b + 1) ^ 3 := by
  have lower := gammaBlock_rounding_le b
  have upper := gammaBlock_power_upper guard
  have depth := gammaBlockDepth_le b
  have cube := le_cube_succ (gammaBlockLog b)
  have coefficient : 8 * gammaBlockDepth b + 7 ≤ 8 * (gammaBlockLog b + 1) ^ 3 := by
    nlinarith only [depth, cube]
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ gammaBlockDepth b) _ (by positivity)
  calc
    _ ≤ b + gammaBlockOutputQuantum b := lower
    _ ≤ 2 ^ gammaBlockDepth b * 524288 * (gammaBlockLog b + 1) ^ 3 +
        2 ^ gammaBlockDepth b * (8 * gammaBlockDepth b + 7) :=
      Nat.add_le_add_right upper.le _
    _ ≤ 2 ^ gammaBlockDepth b * 524288 * (gammaBlockLog b + 1) ^ 3 +
        2 ^ gammaBlockDepth b * (8 * (gammaBlockLog b + 1) ^ 3) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ coefficient) _
    _ = _ := by ring

theorem gammaBlockInputEntropy_eq (b : Nat) :
    gammaBlockInputEntropy b =
      nearHalvingBlockEntropy (gammaBlockDepth b) (gammaBlockReserve b) 0 := by
  simp only [gammaBlockInputEntropy, nearHalvingBlockEntropy, Nat.sub_zero]
  ring

theorem gammaBlockLeafLength_eq (b : Nat) :
    gammaBlockLeafLength b = nearHalvingBlockLeafLength (gammaBlockDepth b) (gammaBlockReserve b) :=
  rfl

theorem gammaBlockSeedBits_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    nearHalvingBlockSeedBits (8 * b) (gammaBlockDepth b) (gammaBlockReserve b)
        (gammaBlockErrorExponent b) ≤ 2 ^ 27 * gammaBlockLog b ^ 3 := by
  have depth := gammaBlockDepth_le b
  have reserve := gammaBlockReserve_lower guard
  have rate : nearHalvingBlockRate (gammaBlockDepth b) + 1 ≤ 17 * (gammaBlockLog b + 1) := by
    dsimp only [nearHalvingBlockRate]
    lia
  have common : explicitCondenserBudget (8 * b)
      (nearHalvingBlockEntropy (gammaBlockDepth b) (gammaBlockReserve b) 0)
      (gammaBlockErrorExponent b) ≤ 13 * (gammaBlockLog b + 1) := by
    rw [← gammaBlockInputEntropy_eq]
    exact gammaBlockBudget_le guard
  have capacity : nearHalvingBlockEntropy (gammaBlockDepth b) (gammaBlockReserve b) 0 ≤ 8 * b := by
    rw [← gammaBlockInputEntropy_eq]
    have := gammaBlockInputEntropy_le guard
    lia
  have paid : 12 * (nearHalvingBlockRate (gammaBlockDepth b) + 1) *
      (13 * (gammaBlockLog b + 1)) + 4 * gammaBlockErrorExponent b ≤ gammaBlockReserve b := by
    have product := Nat.mul_le_mul_right (13 * (gammaBlockLog b + 1)) rate
    dsimp only [gammaBlockErrorExponent]
    nlinarith only [depth, reserve, product]
  have total := nearHalvingBlockSeedBits_le_of_bound (8 * b) (gammaBlockDepth b)
    (gammaBlockReserve b) (gammaBlockErrorExponent b) (13 * (gammaBlockLog b + 1))
    capacity common paid
  rw [← gammaBlockLeafLength_eq] at total
  have internalSeeds : gammaBlockDepth b * (6 * (nearHalvingBlockRate (gammaBlockDepth b) + 1) *
      (13 * (gammaBlockLog b + 1))) ≤ 1326 * (gammaBlockLog b + 1) ^ 3 := by
    calc
      _ ≤ (gammaBlockLog b + 1) * (6 * (17 * (gammaBlockLog b + 1)) *
          (13 * (gammaBlockLog b + 1))) :=
        Nat.mul_le_mul (by lia)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 rate))
      _ = _ := by ring
  have cube := le_cube_succ (gammaBlockLog b)
  have small : 84 * (13 * (gammaBlockLog b + 1) + 1) +
      24 * gammaBlockErrorExponent b + 6 ≤ 1278 * (gammaBlockLog b + 1) ^ 3 := by
    dsimp only [gammaBlockErrorExponent]
    nlinarith only [depth, cube]
  have leaf := gammaBlockLeafLength_le guard
  have bound : nearHalvingBlockSeedBits (8 * b) (gammaBlockDepth b) (gammaBlockReserve b)
      (gammaBlockErrorExponent b) ≤ 9439932 * (gammaBlockLog b + 1) ^ 3 := by
    nlinarith only [total, internalSeeds, small, leaf]
  have logpos : 0 < gammaBlockLog b :=
    Nat.clog_pos (by decide) (by have := gammaBlock_pos guard; lia)
  have comparison : (gammaBlockLog b + 1) ^ 3 ≤ 8 * gammaBlockLog b ^ 3 := by
    calc
      _ ≤ (2 * gammaBlockLog b) ^ 3 := Nat.pow_le_pow_left (by lia) 3
      _ = _ := by ring
  calc
    _ ≤ 9439932 * (gammaBlockLog b + 1) ^ 3 := bound
    _ ≤ 9439932 * (8 * gammaBlockLog b ^ 3) := Nat.mul_le_mul_left _ comparison
    _ ≤ _ := by norm_num; nlinarith

end Algebraic.Cutwidth.Extractor.Internal
