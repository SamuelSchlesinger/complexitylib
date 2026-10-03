/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rounding and degree-budget arithmetic for sparse field sizes

The upper logarithm rounds the field bit length to twice a power of three.
Ceiling division controls the coordinate count. The rate inequality is
integer-valued, so no logarithm or real rounding convention is hidden.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem pow_clog_three_lt {n : Nat} (positive : 0 < n) :
    3 ^ Nat.clog 3 n < 3 * n := by
  by_cases small : n ≤ 1
  · have equal : n = 1 := by lia
    simp [equal]
  · have bigger : 1 < n := by lia
    have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 3) bigger
    have exponent : (Nat.clog 3 n).pred + 1 = Nat.clog 3 n :=
      Nat.succ_pred_eq_of_pos (Nat.clog_pos (by decide) bigger)
    calc
      3 ^ Nat.clog 3 n = 3 ^ (Nat.clog 3 n).pred * 3 := by
        rw [← pow_succ, exponent]
      _ < 3 * n := by nlinarith

theorem sparseFieldBits_lower (u T : Nat) :
    (u + 1) * T ≤ sparseFieldBits u T := by
  have rounded := Nat.le_pow_clog (by decide : 1 < 3) (((u + 1) * T + 1) / 2)
  unfold sparseFieldBits sparseFieldExponent
  lia

theorem sparseFieldBits_upper {u T : Nat} (positive : 0 < T) :
    sparseFieldBits u T ≤ 6 * ((u + 1) * T) := by
  have threshold : 0 < (u + 1) * T := Nat.mul_pos (by lia) positive
  have rounded := pow_clog_three_lt (n := ((u + 1) * T + 1) / 2) (by lia)
  unfold sparseFieldBits sparseFieldExponent
  lia

theorem sparsePowerBits_add {u T : Nat} :
    sparsePowerBits u T + T = sparseFieldBits u T := by
  have lower := sparseFieldBits_lower u T
  have bound : T ≤ (u + 1) * T := by nlinarith
  exact Nat.sub_add_cancel (bound.trans lower)

theorem sparsePowerBits_pos {u T : Nat} (rate : 0 < u) (positive : 0 < T) :
    0 < sparsePowerBits u T := by
  have lower := sparseFieldBits_lower u T
  have strict : T < (u + 1) * T := by nlinarith
  unfold sparsePowerBits
  lia

theorem sparsePowerBits_rate (u T : Nat) :
    u * sparseFieldBits u T ≤ (u + 1) * sparsePowerBits u T := by
  have lower := sparseFieldBits_lower u T
  have total := sparsePowerBits_add (u := u) (T := T)
  nlinarith

theorem condenserCoordinates_capacity {k r : Nat} (positive : 0 < r) :
    k ≤ r * condenserCoordinates k r := by
  exact le_smul_ceilDiv positive

theorem condenserCoordinates_le {k r : Nat} (positive : 0 < r) :
    condenserCoordinates k r ≤ k := by
  apply (ceilDiv_le_iff_le_mul positive).mpr
  nlinarith

theorem condenserCoordinates_output {u k r b : Nat}
    (rate : u * b ≤ (u + 1) * r) :
    u * (condenserCoordinates k r * b) ≤ (u + 1) * k + u * b := by
  let m := condenserCoordinates k r
  change u * (m * b) ≤ (u + 1) * k + u * b
  by_cases zero : m = 0
  · simp only [zero, Nat.zero_mul, Nat.mul_zero]
    exact Nat.zero_le _
  have count : 1 ≤ m := by lia
  have division : r * m ≤ k + r - 1 := by
    exact Nat.mul_div_le (k + r - 1) r
  have remainder : r * (m - 1) ≤ k := by
    rw [Nat.mul_sub_left_distrib]
    lia
  calc
    u * (m * b) = u * b + (u * b) * (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel count]
      ring
    _ ≤ u * b + ((u + 1) * r) * (m - 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right (m - 1) rate) _
    _ = u * b + (u + 1) * (r * (m - 1)) := by ring
    _ ≤ u * b + (u + 1) * k :=
      Nat.add_le_add_left (Nat.mul_le_mul_left (u + 1) remainder) _
    _ = (u + 1) * k + u * b := by ring

theorem condenserCoordinates_loss {D k r T : Nat} {error : ℝ}
    (positive : 0 < r) (budget : (D * k : ℝ) ≤ error * 2 ^ T) :
    (((D - 1) * (2 ^ r - 1) * condenserCoordinates k r : Nat) : ℝ) /
      2 ^ (r + T) ≤ error := by
  have count := condenserCoordinates_le (k := k) positive
  have loss : (D - 1) * (2 ^ r - 1) * condenserCoordinates k r ≤ D * k * 2 ^ r := by
    calc
      _ ≤ D * 2 ^ r * k :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)) count
      _ = D * k * 2 ^ r := by ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (r + T))).mpr
  calc
    _ ≤ (D * k : ℝ) * 2 ^ r := by exact_mod_cast loss
    _ ≤ (error * 2 ^ T) * 2 ^ r :=
      mul_le_mul_of_nonneg_right budget (by positivity)
    _ = error * 2 ^ (r + T) := by rw [pow_add]; ring

theorem sparseCondenser_output {u T k : Nat} :
    u * (condenserCoordinates k (sparsePowerBits u T) * sparseFieldBits u T) ≤
      (u + 1) * k + u * sparseFieldBits u T :=
  condenserCoordinates_output (sparsePowerBits_rate u T)

theorem sparseCondenser_loss {u T D k : Nat} {error : ℝ}
    (rate : 0 < u) (positive : 0 < T) (budget : (D * k : ℝ) ≤ error * 2 ^ T) :
    (((D - 1) * (2 ^ sparsePowerBits u T - 1) *
      condenserCoordinates k (sparsePowerBits u T) : Nat) : ℝ) /
        2 ^ sparseFieldBits u T ≤ error := by
  simpa only [sparsePowerBits_add] using
    condenserCoordinates_loss (T := T) (sparsePowerBits_pos rate positive) budget

end Algebraic.Cutwidth.Extractor.Internal
