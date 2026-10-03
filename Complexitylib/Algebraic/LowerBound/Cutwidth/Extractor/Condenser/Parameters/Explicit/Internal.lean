/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse
import Mathlib.Tactic.Positivity

/-!
# Finite bounds for the explicit sparse parameter choice

Ceiling division covers the source bits; rounding to a power of three costs
at most another factor of three. The logarithmic slack then pays for the
extension-degree and entropy factors in the normalized degree-loss bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem explicitCondenserBudget_pos (n k e : Nat) : 0 < explicitCondenserBudget n k e :=
  Nat.succ_pos _

theorem explicitCondenserFieldBits_pos (n k e u : Nat) :
    0 < sparseFieldBits u (explicitCondenserBudget n k e) := by
  unfold sparseFieldBits
  positivity

theorem explicitCondenserPowerBits_pos (n k e : Nat) {u : Nat} (rate : 0 < u) :
    0 < sparsePowerBits u (explicitCondenserBudget n k e) :=
  sparsePowerBits_pos rate (explicitCondenserBudget_pos n k e)

theorem explicitCondenserExtensionExponent_pos (n k e u : Nat) :
    0 < explicitCondenserExtensionExponent n k e u :=
  Nat.clog_pos (by decide) ((by decide : 1 < 3).trans_le (le_max_left _ _))

theorem explicitCondenser_degree_lower (n k e u : Nat) :
    3 ≤ explicitCondenserExtensionDegree n k e u :=
  (le_max_left _ _).trans (Nat.le_pow_clog (by decide : 1 < 3) _)

theorem explicitCondenser_source_capacity (n k e u : Nat) :
    n ≤ sparseFieldBits u (explicitCondenserBudget n k e) *
      explicitCondenserExtensionDegree n k e u := by
  have cover := condenserCoordinates_capacity (k := n) (explicitCondenserFieldBits_pos n k e u)
  have rounded := Nat.le_pow_clog (by decide : 1 < 3)
    (max 3 (condenserCoordinates n (sparseFieldBits u (explicitCondenserBudget n k e))))
  exact cover.trans (Nat.mul_le_mul_left _ ((le_max_right _ _).trans rounded))

theorem explicitCondenser_degree_le (n k e u : Nat) :
    explicitCondenserExtensionDegree n k e u ≤ 9 * (n + 1) := by
  let target := max 3 (condenserCoordinates n (sparseFieldBits u (explicitCondenserBudget n k e)))
  have bigger : 1 < target := (by decide : 1 < 3).trans_le (le_max_left _ _)
  have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 3) bigger
  have exponent : (Nat.clog 3 target).pred + 1 = Nat.clog 3 target :=
    Nat.succ_pred_eq_of_pos (Nat.clog_pos (by decide) bigger)
  have rounded : 3 ^ Nat.clog 3 target ≤ 3 * target := by
    calc
      _ = 3 ^ (Nat.clog 3 target).pred * 3 := by rw [← pow_succ, exponent]
      _ ≤ target * 3 := Nat.mul_le_mul_right 3 previous.le
      _ = _ := Nat.mul_comm _ _
  have ceiling := condenserCoordinates_le (k := n) (explicitCondenserFieldBits_pos n k e u)
  have bound : target ≤ 3 * (n + 1) := max_le (by lia) (by lia)
  exact rounded.trans (by lia)

theorem explicitCondenser_entropy_capacity (n k e : Nat) {u : Nat} (rate : 0 < u) :
    k ≤ sparsePowerBits u (explicitCondenserBudget n k e) *
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) :=
  condenserCoordinates_capacity (explicitCondenserPowerBits_pos n k e rate)

theorem explicitCondenser_fieldBits_le (n k e u : Nat) :
    sparseFieldBits u (explicitCondenserBudget n k e) ≤
      6 * (u + 1) * explicitCondenserBudget n k e := by
  simpa only [Nat.mul_assoc] using
    sparseFieldBits_upper (u := u) (explicitCondenserBudget_pos n k e)

theorem explicitCondenser_output_rate (n k e u : Nat) :
    u * (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
      sparseFieldBits u (explicitCondenserBudget n k e)) ≤
        (u + 1) * k + u * sparseFieldBits u (explicitCondenserBudget n k e) :=
  sparseCondenser_output

theorem explicitCondenser_error_budget (n k e u : Nat) :
    explicitCondenserExtensionDegree n k e u * k * 2 ^ e ≤
      2 ^ explicitCondenserBudget n k e := by
  have degree := explicitCondenser_degree_le n k e u
  have entropy : explicitCondenserExtensionDegree n k e u * k ≤ 9 * (n + 1) * (k + 1) :=
    (Nat.mul_le_mul_right k degree).trans (Nat.mul_le_mul_left _ (Nat.le_succ k))
  have budget := entropy.trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  calc
    _ ≤ 2 ^ Nat.clog 2 (9 * (n + 1) * (k + 1)) * 2 ^ e :=
      Nat.mul_le_mul_right _ budget
    _ = 2 ^ (e + Nat.clog 2 (9 * (n + 1) * (k + 1))) := by
      rw [pow_add, Nat.mul_comm]
    _ ≤ 2 ^ explicitCondenserBudget n k e :=
      Nat.pow_le_pow_right (by decide) (Nat.le_succ _)

end Algebraic.Cutwidth.Extractor.Internal
