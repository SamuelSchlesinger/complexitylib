/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Foundations.Data.Nat.Asymptotics
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exponentials of iterated-logarithmic budgets

A fixed polynomial in the ceiling logarithm is eventually smaller than its
input, by Cslib's natural exponential-versus-polynomial theorem. Applying
this at the input's ceiling logarithm shows that exponentiating any fixed
iterated-logarithmic polynomial still gives a sublinear function. This keeps
the unbounded Gamma candidate count, rather than replacing it by a fixed
power of the original logarithm.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter

theorem sourceReduction_tendsto_clog :
    Tendsto (fun n : Nat => Nat.clog 2 (n + 1)) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n large
  exact (Nat.le_log_of_pow_le (by decide) large).trans
    ((Nat.log_le_clog 2 n).trans (Nat.clog_mono_right 2 (Nat.le_succ n)))

theorem sourceReduction_eventually_clog_pow_le (c d : Nat) :
    ∀ᶠ n : Nat in atTop, c * (Nat.clog 2 (n + 1) + 1) ^ d ≤ n := by
  have logGrowth : Tendsto (Nat.log 2) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop (2 ^ N)] with n large
    exact Nat.le_log_of_pow_le (by decide) large
  filter_upwards [logGrowth.eventually (Nat.eventually_mul_pow_le_pow
    (c * 3 ^ d) d (by decide : 1 < 2)),
    logGrowth.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
      with n power logpos positive
  have ceiling : Nat.clog 2 (n + 1) ≤ Nat.log 2 n + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide) n)
  have compare : Nat.clog 2 (n + 1) + 1 ≤ 3 * Nat.log 2 n := by lia
  calc
    c * (Nat.clog 2 (n + 1) + 1) ^ d ≤ c * (3 * Nat.log 2 n) ^ d :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left compare d)
    _ = (c * 3 ^ d) * Nat.log 2 n ^ d := by rw [mul_pow]; ring
    _ ≤ 2 ^ Nat.log 2 n := power
    _ ≤ n := Nat.pow_log_le_self 2 (by lia)

theorem sourceReduction_iterated_exp_isLittleO (c d : Nat) :
    (fun n : Nat => ((2 ^
      (c * (Nat.clog 2 (Nat.clog 2 (n + 1) + 1) + 1) ^ d) : Nat) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) := by
  apply Asymptotics.isLittleO_iff_nat_mul_le.mpr
  intro k
  filter_upwards [sourceReduction_tendsto_clog.eventually
    (sourceReduction_eventually_clog_pow_le (c + Nat.clog 2 k + 1) d),
    eventually_ge_atTop 1] with n bound positive
  let L := Nat.clog 2 (n + 1)
  let r := Nat.clog 2 (L + 1) + 1
  change (c + Nat.clog 2 k + 1) * r ^ d ≤ L at bound
  have unit : 1 ≤ r ^ d := Nat.one_le_pow _ _ (by dsimp only [r]; lia)
  have reserved : Nat.clog 2 k + c * r ^ d + 1 ≤ L := by nlinarith
  have exponent : Nat.clog 2 k + c * r ^ d ≤ L - 1 := by lia
  have natural : k * 2 ^ (c * r ^ d) ≤ n := by
    calc
      _ ≤ 2 ^ Nat.clog 2 k * 2 ^ (c * r ^ d) :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) k)
      _ = 2 ^ (Nat.clog 2 k + c * r ^ d) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) exponent
      _ ≤ n := by
        have lower := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
          (show 1 < n + 1 by lia)
        change 2 ^ (L - 1) < n + 1 at lower
        lia
  have cast : (k : ℝ) * ((2 ^ (c * r ^ d) : Nat) : ℝ) ≤ n := by
    exact_mod_cast natural
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using cast

end Algebraic.Cutwidth.Extractor.Internal
