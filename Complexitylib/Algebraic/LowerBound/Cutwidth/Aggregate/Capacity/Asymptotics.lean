/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics

/-!
# Absorbing the one-way capacity remainder

A capacity bound with twice the logarithmic rectangle threshold and a constant
remainder gives a leading coefficient of one when the threshold has sublinear logarithm.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open Filter

/-- A sublinear rectangle threshold absorbs the finite one-way counting remainder. -/
theorem eventually_lt_of_real_oneWayBound (K : Nat → Nat)
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) (C : Nat) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ B : ℝ,
      (n : ℝ) ≤ B + 2 * (Nat.clog 2 (K n) : ℝ) + C → (1 - ε) * n < B := by
  filter_upwards [small.def (by positivity : 0 < ε / 4), positive,
    eventually_mul_logb_add_lt 0 ((C : ℝ) + 2) (by positivity : 0 < ε / 2)]
    with n hsmall hpositive hconstant B hB
  have hlog : 0 ≤ Real.logb 2 (K n) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hpositive)
  have hsmall' : Real.logb 2 (K n) ≤ ε / 4 * n := by
    simpa only [Real.norm_of_nonneg hlog,
      Real.norm_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hsmall
  have hclog : (Nat.clog 2 (K n) : ℝ) < Real.logb 2 (K n) + 1 := by
    rw [← Real.natCeil_logb_natCast 2 (K n)]
    exact Nat.ceil_lt_add_one hlog
  simp only [zero_mul, zero_add] at hconstant
  linarith

/-- The integer-capacity specialization of the one-way remainder estimate. -/
theorem eventually_lt_of_oneWayBound (K : Nat → Nat)
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) (C : Nat) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ B : Nat,
      n ≤ B + 2 * Nat.clog 2 (K n) + C → (1 - ε) * n < B := by
  filter_upwards [eventually_lt_of_real_oneWayBound K small positive C hε] with n bound B hB
  exact bound B (by exact_mod_cast hB)

end Algebraic.Cutwidth.Aggregate
