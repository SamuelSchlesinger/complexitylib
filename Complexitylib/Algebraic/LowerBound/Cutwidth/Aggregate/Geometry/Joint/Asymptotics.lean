/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Asymptotics

/-!
# Asymptotics of joint conjunction-message counting

The receiver keeps a sublinear number of inputs. Pair retention tends to one,
and the finite variable charge retains the full joint-entropy coefficient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Filter

/-- The normalized joint-message inequality tends to its exact coefficient. -/
theorem normalized_bound_tendsto {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) :
    Tendsto (fun n =>
      (1 - overlapPenalty + 2 * (gateSaving * pairRetention n (Nat.clog 2 (K n))) -
        2 * (gateSaving * pairRetention n (Nat.clog 2 (K n))) *
          ((Nat.clog 2 (K n) : ℝ) / n) -
        (1 - overlapPenalty) * ((Nat.clog 2 (K n) : ℝ) / n + 1 / n) -
        1 / n - Real.logb 2 (K n) / n) /
        (1 + gateSaving * pairRetention n (Nat.clog 2 (K n))))
      atTop (nhds gateCoefficient) := by
  have hk := (clog_isLittleO small positive).tendsto_div_nhds_zero
  have ha := pairRetention_tendsto (clog_isLittleO small positive)
  have hd : Tendsto (fun n => gateSaving * pairRetention n (Nat.clog 2 (K n)))
      atTop (nhds gateSaving) := by
    simpa using tendsto_const_nhds.mul ha (a := gateSaving)
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hl := small.tendsto_div_nhds_zero
  have hc1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have hcb : Tendsto (fun _ : ℕ => 1 - overlapPenalty) atTop
      (nhds (1 - overlapPenalty)) := tendsto_const_nhds
  have numerator := ((((hcb.add (hc2.mul hd)).sub ((hc2.mul hd).mul hk)).sub
    (hcb.mul (hk.add h1))).sub h1).sub hl
  have denominator := hc1.add hd
  rw [gateCoefficient_eq]
  simpa [Pi.div_def] using numerator.div denominator
    (by linarith [gateSaving_pos] : 1 + gateSaving ≠ 0)

/-- Finite losses vanish for every sublinear logarithmic sumset threshold. -/
theorem eventually_lt_of_combined_bound {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : ℝ,
      (1 + gateSaving * pairRetention n (Nat.clog 2 (K n))) * g ≥
        (1 - overlapPenalty + 2 * (gateSaving * pairRetention n (Nat.clog 2 (K n)))) * n -
          2 * (gateSaving * pairRetention n (Nat.clog 2 (K n))) * Nat.clog 2 (K n) -
          (1 - overlapPenalty) * (Nat.clog 2 (K n) + 1) - 1 - Real.logb 2 (K n) →
      (gateCoefficient - ε) * n < g := by
  have close := (normalized_bound_tendsto small positive).eventually_const_lt
    (by linarith : gateCoefficient - ε < gateCoefficient)
  filter_upwards [close, eventually_threshold_range (clog_isLittleO small positive)]
    with n hn hr g bound
  let k := Nat.clog 2 (K n)
  let d := gateSaving * pairRetention n k
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by lia : 0 < n)
  have hd : 0 ≤ d := mul_nonneg gateSaving_pos.le (pairRetention_nonneg (by lia))
  have hden : 0 < 1 + d := by linarith
  change gateCoefficient - ε <
    (1 - overlapPenalty + 2 * d - 2 * d * ((k : ℝ) / n) -
      (1 - overlapPenalty) * ((k : ℝ) / n + 1 / n) -
      1 / n - Real.logb 2 (K n) / n) / (1 + d) at hn
  have hn' := (lt_div_iff₀ hden).mp hn
  have multiply := mul_lt_mul_of_pos_right hn' hnR
  have identity :
      (1 - overlapPenalty + 2 * d - 2 * d * ((k : ℝ) / n) -
        (1 - overlapPenalty) * ((k : ℝ) / n + 1 / n) -
        1 / n - Real.logb 2 (K n) / n) * n =
      (1 - overlapPenalty + 2 * d) * n - 2 * d * k -
        (1 - overlapPenalty) * (k + 1) - 1 - Real.logb 2 (K n) := by
    field_simp
  rw [identity] at multiply
  change (1 + d) * g ≥ (1 - overlapPenalty + 2 * d) * n - 2 * d * k -
    (1 - overlapPenalty) * (k + 1) - 1 - Real.logb 2 (K n) at bound
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
