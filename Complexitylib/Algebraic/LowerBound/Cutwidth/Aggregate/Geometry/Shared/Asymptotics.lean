/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Asymptotics

/-!
# Asymptotics of shared-control and refined message counting

A sublinear receiving side retains almost every designated triple. All finite
threshold losses vanish after normalization, leaving the stronger full coefficient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Shared

open Filter

/-- A sublinear receiving threshold eventually leaves at least three sending coordinates. -/
theorem eventually_threshold_range {k : ℕ → ℕ}
    (small : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    ∀ᶠ n in atTop, k n + 4 ≤ n := by
  filter_upwards [small.def (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 8] with n hs hn
  have bound : (k n : ℝ) ≤ (1 / 2 : ℝ) * n := by
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using hs
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have : (k n : ℝ) + 4 ≤ n := by linarith
  exact_mod_cast this

/-- A sublinear receiving side preserves asymptotically every selected primary triple. -/
theorem receiverRetention_tendsto {k : ℕ → ℕ}
    (small : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    Tendsto (fun n => receiverRetention n (k n)) atTop (nhds 1) := by
  have hk := small.tendsto_div_nhds_zero
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have h3 := tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have numerator := (((hc.sub hk).sub h1).mul ((hc.sub hk).sub h2)).mul
    ((hc.sub hk).sub h3)
  have denominator := (hc.sub h1).mul (hc.sub h2)
  have limit := numerator.div denominator (by norm_num : ((1 : ℝ) - 0) * (1 - 0) ≠ 0)
  have same : (fun n : ℕ =>
      (1 - (k n : ℝ) / n - 1 / n) * (1 - (k n : ℝ) / n - 2 / n) *
        (1 - (k n : ℝ) / n - 3 / n) / ((1 - 1 / n) * (1 - 2 / n)))
      =ᶠ[atTop] (fun n => receiverRetention n (k n)) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
    unfold receiverRetention
    field_simp
  apply Tendsto.congr' same
  simpa only [sub_zero, one_mul, div_one, Pi.div_def] using limit

/-- The normalized finite shared-control bound converges to its exact gate coefficient. -/
theorem normalized_bound_tendsto {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) :
    Tendsto (fun n =>
      ((1 - Joint.overlapPenalty) *
          (1 - (Nat.clog 2 (K n) : ℝ) / n - 1 / n) +
        receiverRetention n (Nat.clog 2 (K n)) *
          (Joint.gateSaving / 2 + 3 * wideSaving / 2) -
        2 * receiverRetention n (Nat.clog 2 (K n)) * wideSaving *
          ((Nat.clog 2 (K n) : ℝ) / n) - 1 / n - Real.logb 2 (K n) / n) /
        (1 + receiverRetention n (Nat.clog 2 (K n)) * wideSaving))
      atTop (nhds gateCoefficient) := by
  have hk := (clog_isLittleO small positive).tendsto_div_nhds_zero
  have ha := receiverRetention_tendsto (clog_isLittleO small positive)
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hl := small.tendsto_div_nhds_zero
  have hc1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have hcb : Tendsto (fun _ : ℕ => 1 - Joint.overlapPenalty) atTop
      (nhds (1 - Joint.overlapPenalty)) := tendsto_const_nhds
  have hcr : Tendsto (fun _ : ℕ => wideSaving) atTop (nhds wideSaving) := tendsto_const_nhds
  have hcd : Tendsto (fun _ : ℕ => Joint.gateSaving / 2 + 3 * wideSaving / 2) atTop
      (nhds (Joint.gateSaving / 2 + 3 * wideSaving / 2)) := tendsto_const_nhds
  have numerator := ((((hcb.mul ((hc1.sub hk).sub h1)).add (ha.mul hcd)).sub
    (((hc2.mul ha).mul hcr).mul hk)).sub h1).sub hl
  have denominator := hc1.add (ha.mul hcr)
  simpa [gateCoefficient, Pi.div_def, add_assoc] using numerator.div denominator
    (by linarith [wideSaving_pos] : 1 + 1 * wideSaving ≠ 0)

/-- Absorb every finite logarithmic loss into an arbitrary positive linear slack. -/
theorem eventually_lt_of_combined_bound {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : ℝ,
      (1 + receiverRetention n (Nat.clog 2 (K n)) * wideSaving) * g ≥
        (1 - Joint.overlapPenalty) * ((n : ℝ) - Nat.clog 2 (K n) - 1) +
          receiverRetention n (Nat.clog 2 (K n)) *
            (Joint.gateSaving / 2 + 3 * wideSaving / 2) * n -
          2 * receiverRetention n (Nat.clog 2 (K n)) * wideSaving * Nat.clog 2 (K n) -
          1 - Real.logb 2 (K n) →
      (gateCoefficient - ε) * n < g := by
  have close := (normalized_bound_tendsto small positive).eventually_const_lt
    (by linarith : gateCoefficient - ε < gateCoefficient)
  filter_upwards [close, eventually_threshold_range (clog_isLittleO small positive)]
    with n hn hr g bound
  let k := Nat.clog 2 (K n)
  let a := receiverRetention n k
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by lia : 0 < n)
  have ha : 0 ≤ a := receiverRetention_nonneg hr
  have hden : 0 < 1 + a * wideSaving := by
    have := mul_nonneg ha wideSaving_pos.le
    linarith
  change gateCoefficient - ε <
    ((1 - Joint.overlapPenalty) * (1 - (k : ℝ) / n - 1 / n) +
      a * (Joint.gateSaving / 2 + 3 * wideSaving / 2) -
      2 * a * wideSaving * ((k : ℝ) / n) - 1 / n - Real.logb 2 (K n) / n) /
      (1 + a * wideSaving) at hn
  have hn' := (lt_div_iff₀ hden).mp hn
  have multiply := mul_lt_mul_of_pos_right hn' hnR
  have identity :
      ((1 - Joint.overlapPenalty) * (1 - (k : ℝ) / n - 1 / n) +
        a * (Joint.gateSaving / 2 + 3 * wideSaving / 2) -
        2 * a * wideSaving * ((k : ℝ) / n) - 1 / n - Real.logb 2 (K n) / n) * n =
      (1 - Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
        a * (Joint.gateSaving / 2 + 3 * wideSaving / 2) * n -
        2 * a * wideSaving * k - 1 - Real.logb 2 (K n) := by
    field_simp
  rw [identity] at multiply
  change (1 + a * wideSaving) * g ≥
    (1 - Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
      a * (Joint.gateSaving / 2 + 3 * wideSaving / 2) * n -
      2 * a * wideSaving * k - 1 - Real.logb 2 (K n) at bound
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Shared
