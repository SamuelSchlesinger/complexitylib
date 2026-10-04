/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Asymptotics

/-!
# Asymptotics of the pairing and entropy inequality

A sublinear logarithmic rectangle threshold makes the designated-pair survival
fraction tend to one. The finite inequality therefore retains the full constant
`gateCoefficient`, rather than only a fixed weaker rational coefficient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry

open Filter

/-- Rounding a sublinear positive logarithmic threshold preserves sublinearity. -/
theorem clog_isLittleO {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) :
    (fun n => (Nat.clog 2 (K n) : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  filter_upwards [small.def (by positivity : 0 < δ / 2), positive,
    eventually_mul_logb_add_lt 0 1 (by positivity : 0 < δ / 2)] with n hs hp hc
  have log_nonneg : 0 ≤ Real.logb 2 (K n) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hp)
  have log_small : Real.logb 2 (K n) ≤ δ / 2 * n := by
    simpa only [Real.norm_of_nonneg log_nonneg, Real.norm_of_nonneg (Nat.cast_nonneg n)]
      using hs
  have ceil : (Nat.clog 2 (K n) : ℝ) < Real.logb 2 (K n) + 1 := by
    rw [← Real.natCeil_logb_natCast 2 (K n)]
    exact Nat.ceil_lt_add_one log_nonneg
  simp only [zero_mul, zero_add] at hc
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  linarith

/-- Eventually a sublinear nonnegative threshold leaves at least two sending coordinates. -/
theorem eventually_threshold_range {k : ℕ → ℕ}
    (small : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    ∀ᶠ n in atTop, k n + 3 ≤ n := by
  filter_upwards [small.def (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 6] with n hs hn
  have bound : (k n : ℝ) ≤ (1 / 2 : ℝ) * n := by
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using hs
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have : (k n : ℝ) + 3 ≤ n := by linarith
  exact_mod_cast this

/-- A sublinear receiving side preserves almost every designated pair. -/
theorem pairRetention_tendsto {k : ℕ → ℕ}
    (small : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    Tendsto (fun n => pairRetention n (k n)) atTop (nhds 1) := by
  have hk := small.tendsto_div_nhds_zero
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := ((hc.sub hk).sub h1).mul ((hc.sub hk).sub h2)
  have limit := h.div (hc.sub h1) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have same : (fun n : ℕ =>
      (1 - (k n : ℝ) / n - 1 / n) * (1 - (k n : ℝ) / n - 2 / n) / (1 - 1 / n))
      =ᶠ[atTop] (fun n => pairRetention n (k n)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    unfold pairRetention
    field_simp
  apply Tendsto.congr' same
  simpa only [sub_zero, one_mul, div_one, Pi.div_def] using limit

/-- The normalized finite lower bound tends to the full pairing/entropy coefficient. -/
theorem normalized_bound_tendsto {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) :
    Tendsto (fun n =>
      (1 + 2 * (Entropy.bitSaving * pairRetention n (Nat.clog 2 (K n))) -
        2 * (Entropy.bitSaving * pairRetention n (Nat.clog 2 (K n))) *
          ((Nat.clog 2 (K n) : ℝ) / n) -
        ((Nat.clog 2 (K n) : ℝ) / n + 2 / n) - Real.logb 2 (K n) / n) /
        (1 + Entropy.bitSaving * pairRetention n (Nat.clog 2 (K n))))
      atTop (nhds gateCoefficient) := by
  have hk := (clog_isLittleO small positive).tendsto_div_nhds_zero
  have ha := pairRetention_tendsto (clog_isLittleO small positive)
  have hd : Tendsto (fun n => Entropy.bitSaving * pairRetention n (Nat.clog 2 (K n)))
      atTop (nhds Entropy.bitSaving) := by
    simpa using tendsto_const_nhds.mul ha (a := Entropy.bitSaving)
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have hl := small.tendsto_div_nhds_zero
  have hc1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have numerator := (((hc1.add (hc2.mul hd)).sub
    ((hc2.mul hd).mul hk)).sub (hk.add h2)).sub hl
  have denominator := hc1.add hd
  simpa [gateCoefficient, Pi.div_def] using numerator.div denominator
    (by linarith [Entropy.bitSaving_pos] : 1 + Entropy.bitSaving ≠ 0)

/-- Absorb the finite geometric and logarithmic losses in arbitrary positive linear slack. -/
theorem eventually_lt_of_combined_bound {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : ℝ,
      (1 + Entropy.bitSaving * pairRetention n (Nat.clog 2 (K n))) * g ≥
        (1 + 2 * (Entropy.bitSaving * pairRetention n (Nat.clog 2 (K n)))) * n -
          2 * (Entropy.bitSaving * pairRetention n (Nat.clog 2 (K n))) *
            Nat.clog 2 (K n) - Nat.clog 2 (K n) - 2 - Real.logb 2 (K n) →
      (gateCoefficient - ε) * n < g := by
  have close := (normalized_bound_tendsto small positive).eventually_const_lt
    (by linarith : gateCoefficient - ε < gateCoefficient)
  filter_upwards [close, eventually_threshold_range (clog_isLittleO small positive)]
    with n hn hr g bound
  let k := Nat.clog 2 (K n)
  let d := Entropy.bitSaving * pairRetention n k
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by lia : 0 < n)
  have hd : 0 ≤ d := mul_nonneg Entropy.bitSaving_pos.le (pairRetention_nonneg (by lia))
  have hden : 0 < 1 + d := by linarith
  change gateCoefficient - ε <
    (1 + 2 * d - 2 * d * ((k : ℝ) / n) - ((k : ℝ) / n + 2 / n) -
      Real.logb 2 (K n) / n) / (1 + d) at hn
  have hn' := (lt_div_iff₀ hden).mp hn
  have multiply := mul_lt_mul_of_pos_right hn' hnR
  have identity :
      (1 + 2 * d - 2 * d * ((k : ℝ) / n) - ((k : ℝ) / n + 2 / n) -
        Real.logb 2 (K n) / n) * n =
      (1 + 2 * d) * n - 2 * d * k - k - 2 - Real.logb 2 (K n) := by
    field_simp
    ring
  rw [identity] at multiply
  change (1 + d) * g ≥ (1 + 2 * d) * n - 2 * d * k - k - 2 -
    Real.logb 2 (K n) at bound
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry
