/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Asymptotics

/-!
# Asymptotics of majority-fiber and entropy counting

The receiving threshold and every logarithmic loss are sublinear. Normalizing
the finite combined inequality therefore gives the exact majority-fiber gate
coefficient, with no additional assumptions on the circuit geometry.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Filter

/-- The normalized finite majority-fiber bound converges to its exact coefficient. -/
theorem normalized_bound_tendsto {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) :
    Tendsto (fun n =>
      ((1 - jointWeight * Joint.overlapPenalty) *
          (1 - (Nat.clog 2 (K n) : ℝ) / n - 1 / n) +
        Shared.receiverRetention n (Nat.clog 2 (K n)) * fiberWeight *
          (1 - (Nat.clog 2 (K n) : ℝ) / n - 1 / n -
            messageLoss * ((Nat.clog 2 (K n) : ℝ) / n + 1 / n)) +
        2 * Shared.receiverRetention n (Nat.clog 2 (K n)) * Shared.wideSaving *
          (1 - (Nat.clog 2 (K n) : ℝ) / n) -
        (1 + Shared.receiverRetention n (Nat.clog 2 (K n)) * fiberWeight) *
          (1 / n + Real.logb 2 (K n) / n)) /
        (1 + Shared.receiverRetention n (Nat.clog 2 (K n)) *
          (Shared.wideSaving + fiberWeight)))
      atTop (nhds gateCoefficient) := by
  have hk := (clog_isLittleO small positive).tendsto_div_nhds_zero
  have ha := Shared.receiverRetention_tendsto (clog_isLittleO small positive)
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hl := small.tendsto_div_nhds_zero
  have hc1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have hcb : Tendsto (fun _ : ℕ => 1 - jointWeight * Joint.overlapPenalty) atTop
      (nhds (1 - jointWeight * Joint.overlapPenalty)) := tendsto_const_nhds
  have hcf : Tendsto (fun _ : ℕ => fiberWeight) atTop (nhds fiberWeight) :=
    tendsto_const_nhds
  have hcm : Tendsto (fun _ : ℕ => messageLoss) atTop (nhds messageLoss) :=
    tendsto_const_nhds
  have hcw : Tendsto (fun _ : ℕ => Shared.wideSaving) atTop
      (nhds Shared.wideSaving) := tendsto_const_nhds
  have numerator := (((hcb.mul ((hc1.sub hk).sub h1)).add
    ((ha.mul hcf).mul (((hc1.sub hk).sub h1).sub (hcm.mul (hk.add h1))))).add
    (((hc2.mul ha).mul hcw).mul (hc1.sub hk))).sub
    ((hc1.add (ha.mul hcf)).mul (h1.add hl))
  have denominator := hc1.add (ha.mul (hcw.add hcf))
  have nonzero : 1 + 1 * (Shared.wideSaving + fiberWeight) ≠ 0 := by
    have := scalarDenominator_pos
    unfold scalarDenominator at this
    linarith
  have limit := numerator.div denominator nonzero
  have coefficient :
      (1 - jointWeight * Joint.overlapPenalty + fiberWeight + 2 * Shared.wideSaving) /
        (1 + (Shared.wideSaving + fiberWeight)) = gateCoefficient := by
    rw [jointWeight_mul_overlapPenalty]
    unfold gateCoefficient scalarNumerator scalarDenominator
    congr 1 <;> ring
  simpa only [Pi.div_def, sub_zero, mul_zero, add_zero, one_mul, mul_one,
    coefficient] using limit

/-- Every finite threshold loss is absorbed by an arbitrary positive linear slack. -/
theorem eventually_lt_of_combined_bound {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : ℝ,
      (1 + Shared.receiverRetention n (Nat.clog 2 (K n)) *
          (Shared.wideSaving + fiberWeight)) * g ≥
        (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - Nat.clog 2 (K n) - 1) +
          Shared.receiverRetention n (Nat.clog 2 (K n)) * fiberWeight *
            ((n : ℝ) - Nat.clog 2 (K n) - 1 - messageLoss * (Nat.clog 2 (K n) + 1)) +
          2 * Shared.receiverRetention n (Nat.clog 2 (K n)) * Shared.wideSaving *
            ((n : ℝ) - Nat.clog 2 (K n)) -
          (1 + Shared.receiverRetention n (Nat.clog 2 (K n)) * fiberWeight) *
            (1 + Real.logb 2 (K n)) →
      (gateCoefficient - ε) * n < g := by
  have close := (normalized_bound_tendsto small positive).eventually_const_lt
    (by linarith : gateCoefficient - ε < gateCoefficient)
  filter_upwards [close, Shared.eventually_threshold_range (clog_isLittleO small positive)]
    with n hn hr g bound
  let k := Nat.clog 2 (K n)
  let a := Shared.receiverRetention n k
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by lia : 0 < n)
  have ha : 0 ≤ a := Shared.receiverRetention_nonneg hr
  have hden : 0 < 1 + a * (Shared.wideSaving + fiberWeight) := by
    have := mul_nonneg ha (add_nonneg Shared.wideSaving_pos.le fiberWeight_pos.le)
    linarith
  change gateCoefficient - ε <
    ((1 - jointWeight * Joint.overlapPenalty) * (1 - (k : ℝ) / n - 1 / n) +
      a * fiberWeight * (1 - (k : ℝ) / n - 1 / n - messageLoss * ((k : ℝ) / n + 1 / n)) +
      2 * a * Shared.wideSaving * (1 - (k : ℝ) / n) -
      (1 + a * fiberWeight) * (1 / n + Real.logb 2 (K n) / n)) /
        (1 + a * (Shared.wideSaving + fiberWeight)) at hn
  have multiply := mul_lt_mul_of_pos_right ((lt_div_iff₀ hden).mp hn) hnR
  have identity :
      ((1 - jointWeight * Joint.overlapPenalty) * (1 - (k : ℝ) / n - 1 / n) +
        a * fiberWeight *
          (1 - (k : ℝ) / n - 1 / n - messageLoss * ((k : ℝ) / n + 1 / n)) +
        2 * a * Shared.wideSaving * (1 - (k : ℝ) / n) -
        (1 + a * fiberWeight) * (1 / n + Real.logb 2 (K n) / n)) * n =
      (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
        a * fiberWeight * ((n : ℝ) - k - 1 - messageLoss * (k + 1)) +
        2 * a * Shared.wideSaving * ((n : ℝ) - k) -
        (1 + a * fiberWeight) * (1 + Real.logb 2 (K n)) := by
    field_simp
  rw [identity] at multiply
  change (1 + a * (Shared.wideSaving + fiberWeight)) * g ≥
    (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
      a * fiberWeight * ((n : ℝ) - k - 1 - messageLoss * (k + 1)) +
      2 * a * Shared.wideSaving * ((n : ℝ) - k) -
      (1 + a * fiberWeight) * (1 + Real.logb 2 (K n)) at bound
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
