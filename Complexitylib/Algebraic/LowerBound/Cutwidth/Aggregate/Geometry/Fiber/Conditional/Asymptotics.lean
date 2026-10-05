/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Asymptotics

/-!
# Asymptotics of conditional-majority information bounds

The receiver threshold and logarithmic message-fiber losses are sublinear.
Normalizing the finite combined inequality gives the exact conditional-majority
coefficient, retaining all conditional pair and triple savings.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Filter

/-- The normalized finite conditional-majority inequality converges to its coefficient. -/
theorem normalized_bound_tendsto {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) :
    Tendsto (fun n =>
      ((1 - jointWeight * Joint.overlapPenalty) *
          (1 - (Nat.clog 2 (K n) : ℝ) / n - 1 / n) +
        fiberWeight *
          (1 - (1 + messageLoss - pairSaving) * ((Nat.clog 2 (K n) : ℝ) / n + 1 / n)) +
        2 * Shared.receiverRetention n (Nat.clog 2 (K n)) * wideWeight *
          (1 - (Nat.clog 2 (K n) : ℝ) / n) -
        (1 + fiberWeight) * (1 / n + Real.logb 2 (K n) / n)) /
        (1 + fiberWeight + Shared.receiverRetention n (Nat.clog 2 (K n)) * wideWeight))
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
  have hcm : Tendsto (fun _ : ℕ => 1 + messageLoss - pairSaving) atTop
      (nhds (1 + messageLoss - pairSaving)) := tendsto_const_nhds
  have hcw : Tendsto (fun _ : ℕ => wideWeight) atTop (nhds wideWeight) :=
    tendsto_const_nhds
  have numerator := (((hcb.mul ((hc1.sub hk).sub h1)).add
    (hcf.mul (hc1.sub (hcm.mul (hk.add h1))))).add
    (((hc2.mul ha).mul hcw).mul (hc1.sub hk))).sub
    ((hc1.add hcf).mul (h1.add hl))
  have denominator := (hc1.add hcf).add (ha.mul hcw)
  have nonzero : 1 + fiberWeight + 1 * wideWeight ≠ 0 := by
    have := scalarDenominator_pos
    rw [scalarDenominator_eq] at this
    simpa only [one_mul] using this.ne'
  have limit := numerator.div denominator nonzero
  have coefficient :
      (1 - jointWeight * Joint.overlapPenalty + fiberWeight + 2 * wideWeight) /
        (1 + fiberWeight + wideWeight) = gateCoefficient := by
    rw [← scalarNumerator_eq, ← scalarDenominator_eq]
    rfl
  simpa only [Pi.div_def, sub_zero, mul_zero, add_zero, one_mul, mul_one,
    coefficient] using limit

/-- Every finite receiver loss is absorbed by arbitrary positive linear slack. -/
theorem eventually_lt_of_combined_bound {K : ℕ → ℕ}
    (small : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (positive : ∀ᶠ n in atTop, 1 ≤ K n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : ℝ,
      (1 + fiberWeight + Shared.receiverRetention n (Nat.clog 2 (K n)) * wideWeight) * g ≥
        (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - Nat.clog 2 (K n) - 1) +
          fiberWeight *
            ((n : ℝ) - (1 + messageLoss - pairSaving) * (Nat.clog 2 (K n) + 1)) +
          2 * Shared.receiverRetention n (Nat.clog 2 (K n)) * wideWeight *
            ((n : ℝ) - Nat.clog 2 (K n)) -
          (1 + fiberWeight) * (1 + Real.logb 2 (K n)) →
      (gateCoefficient - ε) * n < g := by
  have close := (normalized_bound_tendsto small positive).eventually_const_lt
    (by linarith : gateCoefficient - ε < gateCoefficient)
  filter_upwards [close, Shared.eventually_threshold_range (clog_isLittleO small positive)]
    with n hn hr g bound
  let k := Nat.clog 2 (K n)
  let a := Shared.receiverRetention n k
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by lia : 0 < n)
  have ha : 0 ≤ a := Shared.receiverRetention_nonneg hr
  have hden : 0 < 1 + fiberWeight + a * wideWeight := by
    have := mul_nonneg ha wideWeight_pos.le
    linarith [fiberWeight_pos]
  change gateCoefficient - ε <
    ((1 - jointWeight * Joint.overlapPenalty) * (1 - (k : ℝ) / n - 1 / n) +
      fiberWeight * (1 - (1 + messageLoss - pairSaving) * ((k : ℝ) / n + 1 / n)) +
      2 * a * wideWeight * (1 - (k : ℝ) / n) -
      (1 + fiberWeight) * (1 / n + Real.logb 2 (K n) / n)) /
        (1 + fiberWeight + a * wideWeight) at hn
  have multiply := mul_lt_mul_of_pos_right ((lt_div_iff₀ hden).mp hn) hnR
  have identity :
      ((1 - jointWeight * Joint.overlapPenalty) * (1 - (k : ℝ) / n - 1 / n) +
        fiberWeight * (1 - (1 + messageLoss - pairSaving) * ((k : ℝ) / n + 1 / n)) +
        2 * a * wideWeight * (1 - (k : ℝ) / n) -
        (1 + fiberWeight) * (1 / n + Real.logb 2 (K n) / n)) * n =
      (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
        fiberWeight * ((n : ℝ) - (1 + messageLoss - pairSaving) * (k + 1)) +
        2 * a * wideWeight * ((n : ℝ) - k) -
        (1 + fiberWeight) * (1 + Real.logb 2 (K n)) := by
    field_simp
  rw [identity] at multiply
  change (1 + fiberWeight + a * wideWeight) * g ≥
    (1 - jointWeight * Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
      fiberWeight * ((n : ℝ) - (1 + messageLoss - pairSaving) * (k + 1)) +
      2 * a * wideWeight * ((n : ℝ) - k) -
      (1 + fiberWeight) * (1 + Real.logb 2 (K n)) at bound
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional
