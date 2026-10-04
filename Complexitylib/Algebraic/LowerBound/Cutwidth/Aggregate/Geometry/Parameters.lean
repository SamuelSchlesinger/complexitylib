/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.OneWay

/-!
# Constants in the pairing and entropy bound

The gate coefficient is `(1+2c)/(1+c)`, where `c` is the saving in bits from a
quarter-biased Boolean message. The survival probability accounts for giving
`k+1` of the `n` primary inputs to the receiving party.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry

/-- Exact survival fraction for two designated primary variables. -/
noncomputable def pairRetention (n k : ℕ) : ℝ :=
  ((n : ℝ) - k - 1) * ((n : ℝ) - k - 2) / ((n : ℝ) * (n - 1))

/-- The asymptotic gate coefficient from affine pairing and biased messages. -/
noncomputable def gateCoefficient : ℝ :=
  (1 + 2 * Entropy.bitSaving) / (1 + Entropy.bitSaving)

/-- Pairing and entropy yield a coefficient strictly above one. -/
theorem one_lt_gateCoefficient : 1 < gateCoefficient := by
  rw [gateCoefficient]
  apply (lt_div_iff₀ (by linarith [Entropy.bitSaving_pos])).mpr
  linarith [Entropy.bitSaving_pos]

/-- The present combination has coefficient strictly below two. -/
theorem gateCoefficient_lt_two : gateCoefficient < 2 := by
  rw [gateCoefficient]
  apply (div_lt_iff₀ (by linarith [Entropy.bitSaving_pos])).mpr
  linarith

/-- In the valid finite range the pair survival factor is nonnegative. -/
theorem pairRetention_nonneg {n k : ℕ} (range : k + 2 ≤ n) : 0 ≤ pairRetention n k := by
  have hr : (k : ℝ) + 2 ≤ n := by exact_mod_cast range
  unfold pairRetention
  exact div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) k]))

end Algebraic.Cutwidth.Aggregate.Geometry
