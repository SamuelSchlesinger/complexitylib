/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.OneWay

/-!
# Constants for the Gold-map gate bound

With `c = 1 - H₂(1/4)`, the restriction–rank and entropy inequalities give the
leading coefficient `(7 + 4c)/(4 + 2c)`, approximately `1.771556`, and the additive
penalty `(3 + 4c)/(4 + 2c)`, approximately `0.857781`. The coefficient lies strictly
between `7/4` and `2`.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Gold

open Cutwidth.Aggregate.Geometry

/-- Leading gate coefficient for the Gold map in odd dimension. -/
noncomputable def gateCoefficient : ℝ :=
  (7 + 4 * Entropy.bitSaving) / (4 + 2 * Entropy.bitSaving)

/-- The finite additive loss in the Gold-map gate bound. -/
noncomputable def constantPenalty : ℝ :=
  (3 + 4 * Entropy.bitSaving) / (4 + 2 * Entropy.bitSaving)

/-- The Gold coefficient exceeds seven quarters. -/
theorem seven_quarters_lt_gateCoefficient : (7 / 4 : ℝ) < gateCoefficient := by
  unfold gateCoefficient
  apply (lt_div_iff₀ (by linarith [Entropy.bitSaving_pos])).mpr
  linarith [Entropy.bitSaving_pos]

/-- The Gold coefficient is below two. -/
theorem gateCoefficient_lt_two : gateCoefficient < 2 := by
  unfold gateCoefficient
  apply (div_lt_iff₀ (by linarith [Entropy.bitSaving_pos])).mpr
  linarith

/-- The finite penalty is positive. -/
theorem constantPenalty_pos : 0 < constantPenalty :=
  div_pos (by linarith [Entropy.bitSaving_pos]) (by linarith [Entropy.bitSaving_pos])

end Algebraic.Aggregate.Geometry.Gold
