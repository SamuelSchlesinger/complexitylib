/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Fibres
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# One-way bounds from joint message weights

Any normalized joint weight certificate can replace the separate-coordinate
product distribution in the rectangle-free message bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open scoped Classical

/-- A joint message cost bounds the number of sending-side input bits. -/
theorem sender_card_le_of_weight_oneWay {n K : ℕ} {f : Cslib.BooleanFunction n}
    (hK : 0 < K) (free : RectangleFree f K)
    (freeNot : RectangleFree (fun x => !(f x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card)
    {Y : Type*} [Fintype Y] (summary : OneWaySummary f U Y) {cost : ℝ}
    (certificate : Entropy.WeightBound summary.key cost) :
    (U.card : ℝ) ≤ Real.logb 2 K + cost / Real.log 2 := by
  have bound := certificate.log_card_le hK (fun message =>
    (Entropy.card_fibre_lt_of_rectangleFree_both hK free freeNot U large
      summary message).le)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at bound
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, ← add_div]
  exact (le_div_iff₀ logpos).mpr bound

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
