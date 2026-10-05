/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Hardness

/-!
# The explicit family and the majority-fiber coefficient

The existing balanced Chattopadhyay--Liao family requires more than `(C-ε)n`
signed unbounded AND/OR/XOR gates eventually, with `C` approximately `1.236484988`.
The signature permits arbitrary fan-in, fanout, depth, and repeated signed literals.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Filter Algebraic.Aggregate.Geometry

/-- The fixed explicit balanced family attains the majority-fiber coefficient
without depth, fanout, fan-in, or placement restrictions. -/
theorem sourceReductionHardFamily_eventually_lt_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ c : Circuit signature n 1,
      c.Computes interpretation (fun x _ => Extractor.sourceReductionHardFamily n x) →
      (gateCoefficient - ε) * n < c.size := by
  have positive : ∀ᶠ n in atTop, 1 ≤ familyThreshold n :=
    Eventually.of_forall fun n => (familyThreshold_one_lt n).le
  have numerical := eventually_lt_of_combined_bound familyThreshold_log_isLittleO positive hε
  have range := Shared.eventually_threshold_range
    (clog_isLittleO familyThreshold_log_isLittleO positive)
  filter_upwards [family_eventually_sumsetDisperser, numerical, range]
    with n disperse bound large c computes
  have same : c.outputFunction interpretation 0 = Extractor.sourceReductionHardFamily n := by
    funext x
    exact congrFun (computes x) 0
  apply bound c.size
  exact size_lowerBound_of_sumsetDisperser c (Nat.zero_lt_of_lt (familyThreshold_one_lt n))
    (by simpa only [same] using disperse) large

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
