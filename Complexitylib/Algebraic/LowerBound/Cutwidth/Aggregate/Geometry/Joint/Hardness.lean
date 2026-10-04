/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Asymptotics

/-!
# The explicit family and the joint-message coefficient

The existing Chattopadhyay--Liao family requires more than `(C-ε)n` signed
unbounded AND/OR/XOR gates eventually, where
`C = (H₂(1/4)+3/4)/(H₂(1/4)+1/2)`, approximately `1.19065368005`.
No sparsity, depth, fanout, or fan-in hypothesis is imposed.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Filter Algebraic.Aggregate.Geometry

/-- The fixed explicit family attains the joint-message coefficient over the whole basis. -/
theorem sourceReductionHardFamily_eventually_lt_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ c : Circuit signature n 1,
      c.Computes interpretation (fun x _ => Extractor.sourceReductionHardFamily n x) →
      (gateCoefficient - ε) * n < c.size := by
  have positive : ∀ᶠ n in atTop, 1 ≤ familyThreshold n :=
    Eventually.of_forall fun n => (familyThreshold_one_lt n).le
  have numerical := eventually_lt_of_combined_bound familyThreshold_log_isLittleO positive hε
  have range := eventually_threshold_range (clog_isLittleO familyThreshold_log_isLittleO positive)
  filter_upwards [family_eventually_sumsetDisperser, numerical, range]
    with n disperse bound large c computes
  have same : c.outputFunction interpretation 0 = Extractor.sourceReductionHardFamily n := by
    funext x
    exact congrFun (computes x) 0
  apply bound c.size
  exact size_lowerBound_of_sumsetDisperser c (Nat.zero_lt_of_lt (familyThreshold_one_lt n))
    (by simpa only [same] using disperse) large

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
