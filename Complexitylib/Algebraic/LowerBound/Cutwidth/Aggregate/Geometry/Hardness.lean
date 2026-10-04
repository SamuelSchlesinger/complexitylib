/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Asymptotics

/-!
# An unconditional whole-basis geometric lower bound

The existing fixed polynomial-time family requires more than
`(gateCoefficient - ε)n` gates over the signed unbounded AND/OR/XOR basis, where
`gateCoefficient = (1+2c)/(1+c)` and `c = 1 - H₂(1/4)`. This is approximately
`1.15876032857`. There is no sparsity, depth, fanout, or fan-in hypothesis.

The proof combines affine restrictions in the tradition of Demenkov--Kulikov with
one-way communication accounting in the tradition of Roychowdhury--Orlitsky--Siu.
The hard family is the already checked Chattopadhyay--Liao construction.
No claim of historical priority is part of the theorem.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry

open Filter Algebraic.Aggregate.Geometry

/-- The same explicit family is gate-hard above coefficient one for arbitrary-depth
signed unbounded AND/OR/XOR circuits, including every binary Boolean operation. -/
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

end Algebraic.Cutwidth.Aggregate.Geometry
