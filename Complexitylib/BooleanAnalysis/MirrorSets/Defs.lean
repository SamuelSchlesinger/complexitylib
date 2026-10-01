/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Fibers.Defs

/-!
# Density limit points for top-down lower bounds

Definition 2 of Oliver Korten, *Top-Down Lower Bounds for All Depths*,
ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis

open scoped Classical

/-- A `(p,k)`-limit point of `Y`: with probability at least `3/4`, the
rate-`p` coordinate fiber over `x` has density at least `2^(-k)` in `Y`. -/
def IsDensityLimit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : Finset (ι → Bool)) (p k : ℝ) (x : ι → Bool) : Prop :=
  3 / 4 ≤ bernoulliAverage p
    (fun P => if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0)

end Complexity.BooleanAnalysis
