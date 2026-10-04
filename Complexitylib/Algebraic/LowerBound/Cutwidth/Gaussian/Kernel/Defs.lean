/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The truncated distance kernel

For a graph `H`, a ratio `q`, and a radius `R`, the kernel row of a vertex `v`
assigns `q ^ dist(v, z)` to every vertex `z` within extended distance `R` of `v`
and `0` to every other vertex. Unreachable vertices have extended distance `⊤`
and therefore receive `0`. The unit kernel row divides by the Euclidean norm of
the row, which is at least one because the row has value `q ^ 0 = 1` at `v`.

Spheres and balls are measured by extended distance, so an unreachable vertex
lies in no sphere and no ball.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

variable {W : Type} (H : SimpleGraph W)

/-- The truncated distance kernel: `q ^ dist(v, z)` when the extended distance
from `v` to `z` is at most `R`, and `0` otherwise. -/
noncomputable def kernel (q : ℝ) (R : ℕ) (v z : W) : ℝ :=
  if H.edist v z ≤ R then q ^ H.dist v z else 0

variable [Fintype W]

/-- The vertices at extended distance exactly `d` from `v`. -/
noncomputable def sphere (v : W) (d : ℕ) : Finset W :=
  Finset.univ.filter fun z => H.edist v z = d

/-- The vertices at extended distance at most `r` from `v`. -/
noncomputable def ball (v : W) (r : ℕ) : Finset W :=
  Finset.univ.filter fun z => H.edist v z ≤ r

/-- The kernel row of `v` divided by its Euclidean norm. -/
noncomputable def unitKernel (q : ℝ) (R : ℕ) (v z : W) : ℝ :=
  kernel H q R v z / Real.sqrt (∑ y, kernel H q R v y ^ 2)

end Algebraic.Cutwidth.Gaussian
