/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Kernel.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Kernel.Internal

/-!
# Correlation of truncated distance kernels

This file bounds the truncated distance kernel of `Gaussian.Kernel.Defs` on a
graph of maximum degree three.

* `card_sphere_le` and `card_ball_le`: spheres and balls grow at most like
  `3 * 2 ^ d`, since a vertex at positive distance `d` has a neighbour at
  distance `d - 1` and hence at most two neighbours at distance `d + 1`.
* `sum_kernel_mul_ge`: for adjacent `u` and `v`, the kernel rows have inner
  product at least `κ = 2q / (1 + q²)` times the mean of their squared norms,
  up to `3 * (2 * q ^ 2) ^ R` contributed by the truncation spheres.
* `sum_unitKernel_mul_ge`: for `0 ≤ q`, the unit kernel rows of adjacent
  vertices have inner product at least `κ - 3 * (2 * q ^ 2) ^ R`.

The ball lemmas `ball_subset_ball_of_adj` and `mem_ball_of_not_disjoint` bound
the vertices on which a kernel row or a pair of adjacent rows depends.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

section General

variable {W : Type} (H : SimpleGraph W)

/-- The kernel row of `v` takes the value `1` at `v`. -/
theorem kernel_self (q : ℝ) (R : ℕ) (v : W) : kernel H q R v v = 1 :=
  Internal.kernel_self H q R v

/-- The kernel is nonnegative for a nonnegative ratio. -/
theorem kernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) : 0 ≤ kernel H q R v z :=
  Internal.kernel_nonneg H hq R v z

/-- The kernel is symmetric. -/
theorem kernel_comm (q : ℝ) (R : ℕ) (v z : W) : kernel H q R v z = kernel H q R z v :=
  Internal.kernel_comm H q R v z

end General

section Finite

variable {W : Type} [Fintype W] (H : SimpleGraph W)

@[simp]
theorem mem_sphere {v z : W} {d : ℕ} : z ∈ sphere H v d ↔ H.edist v z = d :=
  Internal.mem_sphere H

@[simp]
theorem mem_ball {v z : W} {r : ℕ} : z ∈ ball H v r ↔ H.edist v z ≤ r :=
  Internal.mem_ball H

theorem mem_ball_self (v : W) (r : ℕ) : v ∈ ball H v r :=
  Internal.mem_ball_self H v r

theorem mem_ball_comm {v z : W} {r : ℕ} : z ∈ ball H v r ↔ v ∈ ball H z r :=
  Internal.mem_ball_comm H

theorem ball_mono (v : W) {r r' : ℕ} (h : r ≤ r') : ball H v r ⊆ ball H v r' :=
  Internal.ball_mono H v h

theorem sphere_subset_ball (v : W) (r : ℕ) : sphere H v r ⊆ ball H v r :=
  Internal.sphere_subset_ball H v r

theorem sphere_zero (v : W) : sphere H v 0 = {v} :=
  Internal.sphere_zero H v

theorem ball_zero (v : W) : ball H v 0 = {v} :=
  Internal.ball_zero H v

/-- The ball around a neighbour lies in the ball of one larger radius. -/
theorem ball_subset_ball_of_adj {u v : W} (h : H.Adj u v) (R : ℕ) :
    ball H v R ⊆ ball H u (R + 1) :=
  Internal.ball_subset_ball_of_adj H h R

/-- Overlapping balls have centres within the sum of their radii. -/
theorem mem_ball_of_not_disjoint {a b : W} {r r' : ℕ}
    (h : ¬ Disjoint (ball H a r) (ball H b r')) : b ∈ ball H a (r + r') :=
  Internal.mem_ball_of_not_disjoint H h

/-- The kernel row of `v` vanishes outside the ball of radius `R`. -/
theorem kernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    kernel H q R v z = 0 :=
  Internal.kernel_eq_zero_of_notMem_ball H h

theorem kernel_of_mem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∈ ball H v R) :
    kernel H q R v z = q ^ H.dist v z :=
  Internal.kernel_of_mem_ball H h

/-- Every kernel row has squared norm at least one. -/
theorem one_le_sum_kernel_sq {q : ℝ} (R : ℕ) (v : W) : 1 ≤ ∑ z, kernel H q R v z ^ 2 :=
  Internal.one_le_sum_kernel_sq H R v

/-- The unit kernel row has norm one. -/
theorem sum_unitKernel_sq (q : ℝ) (R : ℕ) (v : W) : ∑ z, unitKernel H q R v z ^ 2 = 1 :=
  Internal.sum_unitKernel_sq H q R v

theorem unitKernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    unitKernel H q R v z = 0 :=
  Internal.unitKernel_eq_zero_of_notMem_ball H h

theorem unitKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) :
    0 ≤ unitKernel H q R v z :=
  Internal.unitKernel_nonneg H hq R v z

variable [DecidableRel H.Adj]

/-- In a graph of maximum degree three, the sphere of radius `d + 1` has at most
`3 * 2 ^ d` vertices. -/
theorem card_sphere_succ_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (d : ℕ) :
    (sphere H v (d + 1)).card ≤ 3 * 2 ^ d :=
  Internal.card_sphere_succ_le H degree v d

/-- In a graph of maximum degree three, the sphere of radius `d` has at most
`3 * 2 ^ d` vertices. -/
theorem card_sphere_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (d : ℕ) :
    (sphere H v d).card ≤ 3 * 2 ^ d :=
  Internal.card_sphere_le H degree v d

/-- In a graph of maximum degree three, the ball of radius `r` has at most
`3 * 2 ^ (r + 1)` vertices. -/
theorem card_ball_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (r : ℕ) :
    (ball H v r).card ≤ 3 * 2 ^ (r + 1) :=
  Internal.card_ball_le H degree v r

/-- **Pointwise correlation inequality, summed.** For adjacent vertices the kernel rows
have inner product at least `κ` times the mean of their squared norms, up to the
truncation boundary, where `κ = 2q/(1+q²)`. -/
theorem sum_kernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) (q : ℝ) (R : ℕ) {u v : W}
    (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) * ((∑ z, kernel H q R u z ^ 2) + ∑ z, kernel H q R v z ^ 2) / 2 -
        3 * (2 * q ^ 2) ^ R ≤ ∑ z, kernel H q R u z * kernel H q R v z :=
  Internal.sum_kernel_mul_ge H degree q R huv

/-- **Correlation of adjacent rows.** For a nonnegative ratio `q`, the unit kernel rows
of adjacent vertices have inner product at least `2q/(1+q²) - 3 (2q²)^R`. -/
theorem sum_unitKernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ)
    {u v : W} (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ≤
      ∑ z, unitKernel H q R u z * unitKernel H q R v z :=
  Internal.sum_unitKernel_mul_ge H degree hq0 R huv

end Finite

end Algebraic.Cutwidth.Gaussian
