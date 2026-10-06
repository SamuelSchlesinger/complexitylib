/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.BigOperators.Field

/-!
# The truncated distance kernel

Fix a graph `H`, a ratio `q` and a radius `R`. The *kernel row* of a vertex `v` is the vector
`z ↦ q ^ dist(v, z)`, cut off to `0` outside the ball of radius `R` around `v`. The *unit kernel
row* divides it by its Euclidean norm. Distances are extended distances, so an unreachable vertex
lies in no sphere or ball and receives `0`. The row of `v` has entry `q ^ 0 = 1` at `v`, so its
norm is at least one.

In a graph of maximum degree three:

* **Growth** (`card_sphere_le`, `card_ball_le`). The sphere of radius `d` has at most
  `3 * 2 ^ d` vertices. A vertex at distance `d + 1` has a neighbour at distance `d`, the
  penultimate vertex of a shortest walk; so a vertex at positive distance `d` has at most two
  neighbours at distance `d + 1`.
* **Correlation** (`sum_kernel_mul_ge`, `sum_unitKernel_mul_ge`). For adjacent `u` and `v` the
  distances from `u` and from `v` to any vertex differ by at most one. Where both rows are
  nonzero their entries `a, b` are equal or differ by the factor `q`, and in either case
  `a b ≥ κ (a ^ 2 + b ^ 2) / 2` with `κ = 2q / (1 + q ^ 2) ≤ 1`. Where exactly one row is
  nonzero the vertex lies on a truncation sphere of radius `R`, and the growth bound charges
  these vertices at most `3 (2 q ^ 2) ^ R` in total. Dividing by the norms, for `q ≥ 0` the
  unit rows of adjacent vertices have inner product at least `κ - 3 (2 q ^ 2) ^ R`. No girth
  assumption is needed.

The ball lemmas `ball_subset_ball_of_adj` and `mem_ball_of_not_disjoint` bound the vertices on
which a row, or a pair of rows, depends.

The `_degree` variants prove the same statements in maximum degree `D ≥ 2`, replacing
the sphere bound by `D * (D - 1) ^ d` and the correlation error by
`D * ((D - 1) * q ^ 2) ^ R`.
-/

@[expose] public section

namespace Complexity.Frontier.Gaussian

section General

variable {W : Type} (H : SimpleGraph W)

/-- The truncated distance kernel: `q ^ dist(v, z)` when the extended distance from `v` to `z`
is at most `R`, and `0` otherwise. -/
noncomputable def kernel (q : ℝ) (R : ℕ) (v z : W) : ℝ :=
  if H.edist v z ≤ R then q ^ H.dist v z else 0

/-- The kernel row of `v` takes the value `1` at `v`. -/
theorem kernel_self (q : ℝ) (R : ℕ) (v : W) : kernel H q R v v = 1 := by
  simp [kernel]

/-- The kernel is nonnegative for a nonnegative ratio. -/
theorem kernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) : 0 ≤ kernel H q R v z := by
  unfold kernel
  split_ifs <;> positivity

/-- The kernel is symmetric. -/
theorem kernel_comm (q : ℝ) (R : ℕ) (v z : W) : kernel H q R v z = kernel H q R z v := by
  simp only [kernel, SimpleGraph.edist_comm (u := v), SimpleGraph.dist_comm (u := v)]

/-- Adjacent vertices have extended distances to any vertex differing by at most one. -/
private theorem edist_le_edist_add_one {u v : W} (huv : H.Adj u v) (z : W) :
    H.edist u z ≤ H.edist v z + 1 :=
  calc H.edist u z ≤ H.edist u v + H.edist v z := SimpleGraph.edist_triangle
    _ = H.edist v z + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr huv, add_comm]

/-- A bounded extended distance is the cast of the natural distance. -/
private theorem edist_eq_dist_of_le {v z : W} {n : ℕ} (h : H.edist v z ≤ n) :
    H.edist v z = H.dist v z :=
  (SimpleGraph.reachable_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)).coe_dist_eq_edist.symm

/-- A vertex at distance `k + 1` has a neighbour at distance `k`. -/
private theorem exists_adj_edist_eq {v z : W} {k : ℕ} (h : H.edist v z = (k + 1 : ℕ)) :
    ∃ w, H.Adj w z ∧ H.edist v w = k := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe (SimpleGraph.edist_comm.trans h)
  cases p with
  | nil => simp at hp
  | @cons _ w _ hadj p =>
    simp only [SimpleGraph.Walk.length_cons, Nat.add_right_cancel_iff] at hp
    have hle : H.edist v w ≤ k := SimpleGraph.edist_comm.trans_le (hp ▸ SimpleGraph.edist_le p)
    refine ⟨w, hadj.symm, le_antisymm hle ?_⟩
    have htri : H.edist v z ≤ H.edist v w + 1 := by
      simpa only [SimpleGraph.edist_comm (u := v)] using edist_le_edist_add_one H hadj v
    obtain ⟨n, hn, -⟩ := ENat.le_natCast_iff.mp hle
    rw [h, hn] at htri
    rw [hn]
    have : k + 1 ≤ n + 1 := by exact_mod_cast htri
    exact_mod_cast (by omega : k ≤ n)

/-- `κ = 2q / (1 + q ^ 2)` is at most one. -/
private theorem kappa_le_one (q : ℝ) : 2 * q / (1 + q ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (q - 1)]

/-- Entries differing by the factor `q` meet the correlation bound with equality. -/
private theorem kappa_mul_sq_add_sq (q x : ℝ) :
    2 * q / (1 + q ^ 2) * (x ^ 2 + (x * q) ^ 2) / 2 = x * (x * q) := by
  field_simp

/-- **Pointwise defect.** For adjacent `u` and `v`, the kernel entries at `z` fall short of `κ`
times their mean square only on the truncation spheres. -/
private theorem kernel_defect_le {q : ℝ} (R : ℕ) {u v : W} (huv : H.Adj u v) (z : W) :
    2 * q / (1 + q ^ 2) * (kernel H q R u z ^ 2 + kernel H q R v z ^ 2) / 2 -
        kernel H q R u z * kernel H q R v z ≤
      (q ^ 2) ^ R / 2 *
        ((if H.edist u z = R then 1 else 0) + (if H.edist v z = R then 1 else 0)) := by
  wlog huvz : H.edist u z ≤ H.edist v z generalizing u v
  · linarith [this huv.symm (le_of_not_ge huvz)]
  have hκ := kappa_le_one q
  have hIv : (0 : ℝ) ≤ if H.edist v z = R then 1 else 0 := by split_ifs <;> norm_num
  have hRHS : 0 ≤ (q ^ 2) ^ R / 2 *
      ((if H.edist u z = R then 1 else 0) + (if H.edist v z = R then 1 else 0)) := by
    split_ifs <;> positivity
  have h := edist_le_edist_add_one H huv.symm z
  unfold kernel
  by_cases hv : H.edist v z ≤ R
  · -- Both entries are nonzero: the distances are equal or differ by one.
    have hu := huvz.trans hv
    rw [ite_eq_left hu, ite_eq_left hv]
    refine le_trans ?_ hRHS
    rw [edist_eq_dist_of_le H hu, edist_eq_dist_of_le H hv] at huvz h
    have h1 : H.dist u z ≤ H.dist v z := by exact_mod_cast huvz
    have h2 : H.dist v z ≤ H.dist u z + 1 := by exact_mod_cast h
    rcases (by omega : H.dist v z = H.dist u z ∨ H.dist v z = H.dist u z + 1) with h | h
    · rw [h]
      nlinarith [mul_le_mul_of_nonneg_right hκ (sq_nonneg (q ^ H.dist u z))]
    · rw [h, pow_succ q (H.dist u z)]
      linarith [kappa_mul_sq_add_sq q (q ^ H.dist u z)]
  rw [ite_eq_right hv]
  by_cases hu : H.edist u z ≤ R
  · -- Only the entry of `u` is nonzero, so `z` lies on the sphere of radius `R` around `u`.
    have hd := edist_eq_dist_of_le H hu
    rw [hd] at h hu ⊢
    have hR : H.dist u z = R := by
      have hlt : R < H.dist u z + 1 := by exact_mod_cast (lt_of_not_ge hv).trans_le h
      have hle : H.dist u z ≤ R := by exact_mod_cast hu
      omega
    rw [hR, ite_eq_left le_rfl, ite_eq_left rfl, ← pow_mul, mul_comm R 2, pow_mul]
    have hP : 0 ≤ (q ^ 2) ^ R := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hκ hP, mul_nonneg hP hIv]
  · rw [ite_eq_right hu]
    simpa using hRHS

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

end General

section Finite

variable {W : Type} [Fintype W] (H : SimpleGraph W)

@[simp]
theorem mem_sphere {v z : W} {d : ℕ} : z ∈ sphere H v d ↔ H.edist v z = d := by
  simp [sphere]

@[simp]
theorem mem_ball {v z : W} {r : ℕ} : z ∈ ball H v r ↔ H.edist v z ≤ r := by
  simp [ball]

theorem mem_ball_self (v : W) (r : ℕ) : v ∈ ball H v r := by
  simp

theorem mem_ball_comm {v z : W} {r : ℕ} : z ∈ ball H v r ↔ v ∈ ball H z r := by
  rw [mem_ball, mem_ball, SimpleGraph.edist_comm]

theorem ball_mono (v : W) {r r' : ℕ} (h : r ≤ r') : ball H v r ⊆ ball H v r' :=
  fun _ hz => (mem_ball H).mpr (((mem_ball H).mp hz).trans (by exact_mod_cast h))

theorem sphere_subset_ball (v : W) (r : ℕ) : sphere H v r ⊆ ball H v r :=
  fun _ hz => (mem_ball H).mpr ((mem_sphere H).mp hz).le

theorem sphere_zero (v : W) : sphere H v 0 = {v} := by
  ext z
  rw [mem_sphere, Nat.cast_zero, SimpleGraph.edist_eq_zero_iff, Finset.mem_singleton, eq_comm]

theorem ball_zero (v : W) : ball H v 0 = {v} := by
  ext z
  rw [mem_ball, Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff,
    Finset.mem_singleton, eq_comm]

/-- The ball around a neighbour lies in the ball of one larger radius. -/
theorem ball_subset_ball_of_adj {u v : W} (h : H.Adj u v) (R : ℕ) :
    ball H v R ⊆ ball H u (R + 1) := by
  intro z hz
  rw [mem_ball] at hz ⊢
  calc H.edist u z ≤ H.edist v z + 1 := edist_le_edist_add_one H h z
    _ ≤ R + 1 := by gcongr
    _ = ((R + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- Overlapping balls have centres within the sum of their radii. -/
theorem mem_ball_of_not_disjoint {a b : W} {r r' : ℕ}
    (h : ¬ Disjoint (ball H a r) (ball H b r')) : b ∈ ball H a (r + r') := by
  obtain ⟨z, hza, hzb⟩ := Finset.not_disjoint_iff.mp h
  rw [mem_ball] at hza hzb ⊢
  calc H.edist a b ≤ H.edist a z + H.edist z b := SimpleGraph.edist_triangle
    _ ≤ r + r' := by rw [SimpleGraph.edist_comm (u := z)]; exact add_le_add hza hzb
    _ = ((r + r' : ℕ) : ℕ∞) := by push_cast; rfl

/-- The kernel row of `v` vanishes outside the ball of radius `R`. -/
theorem kernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    kernel H q R v z = 0 := by
  rw [mem_ball] at h
  simp [kernel, h]

/-- Inside the ball of radius `R`, the kernel row of `v` is `q ^ dist(v, z)`. -/
theorem kernel_of_mem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∈ ball H v R) :
    kernel H q R v z = q ^ H.dist v z := by
  rw [mem_ball] at h
  simp [kernel, h]

/-- Every kernel row has squared norm at least one. -/
theorem one_le_sum_kernel_sq {q : ℝ} (R : ℕ) (v : W) : 1 ≤ ∑ z, kernel H q R v z ^ 2 :=
  calc (1 : ℝ) = kernel H q R v v ^ 2 := by rw [kernel_self, one_pow]
    _ ≤ ∑ z, kernel H q R v z ^ 2 :=
      Finset.single_le_sum (f := fun z => kernel H q R v z ^ 2) (fun z _ => sq_nonneg _)
        (Finset.mem_univ v)

/-- The unit kernel row has norm one. -/
theorem sum_unitKernel_sq (q : ℝ) (R : ℕ) (v : W) : ∑ z, unitKernel H q R v z ^ 2 = 1 := by
  have hA : 1 ≤ ∑ y, kernel H q R v y ^ 2 := one_le_sum_kernel_sq H R v
  simp only [unitKernel, div_pow, ← Finset.sum_div]
  rw [Real.sq_sqrt (by linarith), div_self (by linarith)]

/-- The unit kernel row of `v` vanishes outside the ball of radius `R`. -/
theorem unitKernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    unitKernel H q R v z = 0 := by
  rw [unitKernel, kernel_eq_zero_of_notMem_ball H h, zero_div]

/-- The unit kernel is nonnegative for a nonnegative ratio. -/
theorem unitKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) :
    0 ≤ unitKernel H q R v z :=
  div_nonneg (kernel_nonneg H hq R v z) (Real.sqrt_nonneg _)

variable [DecidableRel H.Adj]

/-- A vertex at positive distance has a neighbour one step closer, leaving at most
`D - 1` neighbours one step farther. -/
private theorem card_filter_neighborFinset_le {D : ℕ} (degree : ∀ v, H.degree v ≤ D)
    {v w : W} {d : ℕ}
    (hw : H.edist v w = (d + 1 : ℕ)) :
    ((H.neighborFinset w).filter fun y => H.edist v y = (d + 1 + 1 : ℕ)).card ≤ D - 1 := by
  classical
  obtain ⟨p, hpw, hp⟩ := exists_adj_edist_eq H hw
  have hsub : ((H.neighborFinset w).filter fun y => H.edist v y = (d + 1 + 1 : ℕ)) ⊆
      (H.neighborFinset w).erase p := by
    intro y hy
    rw [Finset.mem_filter] at hy
    refine Finset.mem_erase.mpr ⟨?_, hy.1⟩
    rintro rfl
    have : d = d + 1 + 1 := by exact_mod_cast hp.symm.trans hy.2
    omega
  calc _ ≤ ((H.neighborFinset w).erase p).card := Finset.card_le_card hsub
    _ = H.degree w - 1 := by
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset w p).mpr hpw.symm),
        H.card_neighborFinset_eq_degree]
    _ ≤ D - 1 := Nat.sub_le_sub_right (degree w) 1

/-- Every vertex of the sphere of radius `d + 1` is a neighbour of a vertex of the sphere of
radius `d`. -/
private theorem card_sphere_succ_le_sum (v : W) (d : ℕ) :
    (sphere H v (d + 1)).card ≤ ∑ w ∈ sphere H v d,
      ((H.neighborFinset w).filter fun y => H.edist v y = (d + 1 : ℕ)).card := by
  classical
  refine (Finset.card_le_card fun z hz => ?_).trans Finset.card_biUnion_le
  obtain ⟨w, hwz, hw⟩ := exists_adj_edist_eq H ((mem_sphere H).mp hz)
  exact Finset.mem_biUnion.mpr ⟨w, (mem_sphere H).mpr hw,
    Finset.mem_filter.mpr ⟨(H.mem_neighborFinset w z).mpr hwz, (mem_sphere H).mp hz⟩⟩

/-- In maximum degree `D`, the sphere of radius `d + 1` has at most
`D * (D - 1) ^ d` vertices. -/
theorem card_sphere_succ_le_degree {D : ℕ} (degree : ∀ v, H.degree v ≤ D) (v : W) (d : ℕ) :
    (sphere H v (d + 1)).card ≤ D * (D - 1) ^ d := by
  induction d with
  | zero =>
    refine (card_sphere_succ_le_sum H v 0).trans ?_
    rw [sphere_zero, Finset.sum_singleton, pow_zero, mul_one]
    exact (Finset.card_filter_le _ _).trans ((H.card_neighborFinset_eq_degree v).trans_le
      (degree v))
  | succ d ih =>
    refine (card_sphere_succ_le_sum H v (d + 1)).trans ?_
    calc _ ≤ ∑ _w ∈ sphere H v (d + 1), (D - 1) := Finset.sum_le_sum fun w hw =>
          card_filter_neighborFinset_le H degree ((mem_sphere H).mp hw)
      _ = (D - 1) * (sphere H v (d + 1)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ (D - 1) * (D * (D - 1) ^ d) := Nat.mul_le_mul_left _ ih
      _ = D * (D - 1) ^ (d + 1) := by ring

theorem card_sphere_succ_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (d : ℕ) :
    (sphere H v (d + 1)).card ≤ 3 * 2 ^ d := card_sphere_succ_le_degree H degree v d

/-- Sphere growth in any fixed maximum degree. -/
theorem card_sphere_le_degree {D : ℕ} (hD : 2 ≤ D) (degree : ∀ v, H.degree v ≤ D)
    (v : W) (d : ℕ) : (sphere H v d).card ≤ D * (D - 1) ^ d := by
  cases d with
  | zero => simpa [sphere_zero] using (by lia : 1 ≤ D)
  | succ d =>
    refine (card_sphere_succ_le_degree H degree v d).trans ?_
    rw [pow_succ, ← mul_assoc]
    exact Nat.le_mul_of_pos_right _ (by lia)

/-- A convenient locality bound; sharp ball growth is unnecessary for concentration. -/
theorem card_ball_le_degree {D : ℕ} (hD : 2 ≤ D) (degree : ∀ v, H.degree v ≤ D)
    (v : W) (r : ℕ) : (ball H v r).card ≤ D ^ (r + 1) := by
  induction r with
  | zero => simpa [ball_zero] using (by lia : 1 ≤ D)
  | succ r ih =>
    classical
    have hsub : ball H v (r + 1) ⊆ ball H v r ∪ sphere H v (r + 1) := by
      intro z hz
      rw [mem_ball] at hz
      rw [Finset.mem_union, mem_ball, mem_sphere]
      obtain ⟨n, hn, hle⟩ := ENat.le_natCast_iff.mp hz
      rw [hn]
      rcases Nat.lt_or_ge n (r + 1) with h | h
      · exact Or.inl (by exact_mod_cast (by lia : n ≤ r))
      · exact Or.inr (by rw [show n = r + 1 by lia])
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hs := card_sphere_succ_le_degree H degree v r
    have hp : (D - 1) ^ r ≤ D ^ r := Nat.pow_le_pow_left (by lia) r
    have hmul := Nat.mul_le_mul_left D hp
    have hg : D ^ (r + 1) + D ^ (r + 1) ≤ D ^ (r + 1) * D := by
      nlinarith [Nat.mul_le_mul_left (D ^ (r + 1)) hD]
    rw [← pow_succ'] at hmul
    rw [pow_succ D (r + 1)]
    nlinarith

/-- In a graph of maximum degree three, the sphere of radius `d` has at most
`3 * 2 ^ d` vertices. -/
theorem card_sphere_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (d : ℕ) :
    (sphere H v d).card ≤ 3 * 2 ^ d := by
  cases d with
  | zero => simp [sphere_zero]
  | succ d => exact (card_sphere_succ_le H degree v d).trans (by rw [pow_succ]; omega)

/-- A form of `card_ball_le` strong enough to carry the induction on the radius. -/
private theorem card_ball_add_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (r : ℕ) :
    (ball H v r).card + 3 ≤ 3 * 2 ^ (r + 1) := by
  induction r with
  | zero => simp [ball_zero]
  | succ r ih =>
    classical
    have hsub : ball H v (r + 1) ⊆ ball H v r ∪ sphere H v (r + 1) := by
      intro z hz
      rw [mem_ball] at hz
      rw [Finset.mem_union, mem_ball, mem_sphere]
      obtain ⟨n, hn, hle⟩ := ENat.le_natCast_iff.mp hz
      rw [hn]
      rcases Nat.lt_or_ge n (r + 1) with h | h
      · exact Or.inl (by exact_mod_cast (by omega : n ≤ r))
      · exact Or.inr (by rw [show n = r + 1 by omega])
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := card_sphere_le H degree v (r + 1)
    rw [pow_succ 2 (r + 1)]
    omega

/-- In a graph of maximum degree three, the ball of radius `r` has at most
`3 * 2 ^ (r + 1)` vertices. -/
theorem card_ball_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (r : ℕ) :
    (ball H v r).card ≤ 3 * 2 ^ (r + 1) := by
  have := card_ball_add_le H degree v r
  omega

/-- **Pointwise correlation inequality, summed.** For adjacent vertices the kernel rows have
inner product at least `κ` times the mean of their squared norms, up to the truncation
boundary, where `κ = 2q/(1+q^2)`. -/
theorem sum_kernel_mul_ge_degree {D : ℕ} (hD : 2 ≤ D) (degree : ∀ v, H.degree v ≤ D)
    (q : ℝ) (R : ℕ) {u v : W}
    (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) * ((∑ z, kernel H q R u z ^ 2) + ∑ z, kernel H q R v z ^ 2) / 2 -
        D * ((D - 1 : ℕ) * q ^ 2) ^ R ≤ ∑ z, kernel H q R u z * kernel H q R v z := by
  have hsum : 2 * q / (1 + q ^ 2) *
        ((∑ z, kernel H q R u z ^ 2) + ∑ z, kernel H q R v z ^ 2) / 2 -
        ∑ z, kernel H q R u z * kernel H q R v z =
      ∑ z, (2 * q / (1 + q ^ 2) * (kernel H q R u z ^ 2 + kernel H q R v z ^ 2) / 2 -
        kernel H q R u z * kernel H q R v z) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hle := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) =>
    kernel_defect_le H (q := q) R huv z
  have hcount : ∑ z, (q ^ 2) ^ R / 2 *
        ((if H.edist u z = R then (1 : ℝ) else 0) + (if H.edist v z = R then 1 else 0)) =
      (q ^ 2) ^ R / 2 * (((sphere H u R).card : ℝ) + (sphere H v R).card) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
    rfl
  have hu : ((sphere H u R).card : ℝ) ≤ D * (D - 1 : ℕ) ^ R := by
    exact_mod_cast card_sphere_le_degree H hD degree u R
  have hv : ((sphere H v R).card : ℝ) ≤ D * (D - 1 : ℕ) ^ R := by
    exact_mod_cast card_sphere_le_degree H hD degree v R
  have hP : 0 ≤ (q ^ 2) ^ R := by positivity
  have hbound : (q ^ 2) ^ R / 2 * (((sphere H u R).card : ℝ) + (sphere H v R).card) ≤
      D * ((D - 1 : ℕ) * q ^ 2) ^ R := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hu hv) hP]
  linarith

theorem sum_kernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) (q : ℝ) (R : ℕ) {u v : W}
    (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) * ((∑ z, kernel H q R u z ^ 2) + ∑ z, kernel H q R v z ^ 2) / 2 -
        3 * (2 * q ^ 2) ^ R ≤ ∑ z, kernel H q R u z * kernel H q R v z := by
  simpa using sum_kernel_mul_ge_degree H (by norm_num : 2 ≤ 3) degree q R huv

/-- **Correlation of adjacent rows.** For a nonnegative ratio `q`, the unit kernel rows of
adjacent vertices have inner product at least `2q/(1+q^2) - D ((D-1)q^2)^R`. -/
theorem sum_unitKernel_mul_ge_degree {D : ℕ} (hD : 2 ≤ D) (degree : ∀ v, H.degree v ≤ D)
    {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ)
    {u v : W} (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) - D * ((D - 1 : ℕ) * q ^ 2) ^ R ≤
      ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
  simp only [unitKernel, div_mul_div_comm, ← Finset.sum_div]
  have hC := sum_kernel_mul_ge_degree H hD degree q R huv
  have hA := one_le_sum_kernel_sq H (q := q) R u
  have hB := one_le_sum_kernel_sq H (q := q) R v
  generalize ∑ z, kernel H q R u z * kernel H q R v z = C at hC ⊢
  generalize ∑ z, kernel H q R u z ^ 2 = A at hA hC ⊢
  generalize ∑ z, kernel H q R v z ^ 2 = B at hB hC ⊢
  have hκ : 0 ≤ 2 * q / (1 + q ^ 2) := by positivity
  have he : 0 ≤ (D : ℝ) * ((D - 1 : ℕ) * q ^ 2) ^ R := by positivity
  have hs : 1 ≤ Real.sqrt A := Real.one_le_sqrt.mpr hA
  have ht : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt (by linarith)
  have htB : Real.sqrt B ^ 2 = B := Real.sq_sqrt (by linarith)
  have hamgm : 2 * (Real.sqrt A * Real.sqrt B) ≤ A + B := by
    nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B)]
  have h1 : 1 ≤ Real.sqrt A * Real.sqrt B := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hamgm hκ, mul_le_mul_of_nonneg_left h1 he]

theorem sum_unitKernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ)
    {u v : W} (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ≤
      ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
  simpa using sum_unitKernel_mul_ge_degree H (by norm_num : 2 ≤ 3) degree hq0 R huv

end Finite

end Complexity.Frontier.Gaussian
