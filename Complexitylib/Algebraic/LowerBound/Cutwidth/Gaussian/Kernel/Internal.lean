/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Kernel.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Distance-kernel internals

Proofs of the sphere growth bounds and of the correlation inequality for the
truncated distance kernel.

A vertex at distance `d + 1` from `v` has a neighbour at distance `d`: the
penultimate vertex of a shortest walk. In a graph of maximum degree three,
a vertex at positive distance `d` therefore has at most two neighbours at
distance `d + 1`, which gives `|S_{d+1}(v)| ≤ 3 * 2 ^ d`.

For adjacent `u` and `v`, the distances from `u` and `v` to any vertex differ by
at most one. When both kernel values are nonzero they are equal or differ by
the factor `q`, and `x * y ≥ κ (x² + y²) / 2` with `κ = 2q / (1 + q²)`. When
exactly one is nonzero it lies on the truncation sphere of radius `R`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

section General

variable {W : Type} (H : SimpleGraph W)

/-- Adjacent vertices have extended distances to any vertex differing by at most one. -/
theorem edist_le_edist_add_one {u v : W} (huv : H.Adj u v) (z : W) :
    H.edist u z ≤ H.edist v z + 1 :=
  calc H.edist u z ≤ H.edist u v + H.edist v z := SimpleGraph.edist_triangle
    _ = H.edist v z + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr huv, add_comm]

/-- A bounded extended distance is the cast of the natural distance. -/
theorem edist_eq_dist_of_le {v z : W} {n : ℕ} (h : H.edist v z ≤ n) :
    H.edist v z = H.dist v z := by
  have hne : H.edist v z ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) h
  exact (SimpleGraph.reachable_of_edist_ne_top hne).coe_dist_eq_edist.symm

/-- A vertex at distance `k + 1` has a neighbour at distance `k`. -/
theorem exists_adj_edist_eq {v z : W} {k : ℕ} (h : H.edist v z = (k + 1 : ℕ)) :
    ∃ w, H.Adj w z ∧ H.edist v w = k := by
  have h' : H.edist z v = (k + 1 : ℕ) := by rw [SimpleGraph.edist_comm, h]
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe h'
  cases p with
  | nil => simp at hp
  | @cons _ w _ hadj q =>
    simp only [SimpleGraph.Walk.length_cons, Nat.add_right_cancel_iff] at hp
    have hle : H.edist v w ≤ k := by
      rw [SimpleGraph.edist_comm, ← hp]
      exact SimpleGraph.edist_le q
    refine ⟨w, hadj.symm, le_antisymm hle ?_⟩
    have htri : H.edist v z ≤ H.edist v w + H.edist w z := SimpleGraph.edist_triangle
    rw [h, SimpleGraph.edist_eq_one_iff_adj.mpr hadj.symm] at htri
    obtain ⟨n, hn, -⟩ := ENat.le_natCast_iff.mp hle
    rw [hn] at htri ⊢
    have : k + 1 ≤ n + 1 := by exact_mod_cast htri
    exact_mod_cast (by omega : k ≤ n)

theorem kernel_self (q : ℝ) (R : ℕ) (v : W) : kernel H q R v v = 1 := by
  simp [kernel]

theorem kernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) : 0 ≤ kernel H q R v z := by
  unfold kernel
  split_ifs <;> positivity

theorem kernel_comm (q : ℝ) (R : ℕ) (v z : W) : kernel H q R v z = kernel H q R z v := by
  simp only [kernel, SimpleGraph.edist_comm (u := v), SimpleGraph.dist_comm (u := v)]

/-- `κ = 2q / (1 + q²)` is at most one for every real `q`. -/
theorem kappa_le_one (q : ℝ) : 2 * q / (1 + q ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (q - 1)]

/-- Rows whose distances differ by one meet the correlation bound with equality. -/
theorem kappa_mul_sq_add_sq (q x : ℝ) :
    2 * q / (1 + q ^ 2) * (x ^ 2 + (x * q) ^ 2) / 2 = x * (x * q) := by
  have hpos : (0 : ℝ) < 1 + q ^ 2 := by positivity
  field_simp

/-- The pointwise defect on the truncation boundary. -/
private theorem boundary_defect_le {q : ℝ} (R : ℕ) (I : ℝ) (hI : 0 ≤ I) :
    2 * q / (1 + q ^ 2) * ((q ^ R) ^ 2 + 0 ^ 2) / 2 - q ^ R * 0 ≤ (q ^ 2) ^ R / 2 * (1 + I) := by
  have hκ := kappa_le_one q
  have hP : 0 ≤ (q ^ 2) ^ R := by positivity
  rw [← pow_mul, mul_comm R 2, pow_mul]
  nlinarith [mul_le_mul_of_nonneg_right hκ hP, mul_nonneg hP hI]

/-- **Pointwise defect.** For adjacent `u` and `v`, the kernel values at `z` fall short
of `κ` times their mean square only on the truncation spheres. -/
theorem kernel_defect_le {q : ℝ} (R : ℕ) {u v : W} (huv : H.Adj u v) (z : W) :
    2 * q / (1 + q ^ 2) * (kernel H q R u z ^ 2 + kernel H q R v z ^ 2) / 2 -
        kernel H q R u z * kernel H q R v z ≤
      (q ^ 2) ^ R / 2 *
        ((if H.edist u z = R then 1 else 0) + (if H.edist v z = R then 1 else 0)) := by
  have hκ := kappa_le_one q
  have hP : 0 ≤ (q ^ 2) ^ R := by positivity
  have hIu : (0 : ℝ) ≤ if H.edist u z = R then 1 else 0 := by split_ifs <;> norm_num
  have hIv : (0 : ℝ) ≤ if H.edist v z = R then 1 else 0 := by split_ifs <;> norm_num
  have hRHS : 0 ≤ (q ^ 2) ^ R / 2 *
      ((if H.edist u z = R then 1 else 0) + (if H.edist v z = R then 1 else 0)) := by
    positivity
  have h1 := edist_le_edist_add_one H huv z
  have h2 := edist_le_edist_add_one H huv.symm z
  unfold kernel
  by_cases ha : H.edist u z ≤ R <;> by_cases hb : H.edist v z ≤ R
  · rw [ite_eq_left ha, ite_eq_left hb]
    refine le_trans ?_ hRHS
    rw [edist_eq_dist_of_le H ha, edist_eq_dist_of_le H hb] at h1 h2
    have h1' : H.dist u z ≤ H.dist v z + 1 := by exact_mod_cast h1
    have h2' : H.dist v z ≤ H.dist u z + 1 := by exact_mod_cast h2
    rcases (by omega : H.dist v z = H.dist u z ∨ H.dist v z = H.dist u z + 1 ∨
        H.dist u z = H.dist v z + 1) with h | h | h
    · rw [h]
      nlinarith [mul_le_mul_of_nonneg_right hκ (sq_nonneg (q ^ H.dist u z))]
    · rw [h, pow_succ q (H.dist u z)]
      have := kappa_mul_sq_add_sq q (q ^ H.dist u z)
      linarith
    · rw [h, pow_succ q (H.dist v z)]
      have := kappa_mul_sq_add_sq q (q ^ H.dist v z)
      linarith
  · rw [ite_eq_left ha, ite_eq_right hb]
    have hb' : (R : ℕ∞) < H.edist v z := lt_of_not_ge hb
    have hd := edist_eq_dist_of_le H ha
    rw [hd] at h2 ha ⊢
    have hlt : R < H.dist u z + 1 := by exact_mod_cast hb'.trans_le h2
    have hle : H.dist u z ≤ R := by exact_mod_cast ha
    have hR : H.dist u z = R := by omega
    rw [hR, ite_eq_left rfl]
    exact boundary_defect_le R _ hIv
  · rw [ite_eq_right ha, ite_eq_left hb]
    have ha' : (R : ℕ∞) < H.edist u z := lt_of_not_ge ha
    have hd := edist_eq_dist_of_le H hb
    rw [hd] at h1 hb ⊢
    have hlt : R < H.dist v z + 1 := by exact_mod_cast ha'.trans_le h1
    have hle : H.dist v z ≤ R := by exact_mod_cast hb
    have hR : H.dist v z = R := by omega
    rw [hR, ite_eq_left rfl]
    have := boundary_defect_le (q := q) R _ hIu
    linarith
  · rw [ite_eq_right ha, ite_eq_right hb]
    simpa using hRHS

end General

section Finite

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem mem_sphere {v z : W} {d : ℕ} : z ∈ sphere H v d ↔ H.edist v z = d := by
  simp [sphere]

theorem mem_ball {v z : W} {r : ℕ} : z ∈ ball H v r ↔ H.edist v z ≤ r := by
  simp [ball]

theorem mem_ball_self (v : W) (r : ℕ) : v ∈ ball H v r := by
  simp [mem_ball]

theorem mem_ball_comm {v z : W} {r : ℕ} : z ∈ ball H v r ↔ v ∈ ball H z r := by
  rw [mem_ball, mem_ball, SimpleGraph.edist_comm]

theorem ball_mono (v : W) {r r' : ℕ} (h : r ≤ r') : ball H v r ⊆ ball H v r' := by
  intro z hz
  rw [mem_ball] at hz ⊢
  exact hz.trans (by exact_mod_cast h)

theorem sphere_subset_ball (v : W) (r : ℕ) : sphere H v r ⊆ ball H v r := by
  intro z hz
  rw [mem_sphere] at hz
  rw [mem_ball, hz]

theorem ball_subset_ball_of_adj {u v : W} (h : H.Adj u v) (R : ℕ) :
    ball H v R ⊆ ball H u (R + 1) := by
  intro z hz
  rw [mem_ball] at hz ⊢
  calc H.edist u z ≤ H.edist v z + 1 := edist_le_edist_add_one H h z
    _ ≤ R + 1 := by gcongr
    _ = ((R + 1 : ℕ) : ℕ∞) := by push_cast; rfl

theorem mem_ball_of_not_disjoint {a b : W} {r r' : ℕ}
    (h : ¬ Disjoint (ball H a r) (ball H b r')) : b ∈ ball H a (r + r') := by
  obtain ⟨z, hza, hzb⟩ := Finset.not_disjoint_iff.mp h
  rw [mem_ball] at hza hzb ⊢
  calc H.edist a b ≤ H.edist a z + H.edist z b := SimpleGraph.edist_triangle
    _ ≤ r + r' := by rw [SimpleGraph.edist_comm (u := z)]; exact add_le_add hza hzb
    _ = ((r + r' : ℕ) : ℕ∞) := by push_cast; rfl

theorem sphere_zero (v : W) : sphere H v 0 = {v} := by
  ext z
  rw [mem_sphere, Nat.cast_zero, SimpleGraph.edist_eq_zero_iff, Finset.mem_singleton, eq_comm]

theorem ball_zero (v : W) : ball H v 0 = {v} := by
  ext z
  rw [mem_ball, Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff,
    Finset.mem_singleton, eq_comm]

theorem kernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    kernel H q R v z = 0 := by
  rw [mem_ball] at h
  simp [kernel, h]

theorem kernel_of_mem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∈ ball H v R) :
    kernel H q R v z = q ^ H.dist v z := by
  rw [mem_ball] at h
  simp [kernel, h]

theorem one_le_sum_kernel_sq {q : ℝ} (R : ℕ) (v : W) : 1 ≤ ∑ z, kernel H q R v z ^ 2 :=
  calc (1 : ℝ) = kernel H q R v v ^ 2 := by rw [kernel_self, one_pow]
    _ ≤ ∑ z, kernel H q R v z ^ 2 :=
      Finset.single_le_sum (f := fun z => kernel H q R v z ^ 2) (fun z _ => sq_nonneg _)
        (Finset.mem_univ v)

theorem sum_unitKernel_sq (q : ℝ) (R : ℕ) (v : W) : ∑ z, unitKernel H q R v z ^ 2 = 1 := by
  have hA : 1 ≤ ∑ y, kernel H q R v y ^ 2 := one_le_sum_kernel_sq H R v
  simp only [unitKernel, div_pow, ← Finset.sum_div]
  rw [Real.sq_sqrt (by linarith), div_self (by linarith)]

theorem unitKernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    unitKernel H q R v z = 0 := by
  rw [unitKernel, kernel_eq_zero_of_notMem_ball H h, zero_div]

theorem unitKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) :
    0 ≤ unitKernel H q R v z :=
  div_nonneg (kernel_nonneg H hq R v z) (Real.sqrt_nonneg _)

/-- The unit kernel rows have inner product equal to the kernel inner product divided by
both row norms. -/
theorem sum_unitKernel_mul (q : ℝ) (R : ℕ) (u v : W) :
    ∑ z, unitKernel H q R u z * unitKernel H q R v z =
      (∑ z, kernel H q R u z * kernel H q R v z) /
        (Real.sqrt (∑ z, kernel H q R u z ^ 2) * Real.sqrt (∑ z, kernel H q R v z ^ 2)) := by
  simp only [unitKernel, div_mul_div_comm, ← Finset.sum_div]

variable [DecidableRel H.Adj]

/-- A vertex at positive distance `d + 1` has at most two neighbours at distance `d + 2`. -/
theorem card_filter_neighborFinset_le (degree : ∀ v, H.degree v ≤ 3) {v w : W} {d : ℕ}
    (hw : H.edist v w = (d + 1 : ℕ)) :
    ((H.neighborFinset w).filter fun y => H.edist v y = (d + 1 + 1 : ℕ)).card ≤ 2 := by
  classical
  obtain ⟨p, hpw, hp⟩ := exists_adj_edist_eq H hw
  have hsub : ((H.neighborFinset w).filter fun y => H.edist v y = (d + 1 + 1 : ℕ)) ⊆
      (H.neighborFinset w).erase p := by
    intro y hy
    rw [Finset.mem_filter] at hy
    refine Finset.mem_erase.mpr ⟨?_, hy.1⟩
    rintro rfl
    have := hy.2
    rw [hp] at this
    have : d = d + 1 + 1 := by exact_mod_cast this
    omega
  calc _ ≤ ((H.neighborFinset w).erase p).card := Finset.card_le_card hsub
    _ = H.degree w - 1 := by
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset w p).mpr hpw.symm),
        H.card_neighborFinset_eq_degree]
    _ ≤ 2 := by have := degree w; omega

theorem card_sphere_one_le (degree : ∀ v, H.degree v ≤ 3) (v : W) :
    (sphere H v 1).card ≤ 3 := by
  have hsub : sphere H v 1 ⊆ H.neighborFinset v := by
    intro z hz
    rw [mem_sphere, Nat.cast_one, SimpleGraph.edist_eq_one_iff_adj] at hz
    exact (H.mem_neighborFinset v z).mpr hz
  exact (Finset.card_le_card hsub).trans ((H.card_neighborFinset_eq_degree v).le.trans (degree v))

theorem card_sphere_succ_succ_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (d : ℕ) :
    (sphere H v (d + 1 + 1)).card ≤ 2 * (sphere H v (d + 1)).card := by
  classical
  have hsub : sphere H v (d + 1 + 1) ⊆ (sphere H v (d + 1)).biUnion fun w =>
      (H.neighborFinset w).filter fun y => H.edist v y = (d + 1 + 1 : ℕ) := by
    intro z hz
    rw [mem_sphere] at hz
    obtain ⟨w, hwz, hw⟩ := exists_adj_edist_eq H hz
    rw [Finset.mem_biUnion]
    exact ⟨w, (mem_sphere H).mpr hw,
      Finset.mem_filter.mpr ⟨(H.mem_neighborFinset w z).mpr hwz, hz⟩⟩
  calc (sphere H v (d + 1 + 1)).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ w ∈ sphere H v (d + 1),
        ((H.neighborFinset w).filter fun y => H.edist v y = (d + 1 + 1 : ℕ)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ sphere H v (d + 1), 2 :=
      Finset.sum_le_sum fun w hw =>
        card_filter_neighborFinset_le H degree ((mem_sphere H).mp hw)
    _ = 2 * (sphere H v (d + 1)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_sphere_succ_le (degree : ∀ v, H.degree v ≤ 3) (v : W) :
    ∀ d : ℕ, (sphere H v (d + 1)).card ≤ 3 * 2 ^ d
  | 0 => by simpa using card_sphere_one_le H degree v
  | d + 1 => by
    have h := card_sphere_succ_succ_le H degree v d
    have ih := card_sphere_succ_le degree v d
    rw [pow_succ]
    omega

theorem card_sphere_le (degree : ∀ v, H.degree v ≤ 3) (v : W) :
    ∀ d : ℕ, (sphere H v d).card ≤ 3 * 2 ^ d
  | 0 => by rw [sphere_zero]; simp
  | d + 1 => (card_sphere_succ_le H degree v d).trans (by rw [pow_succ]; omega)

private theorem card_ball_add_le (degree : ∀ v, H.degree v ≤ 3) (v : W) :
    ∀ r : ℕ, (ball H v r).card + 3 ≤ 3 * 2 ^ (r + 1)
  | 0 => by rw [ball_zero]; simp
  | r + 1 => by
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
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (ball H v r) (sphere H v (r + 1))
    have h3 := card_ball_add_le degree v r
    have h4 := card_sphere_le H degree v (r + 1)
    rw [pow_succ 2 (r + 1)]
    omega

theorem card_ball_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (r : ℕ) :
    (ball H v r).card ≤ 3 * 2 ^ (r + 1) := by
  have := card_ball_add_le H degree v r
  omega

/-- **Kernel correlation.** -/
theorem sum_kernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) (q : ℝ) (R : ℕ) {u v : W}
    (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) * ((∑ z, kernel H q R u z ^ 2) + ∑ z, kernel H q R v z ^ 2) / 2 -
        3 * (2 * q ^ 2) ^ R ≤ ∑ z, kernel H q R u z * kernel H q R v z := by
  have hsum : 2 * q / (1 + q ^ 2) *
        ((∑ z, kernel H q R u z ^ 2) + ∑ z, kernel H q R v z ^ 2) / 2 -
        ∑ z, kernel H q R u z * kernel H q R v z =
      ∑ z, (2 * q / (1 + q ^ 2) * (kernel H q R u z ^ 2 + kernel H q R v z ^ 2) / 2 -
        kernel H q R u z * kernel H q R v z) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hle := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => kernel_defect_le H (q := q) R huv z
  have hcount : ∑ z, (q ^ 2) ^ R / 2 *
        ((if H.edist u z = R then (1 : ℝ) else 0) + (if H.edist v z = R then 1 else 0)) =
      (q ^ 2) ^ R / 2 * (((sphere H u R).card : ℝ) + (sphere H v R).card) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
    rfl
  have hu : ((sphere H u R).card : ℝ) ≤ 3 * 2 ^ R := by
    exact_mod_cast card_sphere_le H degree u R
  have hv : ((sphere H v R).card : ℝ) ≤ 3 * 2 ^ R := by
    exact_mod_cast card_sphere_le H degree v R
  have hP : 0 ≤ (q ^ 2) ^ R := by positivity
  have hbound : (q ^ 2) ^ R / 2 * (((sphere H u R).card : ℝ) + (sphere H v R).card) ≤
      3 * (2 * q ^ 2) ^ R := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hu hv) hP]
  linarith

/-- **Unit kernel correlation.** -/
theorem sum_unitKernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ)
    {u v : W} (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ≤
      ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
  rw [sum_unitKernel_mul]
  have hC := sum_kernel_mul_ge H degree q R huv
  have hA := one_le_sum_kernel_sq H (q := q) R u
  have hB := one_le_sum_kernel_sq H (q := q) R v
  generalize ∑ z, kernel H q R u z * kernel H q R v z = C at hC ⊢
  generalize ∑ z, kernel H q R u z ^ 2 = A at hA hC ⊢
  generalize ∑ z, kernel H q R v z ^ 2 = B at hB hC ⊢
  have hκ : 0 ≤ 2 * q / (1 + q ^ 2) := by positivity
  have he : 0 ≤ 3 * (2 * q ^ 2) ^ R := by positivity
  have hs : 1 ≤ Real.sqrt A := Real.one_le_sqrt.mpr hA
  have ht : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt (by linarith)
  have htB : Real.sqrt B ^ 2 = B := Real.sq_sqrt (by linarith)
  have hamgm : 2 * (Real.sqrt A * Real.sqrt B) ≤ A + B := by
    nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B)]
  have h1 : 1 ≤ Real.sqrt A * Real.sqrt B := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hamgm hκ, mul_le_mul_of_nonneg_left h1 he]

end Finite

end Algebraic.Cutwidth.Gaussian.Internal
