/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Kernel
public import Complexitylib.Circuits.Frontier.Layouts.Median
public import Complexitylib.Circuits.Frontier.Layouts.Probability
public import Complexitylib.Circuits.Frontier.Layouts.SecondMoment
public import Complexitylib.Circuits.Frontier.Layouts.Star
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian layouts of cubic graphs

Every large simple cubic graph on `h` vertices has a layout whose prefixes are crossed by at
most `(p + ξ) h` edges, where

`p = (3/(2π)) arccos ((1 + 2√2)/4) ≈ 0.14035`

is `gaussianCoefficient` (`cubicLayoutBound_gaussian`).

**The random layout.** Give each vertex `v` its unit kernel row `x_v` (`Frontier.Gaussian.Kernel`):
the normalized vector of distance weights `q ^ dist(v, z)`, truncated at radius `R`. Give each
edge `uv` the unit vector `y_uv` in the direction of `x_u + x_v`. Draw a standard Gaussian vector
`ω` and score each edge by `⟨y_e, ω⟩`. List the vertices by the median of their three edge
scores (`Frontier.Layouts.Median`).

**One vertex.** A vertex straddles a threshold when two of its edge scores fall on opposite
sides. The three edge vectors at `v` have correlation at least `√((1 + ρ)/2)` with `x_v`, where
`ρ` bounds the correlation of adjacent rows; by Sheppard's bound a pair with correlation `ρ'`
is separated with probability at most `arccos ρ' / π`, and the star inequality
(`Frontier.Gaussian.Star`) bounds the probability that `v` straddles any fixed threshold by
`(3/(2π)) arccos ((1 + 3ρ)/4)` (`measureReal_straddleEvent_le`).

**All thresholds at once.** Each event depends only on the coordinates of `ω` in a ball of
bounded radius, so each count of events has variance `O(h)` and is within `ε h` of its mean
with probability `1 - O(1/h)` (`Frontier.Gaussian.SecondMoment`). For large `h` one sample keeps
the straddling counts at a grid of thresholds, the window counts between them, and the tails
near their means (`exists_good_sample`); the median layout of that sample has every prefix cut
at most `(p_ρ + O(δ) + O(ε) + O(1/T^2)) h`.

**The limit.** As `q` increases to `1/√2` and `R` grows, the adjacent correlation tends to
`2√2/3`, the neighbour correlation of Gaussian waves on the 3-regular tree, and
`(1 + 3 · 2√2/3)/4 = (1 + 2√2)/4`.
-/

@[expose] public section

namespace Complexity.Frontier.Gaussian

open MeasureTheory ProbabilityTheory Finset

/-- The cubic layout coefficient of Gaussian edge scores, `(3/(2π)) arccos ((1 + 2√2)/4)`. -/
noncomputable def gaussianCoefficient : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)

/-! ### Edge vectors and scores -/

section Vectors

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- The squared norm of the sum of two unit kernel rows. -/
noncomputable def pairNormSq (q : ℝ) (R : ℕ) (u v : W) : ℝ :=
  ∑ z, (unitKernel H q R u z + unitKernel H q R v z) ^ 2

theorem pairNormSq_comm (q : ℝ) (R : ℕ) (u v : W) :
    pairNormSq H q R u v = pairNormSq H q R v u := by
  simp only [pairNormSq, add_comm]

theorem pairNormSq_eq (q : ℝ) (R : ℕ) (u v : W) :
    pairNormSq H q R u v = 2 + 2 * ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
  have hu := sum_unitKernel_sq H q R u
  have hv := sum_unitKernel_sq H q R v
  have : ∀ z, (unitKernel H q R u z + unitKernel H q R v z) ^ 2 =
      unitKernel H q R u z ^ 2 + unitKernel H q R v z ^ 2 +
        2 * (unitKernel H q R u z * unitKernel H q R v z) := fun z => by ring
  simp only [pairNormSq, this, sum_add_distrib, ← mul_sum, hu, hv]
  ring

/-- The unit vector of an edge: the normalized sum of the kernel rows of its endpoints. -/
noncomputable def edgeVector (q : ℝ) (R : ℕ) : Sym2 W → W → ℝ :=
  Sym2.lift ⟨fun u v z => (unitKernel H q R u z + unitKernel H q R v z) /
      Real.sqrt (pairNormSq H q R u v), fun u v => by
    funext z
    dsimp only
    rw [add_comm, pairNormSq_comm]⟩

@[simp] theorem edgeVector_mk (q : ℝ) (R : ℕ) (u v z : W) :
    edgeVector H q R s(u, v) z = (unitKernel H q R u z + unitKernel H q R v z) /
      Real.sqrt (pairNormSq H q R u v) := rfl

/-- The Gaussian score of an edge at the sample `ω`. -/
noncomputable def edgeScore (q : ℝ) (R : ℕ) (ω : W → ℝ) (e : Sym2 W) : ℝ :=
  form (edgeVector H q R e) ω

theorem measurable_edgeScore (q : ℝ) (R : ℕ) (e : Sym2 W) :
    Measurable fun ω => edgeScore H q R ω e :=
  measurable_form _

variable {H}

theorem sum_edgeVector_sq {q : ℝ} {R : ℕ} {u v : W} (hpos : 0 < pairNormSq H q R u v) :
    ∑ z, edgeVector H q R s(u, v) z ^ 2 = 1 := by
  simp only [edgeVector_mk, div_pow, ← sum_div]
  rw [Real.sq_sqrt hpos.le]
  exact div_self hpos.ne'

/-- The inner product of an edge vector with the row of an endpoint is `√((1 + ρ)/2)`, where
`ρ` is the correlation of the two endpoint rows. -/
theorem sum_edgeVector_mul {q : ℝ} {R : ℕ} {u v : W} (hpos : 0 < pairNormSq H q R u v) :
    ∑ z, edgeVector H q R s(u, v) z * unitKernel H q R v z =
      Real.sqrt ((1 + ∑ z, unitKernel H q R u z * unitKernel H q R v z) / 2) := by
  set ρ := ∑ z, unitKernel H q R u z * unitKernel H q R v z
  have hsq : pairNormSq H q R u v = 2 * (1 + ρ) := by rw [pairNormSq_eq]; ring
  have hpos' : 0 < 1 + ρ := by linarith
  have hnum : ∑ z, (unitKernel H q R u z + unitKernel H q R v z) * unitKernel H q R v z =
      1 + ρ := by
    have hv := sum_unitKernel_sq H q R v
    simp only [add_mul, sum_add_distrib, ← pow_two, hv]
    ring
  simp only [edgeVector_mk, div_mul_eq_mul_div, ← sum_div, hnum, hsq]
  rw [Real.sqrt_mul (by norm_num), show Real.sqrt ((1 + ρ) / 2) =
      Real.sqrt (1 + ρ) / Real.sqrt 2 from Real.sqrt_div' _ (by norm_num)]
  have h1 : 0 < Real.sqrt (1 + ρ) := Real.sqrt_pos.mpr hpos'
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  field_simp
  rw [Real.sq_sqrt hpos'.le]

end Vectors

/-! ### Locality -/

section Locality

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)

/-- A form depends only on the coordinates where its coefficients are nonzero. -/
theorem form_congr {ι : Type} [Fintype ι] {α : ι → ℝ} {S : Finset ι}
    (hα : ∀ i ∉ S, α i = 0) {ω ω' : ι → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    form α ω = form α ω' := by
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · rw [h i hi]
  · simp [hα i hi]

/-- The coordinates on which the score of an edge depends: the kernel balls of its endpoints. -/
noncomputable def edgeSupport (R : ℕ) : Sym2 W → Finset W :=
  Sym2.lift ⟨fun u v => ball H u R ∪ ball H v R, fun _ _ => union_comm _ _⟩

@[simp] theorem edgeSupport_mk (R : ℕ) (u v : W) :
    edgeSupport H R s(u, v) = ball H u R ∪ ball H v R := rfl

variable {H}

omit [DecidableEq W] in
theorem edgeScore_congr_of_eq_zero {q : ℝ} {R : ℕ} {e : Sym2 W} {S : Finset W}
    (hS : ∀ z ∉ S, edgeVector H q R e z = 0) {ω ω' : W → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    edgeScore H q R ω e = edgeScore H q R ω' e :=
  form_congr hS h

theorem edgeScore_congr {q : ℝ} {R : ℕ} {e : Sym2 W} {S : Finset W}
    (hS : edgeSupport H R e ⊆ S) {ω ω' : W → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    edgeScore H q R ω e = edgeScore H q R ω' e := by
  refine form_congr (S := S) (fun z hz => ?_) h
  induction e using Sym2.ind with
  | _ u v =>
    have hz' : z ∉ edgeSupport H R s(u, v) := fun h => hz (hS h)
    rw [edgeSupport_mk, mem_union, not_or] at hz'
    rw [edgeVector_mk, unitKernel_eq_zero_of_notMem_ball H hz'.1,
      unitKernel_eq_zero_of_notMem_ball H hz'.2, add_zero, zero_div]

variable [DecidableRel H.Adj]

/-- The supports of the edges at `v` lie in the ball of radius `R + 1` around `v`. -/
theorem edgeSupport_subset_ball {R : ℕ} {v : W} {e : Sym2 W} (he : e ∈ H.incidenceFinset v) :
    edgeSupport H R e ⊆ ball H v (R + 1) := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_sep_iff] at he
  obtain ⟨hedge, hv⟩ := he
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
  rw [edgeSupport_mk]
  exact union_subset (ball_mono H v (Nat.le_succ R))
    (ball_subset_ball_of_adj H ((SimpleGraph.mem_edgeSet H).mp hedge) R)

/-- The number of supports that may meet a given one, in a graph of maximum degree three. -/
def overlapBound (R : ℕ) : ℕ := 9 * 2 ^ (2 * R + 2)

/-- Boundedly many edge supports meet that of a given edge. -/
theorem card_filter_not_disjoint_edgeSupport_le (degree : ∀ v, H.degree v ≤ 3) (R : ℕ)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    #{l ∈ H.edgeFinset | ¬ Disjoint (edgeSupport H R e) (edgeSupport H R l)} ≤
      overlapBound R := by
  induction e using Sym2.ind with
  | _ u v =>
  have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  have hsupp : edgeSupport H R s(u, v) ⊆ ball H u (R + 1) := by
    rw [edgeSupport_mk]
    refine union_subset (ball_mono H u (Nat.le_succ R)) (ball_subset_ball_of_adj H huv R)
  have hsub : {l ∈ H.edgeFinset | ¬ Disjoint (edgeSupport H R s(u, v)) (edgeSupport H R l)} ⊆
      (ball H u (2 * R + 1)).biUnion fun c => H.incidenceFinset c := by
    intro l hl
    obtain ⟨hlE, hdisj⟩ := mem_filter.mp hl
    induction l using Sym2.ind with
    | _ a b =>
    have hab : H.Adj a b := SimpleGraph.mem_edgeFinset.mp hlE
    obtain ⟨z, hz₁, hz₂⟩ := not_disjoint_iff.mp hdisj
    have hzu := hsupp hz₁
    rw [edgeSupport_mk, mem_union] at hz₂
    have near : ∀ c, z ∈ ball H c R → c ∈ ball H u (2 * R + 1) := by
      intro c hc
      have := mem_ball_of_not_disjoint H (a := u) (b := c) (r := R + 1) (r' := R)
        (not_disjoint_iff.mpr ⟨z, hzu, hc⟩)
      rwa [show R + 1 + R = 2 * R + 1 by ring] at this
    rw [mem_biUnion]
    rcases hz₂ with hza | hzb
    · exact ⟨a, near a hza, by simpa [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.incidenceSet] using hab⟩
    · exact ⟨b, near b hzb, by simpa [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.incidenceSet] using hab⟩
  calc _ ≤ #((ball H u (2 * R + 1)).biUnion fun c => H.incidenceFinset c) := card_le_card hsub
    _ ≤ ∑ c ∈ ball H u (2 * R + 1), #(H.incidenceFinset c) := card_biUnion_le
    _ ≤ ∑ _c ∈ ball H u (2 * R + 1), 3 := sum_le_sum fun c _ => by
        rw [SimpleGraph.card_incidenceFinset_eq_degree]; exact degree c
    _ = 3 * #(ball H u (2 * R + 1)) := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ 3 * (3 * 2 ^ (2 * R + 1 + 1)) := by gcongr; exact card_ball_le H degree u (2 * R + 1)
    _ = overlapBound R := by unfold overlapBound; ring

/-- Boundedly many balls of radius `R` meet a given one. -/
theorem card_filter_not_disjoint_ball_le (degree : ∀ v, H.degree v ≤ 3) (R : ℕ) (v : W) :
    #{w | ¬ Disjoint (ball H v R) (ball H w R)} ≤ overlapBound R := by
  calc _ ≤ #(ball H v (R + R)) :=
        card_le_card fun w hw => mem_ball_of_not_disjoint H (mem_filter.mp hw).2
    _ ≤ 3 * 2 ^ (R + R + 1) := card_ball_le H degree v (R + R)
    _ ≤ overlapBound R := by
        unfold overlapBound
        have : 2 ^ (R + R + 1) ≤ 2 ^ (2 * R + 2) := Nat.pow_le_pow_right two_pos (by omega)
        omega

end Locality

/-! ### The straddling probability of one vertex -/

section Straddle

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The probability bound for straddling when adjacent kernel rows have correlation at least
`ρ₀`. -/
noncomputable def straddleBound (ρ₀ : ℝ) : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ₀) / 4)

/-- The event that the edge scores at `v` straddle the threshold `t`. -/
def straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) : Set (W → ℝ) :=
  {ω | EdgeStraddles H (edgeScore H q R ω) t v}

noncomputable instance (t x y : ℝ) : Decidable (Between t x y) := by
  unfold Between; infer_instance

variable {H}

omit [DecidableEq W] in
/-- The edge vectors at `v` are unit vectors with correlation at least `√((1 + ρ₀)/2)` with the
row of `v`. -/
theorem edgeVector_star (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q) {R : ℕ}
    {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (v : W) {e : Sym2 W} (he : e ∈ H.incidenceFinset v) :
    ∑ z, edgeVector H q R e z ^ 2 = 1 ∧
      Real.sqrt ((1 + ρ₀) / 2) ≤ ∑ z, edgeVector H q R e z * unitKernel H q R v z := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_sep_iff] at he
  obtain ⟨hedge, hv⟩ := he
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
  have hadj : H.Adj u v := (SimpleGraph.mem_edgeSet H).mp hedge |>.symm
  have hcorr := hρ.trans (sum_unitKernel_mul_ge H degree hq0 R hadj)
  have hpos : 0 < pairNormSq H q R u v := by rw [pairNormSq_eq]; linarith
  rw [Sym2.eq_swap]
  refine ⟨sum_edgeVector_sq hpos, ?_⟩
  rw [sum_edgeVector_mul hpos]
  exact Real.sqrt_le_sqrt (by linarith)

set_option linter.flexible false in
/-- Three reals on both sides of a threshold give four separated ordered pairs. -/
theorem four_le_between_pairs {t p q r : ℝ} (hlt : p < t ∨ q < t ∨ r < t)
    (hge : t ≤ p ∨ t ≤ q ∨ t ≤ r) :
    (4 : ℝ) ≤ ((if Between t p q then 1 else 0) + (if Between t p r then 1 else 0)) +
      (((if Between t q p then 1 else 0) + (if Between t q r then 1 else 0)) +
        ((if Between t r p then 1 else 0) + (if Between t r q then 1 else 0))) := by
  rcases lt_or_ge p t with hp | hp <;> rcases lt_or_ge q t with hq | hq <;>
    rcases lt_or_ge r t with hr | hr <;>
    simp [Between, hp, hq, hr, not_le.mpr, not_lt.mpr] <;> norm_num <;>
    rcases hlt with h | h | h <;> rcases hge with h' | h' | h' <;> linarith

omit [DecidableEq W] in
/-- A straddling vertex of a cubic graph has at least four separated ordered pairs of edges. -/
theorem indicator_edgeStraddles_le [DecidableEq W] (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) (t : ℝ) (v : W) :
    (if EdgeStraddles H score t v then (1 : ℝ) else 0) ≤
      1 / 4 * ∑ e ∈ H.incidenceFinset v, ∑ e' ∈ (H.incidenceFinset v).erase e,
        if Between t (score e) (score e') then (1 : ℝ) else 0 := by
  split_ifs with h
  swap
  · refine mul_nonneg (by norm_num) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => ?_)
    split_ifs <;> norm_num
  obtain ⟨e₁, he₁, h₁, e₂, he₂, h₂⟩ := h
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ :=
    card_eq_three.mp (card_incidenceFinset_of_regular regular v)
  rw [hs] at he₁ he₂ ⊢
  have hlt : score x < t ∨ score y < t ∨ score z < t := by
    simp only [mem_insert, mem_singleton] at he₁
    rcases he₁ with rfl | rfl | rfl <;> simp [h₁]
  have hge : t ≤ score x ∨ t ≤ score y ∨ t ≤ score z := by
    simp only [mem_insert, mem_singleton] at he₂
    rcases he₂ with rfl | rfl | rfl <;> simp [h₂]
  have ex : ({x, y, z} : Finset (Sym2 W)).erase x = {y, z} := by
    ext; simp only [mem_erase, mem_insert, mem_singleton]; grind
  have ey : ({x, y, z} : Finset (Sym2 W)).erase y = {x, z} := by
    ext; simp only [mem_erase, mem_insert, mem_singleton]; grind
  have ez : ({x, y, z} : Finset (Sym2 W)).erase z = {x, y} := by
    ext; simp only [mem_erase, mem_insert, mem_singleton]; grind
  rw [sum_insert (by simp [hxy, hxz]), sum_insert (by simp [hyz]), sum_singleton, ex, ey, ez,
    sum_pair hyz, sum_pair hxz, sum_pair hxy]
  have := four_le_between_pairs hlt hge
  linarith

theorem measurableSet_between {Ω : Type} [MeasurableSpace Ω] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    MeasurableSet {ω | Between t (f ω) (g ω)} := by
  unfold Between
  exact ((measurableSet_lt hf measurable_const).inter (measurableSet_le measurable_const hg)).union
    ((measurableSet_lt hg measurable_const).inter (measurableSet_le measurable_const hf))

omit [DecidableEq W] in
theorem measurableSet_straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) :
    MeasurableSet (straddleEvent H q R t v) := by
  have : straddleEvent H q R t v = ⋃ e ∈ H.incidenceFinset v,
      ({ω | edgeScore H q R ω e < t} ∩
        ⋃ e' ∈ H.incidenceFinset v, {ω | t ≤ edgeScore H q R ω e'}) := by
    ext ω
    simp only [straddleEvent, EdgeStraddles, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff, exists_prop]
  rw [this]
  refine measurableSet_biUnion _ fun e _ => ?_
  exact (measurableSet_lt (measurable_edgeScore H q R e) measurable_const).inter
    (measurableSet_biUnion _ fun e' _ =>
      measurableSet_le measurable_const (measurable_edgeScore H q R e'))

omit [DecidableEq W] in
/-- Whether `v` straddles a threshold depends only on the ball of radius `R + 1` around `v`. -/
theorem dependsOn_straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) :
    DependsOn (· ∈ straddleEvent H q R t v) (ball H v (R + 1) : Set W) := by
  classical
  intro ω ω' h
  have hscore : ∀ e ∈ H.incidenceFinset v, edgeScore H q R ω e = edgeScore H q R ω' e :=
    fun e he => edgeScore_congr (edgeSupport_subset_ball he) fun i hi => h i hi
  simp only [straddleEvent, Set.mem_ofPred_eq, EdgeStraddles]
  apply propext
  constructor
  · rintro ⟨e, he, h1, e', he', h2⟩
    exact ⟨e, he, hscore e he ▸ h1, e', he', hscore e' he' ▸ h2⟩
  · rintro ⟨e, he, h1, e', he', h2⟩
    exact ⟨e, he, (hscore e he).symm ▸ h1, e', he', (hscore e' he').symm ▸ h2⟩

omit [DecidableEq W] in
/-- **Straddling probability.** If adjacent kernel rows have correlation at least `ρ₀ ≥ 17/32`,
a vertex straddles any fixed threshold with probability at most `straddleBound ρ₀`. -/
theorem measureReal_straddleEvent_le (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 17 / 32 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : W) :
    (gaussPi W).real (straddleEvent H q R t v) ≤ straddleBound ρ₀ := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set κ := Real.sqrt ((1 + ρ₀) / 2) with hκ
  have hκ78 : 7 / 8 ≤ κ := by
    rw [hκ, show (7 / 8 : ℝ) = Real.sqrt ((7 / 8) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hκsq : κ ^ 2 = (1 + ρ₀) / 2 := Real.sq_sqrt (by linarith)
  have star := fun e (he : e ∈ H.incidenceFinset v) =>
    edgeVector_star degree hq0 (by linarith) hρ v he
  set s := H.incidenceFinset v
  have hs : #s = 3 := card_incidenceFinset_of_regular regular v
  have hxv := sum_unitKernel_sq H q R v
  -- Pairwise correlations are large.
  have pair : ∀ e ∈ s, ∀ e' ∈ s, -1 < ∑ z, edgeVector H q R e z * edgeVector H q R e' z := by
    intro e he e' he'
    have := le_inner_of_le_inner hxv (star e he).1 (star e' he').1 (star e he).2 (star e' he').2
    linarith
  -- The pointwise counting inequality, integrated.
  have hint : ∀ e e', Integrable ({ω : W → ℝ |
      Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}.indicator 1) (gaussPi W) :=
    fun e e' => (integrable_const (1 : ℝ)).indicator
      (measurableSet_between (measurable_edgeScore H q R e) (measurable_edgeScore H q R e') t)
  have count : (gaussPi W).real (straddleEvent H q R t v) ≤
      1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
        (gaussPi W).real {ω | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')} := by
    rw [← integral_indicator_one (measurableSet_straddleEvent q R t v)]
    have hpt : ∀ ω, (straddleEvent H q R t v).indicator (1 : (W → ℝ) → ℝ) ω ≤
        1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          {ω : W → ℝ | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}.indicator 1 ω := by
      intro ω
      have := indicator_edgeStraddles_le regular (edgeScore H q R ω) t v
      simp only [Set.indicator_apply, straddleEvent, Set.mem_ofPred_eq, Pi.one_apply]
      convert this using 1
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg
      (fun _ _ => zero_le_one) ω) ?_ (Filter.Eventually.of_forall hpt)).trans_eq ?_
    · exact Integrable.const_mul (integrable_finsetSum _ fun e _ =>
        integrable_finsetSum _ fun e' _ => hint e e') _
    · rw [integral_const_mul, integral_finsetSum _ fun e _ =>
        integrable_finsetSum _ fun e' _ => hint e e']
      congr 1
      refine sum_congr rfl fun e _ => ?_
      rw [integral_finsetSum _ fun e' _ => hint e e']
      exact sum_congr rfl fun e' _ => integral_indicator_one (measurableSet_between
        (measurable_edgeScore H q R e) (measurable_edgeScore H q R e') t)
  refine count.trans ?_
  -- Sheppard's bound for each separated pair, then the star inequality.
  have hsum := sum_arccos_star_le hxv s hs (fun e => edgeVector H q R e)
    (fun e he => (star e he).1) hκ78 (fun e he => (star e he).2)
  calc 1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
        (gaussPi W).real {ω | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}
      ≤ 1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          Real.arccos (∑ z, edgeVector H q R e z * edgeVector H q R e' z) / Real.pi := by
        gcongr with e he e' he'
        exact gaussPi_between_le_arccos (star e he).1 (star e' (mem_of_mem_erase he')).1
          (pair e he e' (mem_of_mem_erase he')) t
    _ = 1 / 4 / Real.pi * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          Real.arccos (∑ z, edgeVector H q R e z * edgeVector H q R e' z) := by
        simp only [div_eq_mul_inv, ← sum_mul]; ring
    _ ≤ 1 / 4 / Real.pi * (6 * Real.arccos ((3 * κ ^ 2 - 1) / 2)) := by gcongr
    _ = straddleBound ρ₀ := by
        rw [hκsq, straddleBound, show (3 * ((1 + ρ₀) / 2) - 1) / 2 = (1 + 3 * ρ₀) / 4 by ring]
        ring

end Straddle

/-! ### A good sample -/

section Sample

variable {W : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]

omit [DecidableEq W] in
theorem card_edgeFinset_of_regular (regular : H.IsRegularOfDegree 3) :
    (#H.edgeFinset : ℝ) = 3 / 2 * Fintype.card W := by
  have hsum := H.sum_degrees_eq_twice_card_edges
  simp only [regular.degree_eq, sum_const, card_univ, smul_eq_mul] at hsum
  have : ((Fintype.card W * 3 : ℕ) : ℝ) = ((2 * #H.edgeFinset : ℕ) : ℝ) := by
    exact_mod_cast hsum
  push_cast at this
  linarith

/-- The event that a count of events deviates from its mean by at least `c`. -/
def deviation {κ : Type} (F : Finset κ) (A : κ → Set (W → ℝ)) (c : ℝ) : Set (W → ℝ) :=
  {ω | c ≤ |∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω - ∑ k ∈ F, (gaussPi W).real (A k)|}

omit [DecidableEq W] in
theorem lt_of_notMem_deviation {κ : Type} {F : Finset κ} {A : κ → Set (W → ℝ)} {c : ℝ}
    {ω : W → ℝ} (h : ω ∉ deviation F A c) :
    ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω < ∑ k ∈ F, (gaussPi W).real (A k) + c := by
  simp only [deviation, Set.mem_ofPred_eq, not_le] at h
  linarith [le_abs_self (∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
    ∑ k ∈ F, (gaussPi W).real (A k))]

/-- A count of the elements with a property implying an event is at most the number of
events that occur. -/
theorem card_filter_le_sum_indicator {Ω κ : Type} (F : Finset κ) (A : κ → Set Ω) (ω : Ω)
    (p : κ → Prop) [DecidablePred p] (hp : ∀ k ∈ F, p k → ω ∈ A k) :
    (#(F.filter p) : ℝ) ≤ ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω := by
  rw [card_filter]
  push_cast
  refine sum_le_sum fun k hk => ?_
  split_ifs with h
  · rw [Set.indicator_of_mem (hp k hk h)]
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

variable (H) in
/-- An event about one edge score. -/
def edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) : Set (W → ℝ) :=
  {ω | p (edgeScore H q R ω e)}

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_edgeScoreEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (e : Sym2 W) :
    MeasurableSet (edgeScoreEvent H q R p e) :=
  measurable_edgeScore H q R e hp

omit [DecidableRel H.Adj] in
theorem dependsOn_edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) :
    DependsOn (· ∈ edgeScoreEvent H q R p e) (edgeSupport H R e : Set W) := by
  intro ω ω' h
  simp only [edgeScoreEvent, Set.mem_ofPred_eq]
  rw [edgeScore_congr le_rfl fun i hi => h i hi]

omit [DecidableEq W] in
/-- The edge vectors of a graph with large kernel correlations are unit vectors. -/
theorem sum_edgeVector_sq_of_mem (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) : ∑ z, edgeVector H q R e z ^ 2 = 1 := by
  induction e using Sym2.ind with
  | _ u v =>
  have hcorr := hρ.trans (sum_unitKernel_mul_ge H degree hq0 R (SimpleGraph.mem_edgeFinset.mp he))
  exact sum_edgeVector_sq (by rw [pairNormSq_eq]; linarith)

/-- The prefix-cut bound of the median layout, per vertex, with the given parameters. -/
noncomputable def cubicBound (ρ₀ T ε : ℝ) (M : ℕ) : ℝ :=
  max (9 / (2 * T ^ 2) + 3 * ε)
    (straddleBound ρ₀ + 9 / 2 * (2 * T / M) / Real.sqrt (2 * Real.pi) + 4 * ε)

omit [DecidableEq W] in
/-- **A good sample.** For a large cubic graph some Gaussian sample yields a median layout all
of whose prefixes are crossed by at most `h · cubicBound ρ₀ T ε M` edges. -/
theorem exists_good_sample (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    (R : ℕ) {ρ₀ : ℝ} (hρ₀ : 17 / 32 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 3) * (overlapBound (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
      (#(H.crossingFinset {w | key w < t}) : ℝ) ≤ Fintype.card W * cubicBound ρ₀ T ε M := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card W : ℝ) with hh
  set P := gaussPi W
  set Dn : ℝ := (overlapBound (R + 1) : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := 2 * T / M with hδ
  have hδpos : 0 < δ := by positivity
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h with hc
  have hcpos : 0 < c := by positivity
  have hE := card_edgeFinset_of_regular regular
  have hρ₀' : -1 < ρ₀ := by linarith
  have unit := fun {e : Sym2 W} (he : e ∈ H.edgeFinset) =>
    sum_edgeVector_sq_of_mem degree hq0 hρ₀' hρ he
  -- The thresholds and the four families of events.
  let thr : ℕ → ℝ := fun i => -T + i * δ
  let straddle : ℕ → W → Set (W → ℝ) := fun i => straddleEvent H q R (thr i)
  let window : ℕ → Sym2 W → Set (W → ℝ) := fun i =>
    edgeScoreEvent H q R (fun x => thr i ≤ x ∧ x < thr i + δ)
  let low : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => x < -T)
  let high : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => T ≤ x)
  let bad : Set (W → ℝ) :=
    ((⋃ i ∈ range M,
      (deviation univ (straddle i) c ∪ deviation H.edgeFinset (window i) c)) ∪
      deviation H.edgeFinset low c) ∪ deviation H.edgeFinset high c
  -- Each count deviates from its mean by `c` with probability `O(1/h)`.
  have straddleDev : ∀ i, P.real (deviation univ (straddle i) c) ≤ h * Dn / c ^ 2 := by
    intro i
    have := pi_deviation_le (fun _ : W => gaussianReal 0 1) univ (straddle i)
      (fun v => ball H v (R + 1)) (fun v _ => measurableSet_straddleEvent q R (thr i) v)
      (fun v _ => dependsOn_straddleEvent q R (thr i) v)
      (fun v _ => card_filter_not_disjoint_ball_le degree (R + 1) v) hcpos
    rwa [card_univ] at this
  have edgeDev : ∀ (A : Sym2 W → Set (W → ℝ)), (∀ e, MeasurableSet (A e)) →
      (∀ e, DependsOn (· ∈ A e) (edgeSupport H R e : Set W)) →
      P.real (deviation H.edgeFinset A c) ≤ #H.edgeFinset * Dn / c ^ 2 := by
    intro A hA hdep
    refine (pi_deviation_le (fun _ : W => gaussianReal 0 1) H.edgeFinset A (edgeSupport H R)
      (fun e _ => hA e) (fun e _ => hdep e)
      (fun e he => card_filter_not_disjoint_edgeSupport_le degree R he) hcpos).trans ?_
    have : overlapBound R ≤ overlapBound (R + 1) := by
      unfold overlapBound; exact Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right two_pos (by omega))
    gcongr
    simp only [Dn]
    exact_mod_cast this
  have edgeDev' : ∀ {p : ℝ → Prop}, MeasurableSet {x | p x} →
      P.real (deviation H.edgeFinset (edgeScoreEvent H q R p) c) ≤
        #H.edgeFinset * Dn / c ^ 2 := fun hp =>
    edgeDev _ (fun e => measurableSet_edgeScoreEvent q R hp e)
      (fun e => dependsOn_edgeScoreEvent q R _ e)
  have hbad : P.real bad < 1 := by
    have hunion : P.real bad ≤ ∑ i ∈ range M,
        (h * Dn / c ^ 2 + #H.edgeFinset * Dn / c ^ 2) +
          #H.edgeFinset * Dn / c ^ 2 + #H.edgeFinset * Dn / c ^ 2 := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (edgeDev' (measurableSet_le measurable_const measurable_id)))
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (edgeDev' (measurableSet_lt measurable_id measurable_const)))
      refine (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun i _ => ?_)
      exact (measureReal_union_le _ _).trans (add_le_add (straddleDev i)
        (edgeDev' ((measurableSet_le measurable_const measurable_id).inter
          (measurableSet_lt measurable_id measurable_const))))
    rw [sum_const, card_range, nsmul_eq_mul, hE] at hunion
    refine hunion.trans_lt ?_
    have hD : 0 ≤ Dn := by positivity
    have key : (M * (h * Dn / c ^ 2 + 3 / 2 * h * Dn / c ^ 2) + 3 / 2 * h * Dn / c ^ 2 +
        3 / 2 * h * Dn / c ^ 2) = (5 / 2 * M + 3) * Dn / ε ^ 2 / h := by
      rw [hc]; field_simp; ring
    rw [key, div_lt_one hhpos]
    calc (5 / 2 * (M : ℝ) + 3) * Dn / ε ^ 2 ≤ (3 * M + 3) * Dn / ε ^ 2 := by
          gcongr; linarith
      _ < h := large
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra! hall
    have : bad = Set.univ := Set.eq_univ_of_forall hall
    rw [this, probReal_univ] at hbad
    exact lt_irrefl _ hbad
  simp only [bad, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  obtain ⟨⟨hmid, hlow⟩, hhigh⟩ := hω
  set X := edgeScore H q R ω
  -- The means of the counts.
  have edgeMean : ∀ {p : ℝ → Prop} {b : ℝ}, (∀ e ∈ H.edgeFinset,
      P.real (edgeScoreEvent H q R p e) ≤ b) →
      ∑ e ∈ H.edgeFinset, P.real (edgeScoreEvent H q R p e) ≤ #H.edgeFinset * b :=
    fun hb => (sum_le_sum hb).trans_eq (by rw [sum_const, nsmul_eq_mul])
  have tailMean : ∀ e ∈ H.edgeFinset, P.real (low e) ≤ 1 / T ^ 2 ∧ P.real (high e) ≤ 1 / T ^ 2 :=
    fun e he => ⟨(measureReal_mono fun ω' hω' => by
      simp only [low, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
      rw [abs_of_neg (by linarith)]; linarith).trans (gaussPi_tail_le _ (unit he) hT),
      (measureReal_mono fun ω' hω' => by
      simp only [high, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
      exact hω'.trans (le_abs_self _)).trans (gaussPi_tail_le _ (unit he) hT)⟩
  -- A count below its mean plus `c`, for edges in a tail.
  have tail : ∀ (p : ℝ → Prop) [DecidablePred p],
      (∀ e ∈ H.edgeFinset, P.real (edgeScoreEvent H q R p e) ≤ 1 / T ^ 2) →
      ω ∉ deviation H.edgeFinset (edgeScoreEvent H q R p) c →
      3 * (#{e ∈ H.edgeFinset | p (X e)} : ℝ) ≤ h * (9 / (2 * T ^ 2) + 3 * ε) := by
    intro p _ hmean hdev
    have hlt := lt_of_notMem_deviation hdev
    have hcount := card_filter_le_sum_indicator H.edgeFinset (edgeScoreEvent H q R p) ω
      (fun e => p (X e)) fun e _ hpe => hpe
    have := edgeMean hmean
    calc 3 * (#{e ∈ H.edgeFinset | p (X e)} : ℝ)
        ≤ 3 * (#H.edgeFinset * (1 / T ^ 2) + c) := by linarith
      _ = h * (9 / (2 * T ^ 2) + 3 * ε) := by rw [hE, hc]; field_simp; ring
  have hB1 : h * (9 / (2 * T ^ 2) + 3 * ε) ≤ h * cubicBound ρ₀ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hhpos.le
  have hB2 : h * (straddleBound ρ₀ + 9 / 2 * δ / Real.sqrt (2 * Real.pi) + 4 * ε) ≤
      h * cubicBound ρ₀ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hhpos.le
  obtain ⟨key, hinj, hcut⟩ := exists_key_of_edgeScore regular X hδpos M
    (a := -T) (B := h * cubicBound ρ₀ T ε M)
    ((tail (· < -T) (fun e he => (tailMean e he).1) hlow).trans hB1)
    (by
      have hT' : -T + M * δ = T := by rw [hδ]; field_simp; ring
      rw [hT']
      exact (tail (T ≤ ·) (fun e he => (tailMean e he).2) hhigh).trans hB1)
    (by
      intro i hi
      have hiM : i ∈ range M := mem_range.mpr hi
      have hS := lt_of_notMem_deviation (hmid i hiM).1
      have hW := lt_of_notMem_deviation (hmid i hiM).2
      have hScount := card_filter_le_sum_indicator univ (straddle i) ω
        (fun v => EdgeStraddles H X (-T + i * δ) v) fun v _ hv => hv
      have hWcount := card_filter_le_sum_indicator H.edgeFinset (window i) ω
        (fun e => -T + i * δ ≤ X e ∧ X e < -T + (i + 1) * δ) fun e _ he =>
          ⟨he.1, by simp only [thr]; linarith [he.2]⟩
      have hSmean : ∑ v, P.real (straddle i v) ≤ h * straddleBound ρ₀ :=
        (sum_le_sum fun v _ => measureReal_straddleEvent_le regular hq0 hρ₀ hρ (thr i) v).trans_eq
          (by rw [sum_const, nsmul_eq_mul, card_univ])
      have hWmean := edgeMean (p := fun x => thr i ≤ x ∧ x < thr i + δ)
        (b := δ / Real.sqrt (2 * Real.pi)) fun e he =>
        gaussPi_window_le _ (unit he) (thr i) hδpos.le
      calc (#{v | EdgeStraddles H X (-T + i * δ) v} : ℝ) +
            3 * #{e ∈ H.edgeFinset | -T + i * δ ≤ X e ∧ X e < -T + (i + 1) * δ}
          ≤ (h * straddleBound ρ₀ + c) +
              3 * (#H.edgeFinset * (δ / Real.sqrt (2 * Real.pi)) + c) := by
            gcongr
            · linarith
            · linarith
        _ = h * (straddleBound ρ₀ + 9 / 2 * δ / Real.sqrt (2 * Real.pi) + 4 * ε) := by
            rw [hE, hc]; ring
        _ ≤ _ := hB2)
  exact ⟨key, hinj, fun t => (hcut t).trans_eq (by ring)⟩

end Sample

/-! ### Parameters -/

theorem continuous_correlation : Continuous fun q : ℝ => 2 * q / (1 + q ^ 2) :=
  (continuous_const.mul continuous_id).div (continuous_const.add (continuous_pow 2))
    fun q => by positivity

theorem correlation_limit :
    2 * (Real.sqrt 2 / 2) / (1 + (Real.sqrt 2 / 2) ^ 2) = 2 * Real.sqrt 2 / 3 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, h2]
  field_simp
  ring

/-- **Decay rate and radius.** Every correlation target below `2√2/3` is met by the
truncated kernel for some decay rate `q < 1/√2` and some radius. -/
theorem exists_decay_radius {ρ₀ : ℝ} (hρ₀g : ρ₀ < 2 * Real.sqrt 2 / 3) :
    ∃ (q : ℝ) (R : ℕ), 0 ≤ q ∧ ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by
  set g : ℝ := 2 * Real.sqrt 2 / 3 with hg
  set q₀ : ℝ := Real.sqrt 2 / 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  obtain ⟨δ, hδ, hκ⟩ := Metric.continuousAt_iff.mp continuous_correlation.continuousAt
    ((g - ρ₀) / 2) (by linarith)
  set q := q₀ - min δ q₀ / 2 with hq
  have hminq : 0 < min δ q₀ := lt_min hδ hq₀pos
  have hq0 : 0 ≤ q := by rw [hq]; linarith [min_le_right δ q₀]
  have hqq₀ : q < q₀ := by rw [hq]; linarith
  have hκq : g - (g - ρ₀) / 2 < 2 * q / (1 + q ^ 2) := by
    have hdist : dist q q₀ < δ := by
      rw [Real.dist_eq, hq, abs_of_neg (by linarith)]
      linarith [min_le_left δ q₀]
    have := hκ hdist
    rw [Real.dist_eq, hq₀, correlation_limit, ← hg] at this
    linarith [neg_abs_le (2 * q / (1 + q ^ 2) - g)]
  have hdecay : 2 * q ^ 2 < 1 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : q ^ 2 < q₀ ^ 2 := by gcongr
    rw [hq₀, div_pow, h2] at this
    linarith
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < (g - ρ₀) / 6) hdecay
  exact ⟨q, R, hq0, by linarith⟩

theorem gaussianCoefficient_eq :
    gaussianCoefficient = straddleBound (2 * Real.sqrt 2 / 3) := by
  rw [gaussianCoefficient, straddleBound]
  congr 2
  ring

theorem gaussianCoefficient_ge : 1 / 20 ≤ gaussianCoefficient := by
  have hsqrt : Real.sqrt 2 < 71 / 50 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpi4 := Real.pi_le_four
  have hθ : Real.pi / 30 ≤ Real.arccos ((1 + 2 * Real.sqrt 2) / 4) := by
    have hcos : (1 + 2 * Real.sqrt 2) / 4 ≤ Real.cos (Real.pi / 30) := by
      have := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 30)
      have hsq : (Real.pi / 30) ^ 2 ≤ (4 / 30) ^ 2 := by gcongr
      linarith
    calc Real.pi / 30 = Real.arccos (Real.cos (Real.pi / 30)) :=
          (Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])).symm
      _ ≤ _ := Real.arccos_le_arccos hcos
  unfold gaussianCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

theorem gaussianCoefficient_pos : 0 < gaussianCoefficient :=
  lt_of_lt_of_le (by norm_num) gaussianCoefficient_ge

/-- The circuit coefficient `1 + 1/(2p)` of the cubic coefficient `p`. -/
theorem one_add_inv_two_mul_gaussianCoefficient :
    1 + 1 / (2 * gaussianCoefficient) =
      1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
  have hsqrt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h : 0 < Real.arccos ((1 + 2 * Real.sqrt 2) / 4) := Real.arccos_pos.mpr (by linarith)
  unfold gaussianCoefficient
  congr 1
  field_simp

/-- The layout coefficient `2p` is at most `9/32`. -/
theorem two_mul_gaussianCoefficient_le : 2 * gaussianCoefficient ≤ 9 / 32 := by
  have hlo : (141421 : ℝ) / 100000 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  set θ := 3 * Real.pi / 32 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hθlo : 0.29451 ≤ θ := by rw [hθ]; linarith
  have hθhi : θ ≤ 0.29453 := by rw [hθ]; linarith
  have hcosθ : Real.cos θ ≤ (1 + 2 * Real.sqrt 2) / 4 := by
    have hb := Real.cos_bound (x := θ) (by rw [abs_of_nonneg hθ0]; exact hθ1)
    rw [abs_of_nonneg hθ0] at hb
    have h2 : θ ^ 2 ≥ 0.29451 ^ 2 := by gcongr
    have h4 : θ ^ 4 ≤ 0.29453 ^ 4 := by gcongr
    nlinarith [(abs_sub_le_iff.mp hb).1]
  have harc : Real.arccos ((1 + 2 * Real.sqrt 2) / 4) ≤ θ :=
    (Real.arccos_le_arccos hcosθ).trans_eq
      (Real.arccos_cos hθ0 (by rw [hθ]; linarith [Real.pi_pos]))
  unfold gaussianCoefficient
  rw [hθ] at harc
  have : 2 * (3 / (2 * Real.pi) * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) =
      3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4) / Real.pi := by
    field_simp
  rw [this, div_le_iff₀ Real.pi_pos]
  linarith

/-- **Parameters.** For every positive slack some admissible parameters bring the per-vertex
cut bound within that slack of `gaussianCoefficient`. -/
theorem exists_parameters {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ T ε : ℝ) (M : ℕ), 0 ≤ q ∧ 17 / 32 ≤ ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      cubicBound ρ₀ T ε M ≤ gaussianCoefficient + ξ := by
  set g : ℝ := 2 * Real.sqrt 2 / 3 with hg
  have hsqrt_lo : (7 : ℝ) / 5 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  -- A correlation target `ρ₀ < g` with a nearly optimal straddling bound.
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    ((Real.continuous_arccos.comp (by fun_prop : Continuous fun ρ : ℝ => (1 + 3 * ρ) / 4)
      ).continuousAt (x := g)) (Real.pi * ξ / 6) (by positivity)
  set ρ₀ := g - min η (1 / 4) / 2 with hρ₀
  have hmin : 0 < min η (1 / 4) := lt_min hη (by norm_num)
  have hρ₀g : ρ₀ < g := by rw [hρ₀]; linarith
  have hρ₀low : 17 / 32 ≤ ρ₀ := by rw [hρ₀, hg]; linarith [min_le_right η (1 / 4)]
  have hbound : straddleBound ρ₀ ≤ gaussianCoefficient + ξ / 4 := by
    have hdist : dist ρ₀ g < η := by
      rw [Real.dist_eq, hρ₀, abs_of_neg (by linarith)]
      linarith [min_le_left η (1 / 4)]
    have := hcont hdist
    simp only [Function.comp_apply, Real.dist_eq] at this
    have hle := (le_abs_self _).trans this.le
    rw [straddleBound, gaussianCoefficient_eq, ← hg, straddleBound]
    have hpi : 0 < Real.pi := Real.pi_pos
    calc 3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ₀) / 4)
        ≤ 3 / (2 * Real.pi) * (Real.arccos ((1 + 3 * g) / 4) + Real.pi * ξ / 6) := by
          gcongr; linarith
      _ = 3 / (2 * Real.pi) * Real.arccos ((1 + 3 * g) / 4) + ξ / 4 := by field_simp; ring
  obtain ⟨q, R, hq0, hρ⟩ := exists_decay_radius hρ₀g
  -- The grid and the deviation slack.
  set ε := min (ξ / 12) (1 / 100) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  set M : ℕ := ⌈720 / ξ⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : 720 / ξ ≤ M := by rw [hM]; push_cast; linarith [Nat.le_ceil (720 / ξ)]
  refine ⟨q, R, ρ₀, 20, ε, M, hq0, hρ₀low, hρ, by norm_num, hεpos, hMpos, ?_⟩
  have hcoef := gaussianCoefficient_ge
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  refine max_le ?_ ?_
  · have : ε ≤ 1 / 100 := min_le_right _ _
    linarith
  · have hεξ : ε ≤ ξ / 12 := min_le_left _ _
    have hsqrtpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.two_le_pi])
    have hgrid : 9 / 2 * (2 * 20 / M) / Real.sqrt (2 * Real.pi) ≤ ξ / 4 := by
      rw [div_le_iff₀ (by positivity)]
      calc 9 / 2 * (2 * 20 / (M : ℝ)) = 180 / M := by ring
        _ ≤ ξ / 2 := by
            rw [div_le_iff₀ hMpos']
            have := mul_le_mul_of_nonneg_left hMR hξ.le
            rw [mul_div_cancel₀ _ hξ.ne'] at this
            linarith
        _ ≤ ξ / 4 * Real.sqrt (2 * Real.pi) := by nlinarith
    linarith

/-- **Gaussian layouts of cubic graphs.** For every `ξ > 0`, every sufficiently large simple
cubic graph on `h` vertices has a layout whose prefixes are crossed by at most
`(gaussianCoefficient + ξ) h` edges. -/
theorem cubicLayoutBound_gaussian : CubicLayoutBound gaussianCoefficient := by
  intro ξ hξ
  obtain ⟨q, R, ρ₀, T, ε, M, hq0, hρ₀, hρ, hT, hε, hM, hbound⟩ := exists_parameters hξ
  refine ⟨⌈(3 * M + 3) * (overlapBound (R + 1) : ℝ) / ε ^ 2⌉₊,
    fun W _ _ H _ regular large => ?_⟩
  have large' : (3 * M + 3) * (overlapBound (R + 1) : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨key, hinj, hcut⟩ := exists_good_sample regular hq0 R hρ₀ hρ hT hε hM large'
  refine ⟨key, hinj, fun t => (hcut t).trans ?_⟩
  have hh0 : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hbound hh0]

end Complexity.Frontier.Gaussian
