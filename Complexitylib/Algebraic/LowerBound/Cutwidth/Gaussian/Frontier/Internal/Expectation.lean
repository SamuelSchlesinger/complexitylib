/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Vector
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Arccos
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Expectation

/-!
# Expected straddling vertices of the edge-score order

A threshold separates two Gaussian edge scores with probability at most `arccos ρ' / π`
(Sheppard's bound), where `ρ'` is the correlation of the edge vectors. The three edge vectors
at a vertex are within correlation `√((1 + ρ₀)/2)` of the vertex row, so the star inequality
bounds their summed angles. A straddling vertex has at least four separated ordered pairs,
so it straddles a threshold with probability at most `(3/(2π)) arccos ((1 + 3ρ₀)/4)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The per-vertex straddling bound for edge correlations at least `ρ₀`. -/
noncomputable def frontierBound (ρ₀ : ℝ) : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ₀) / 4)

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The event that the edge scores at `v` straddle `t`. -/
def straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) : Set (W → ℝ) :=
  {ω | EdgeStraddles H (edgeScore H q R ω) t v}

omit [DecidableEq W] in
/-- The edges at a vertex of a graph whose edges have kernel correlation at least `ρ₀`. -/
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
  refine ⟨sum_edgeVector_sq H hpos, ?_⟩
  rw [sum_edgeVector_mul H hpos]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Straddling probability.** -/
theorem measureReal_straddleEvent_le (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 17 / 32 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : W) :
    (gaussPi W).real (straddleEvent H q R t v) ≤ frontierBound ρ₀ := by
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set κ := Real.sqrt ((1 + ρ₀) / 2) with hκ
  have hκ78 : 7 / 8 ≤ κ := by
    rw [hκ, show (7 / 8 : ℝ) = Real.sqrt ((7 / 8) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hκsq : κ ^ 2 = (1 + ρ₀) / 2 := Real.sq_sqrt (by linarith)
  have star := fun e (he : e ∈ H.incidenceFinset v) =>
    edgeVector_star H degree hq0 (by linarith) hρ v he
  set s := H.incidenceFinset v
  have hs : s.card = 3 := by rw [SimpleGraph.card_incidenceFinset_eq_degree, regular.degree_eq]
  have hxv := sum_unitKernel_sq H q R v
  -- Pairwise correlations are large.
  have pair : ∀ e ∈ s, ∀ e' ∈ s, -1 < ∑ z, edgeVector H q R e z * edgeVector H q R e' z := by
    intro e he e' he'
    have := le_inner_of_le_inner hxv (star e he).1 (star e' he').1 (star e he).2 (star e' he').2
    linarith
  -- Pointwise counting inequality, integrated.
  have hmeas : ∀ e ∈ s, ∀ e' ∈ s, MeasurableSet
      {ω : W → ℝ | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')} := fun e _ e' _ =>
    measurableSet_between (measurable_edgeScore H q R e) (measurable_edgeScore H q R e') t
  have hS : MeasurableSet (straddleEvent H q R t v) := by
    have : straddleEvent H q R t v = ⋃ e ∈ s, ({ω | edgeScore H q R ω e < t} ∩
        ⋃ e' ∈ s, {ω | t ≤ edgeScore H q R ω e'}) := by
      ext ω
      simp only [straddleEvent, EdgeStraddles, s, Set.mem_ofPred_eq, Set.mem_iUnion,
        Set.mem_inter_iff, exists_prop]
    rw [this]
    refine Finset.measurableSet_biUnion _ fun e _ => ?_
    exact (measurableSet_lt (measurable_edgeScore H q R e) measurable_const).inter
      (Finset.measurableSet_biUnion _ fun e' _ =>
        measurableSet_le measurable_const (measurable_edgeScore H q R e'))
  have count : (gaussPi W).real (straddleEvent H q R t v) ≤
      1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
        (gaussPi W).real {ω | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')} := by
    rw [← integral_indicator_one hS]
    have hpt : ∀ ω, (straddleEvent H q R t v).indicator (1 : (W → ℝ) → ℝ) ω ≤
        1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          {ω : W → ℝ | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}.indicator 1 ω := by
      intro ω
      have := indicator_edgeStraddles_le H regular (edgeScore H q R ω) t v
      simp only [Set.indicator_apply, straddleEvent, Set.mem_ofPred_eq, Pi.one_apply]
      exact this
    have hint : ∀ e e', Integrable ({ω : W → ℝ |
        Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}.indicator 1) (gaussPi W) :=
      fun e e' => (integrable_const (1 : ℝ)).indicator
        (measurableSet_between (measurable_edgeScore H q R e) (measurable_edgeScore H q R e') t)
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg
      (fun _ _ => zero_le_one) ω) ?_ (Filter.Eventually.of_forall hpt)).trans_eq ?_
    · exact Integrable.const_mul (integrable_finsetSum _ fun e _ =>
        integrable_finsetSum _ fun e' _ => hint e e') _
    · rw [integral_const_mul, integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun e' _ =>
            integral_indicator_one (measurableSet_between (measurable_edgeScore H q R e)
              (measurable_edgeScore H q R e') t)
        · exact fun e' _ => hint e e'
      · exact fun e _ => integrable_finsetSum _ fun e' _ => hint e e'
  refine count.trans ?_
  -- Each separated pair, then the star inequality.
  have each : ∀ e ∈ s, ∀ e' ∈ s.erase e,
      (gaussPi W).real {ω | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')} ≤
        Real.arccos (∑ z, edgeVector H q R e z * edgeVector H q R e' z) / Real.pi :=
    fun e he e' he' => gaussPi_between_le_arccos (star e he).1
      (star e' (Finset.mem_of_mem_erase he')).1 (pair e he e' (Finset.mem_of_mem_erase he')) t
  have hsum := sum_arccos_star_le hxv s hs (fun e => edgeVector H q R e)
    (fun e he => (star e he).1) hκ78 (fun e he => (star e he).2)
  calc 1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
        (gaussPi W).real {ω | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}
      ≤ 1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          Real.arccos (∑ z, edgeVector H q R e z * edgeVector H q R e' z) / Real.pi := by
        gcongr with e he e' he'
        exact each e he e' he'
    _ = 1 / 4 / Real.pi * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          Real.arccos (∑ z, edgeVector H q R e z * edgeVector H q R e' z) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]; ring
    _ ≤ 1 / 4 / Real.pi * (6 * Real.arccos ((3 * κ ^ 2 - 1) / 2)) := by
        gcongr
    _ = frontierBound ρ₀ := by
        rw [hκsq, frontierBound, show (3 * ((1 + ρ₀) / 2) - 1) / 2 = (1 + 3 * ρ₀) / 4 by ring]
        ring

end Algebraic.Cutwidth.Gaussian.Internal
