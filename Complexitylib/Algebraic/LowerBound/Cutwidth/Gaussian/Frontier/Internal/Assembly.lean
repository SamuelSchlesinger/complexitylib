/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Expectation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Assembly

/-!
# A good sample for the edge-score decomposition

Fix thresholds `-T + i δ` with `δ = 2T / M`. For each threshold count the vertices whose edge
scores straddle it and the edges scoring in the following window, and count the edges in both
tails. Each count is a sum of local events, so it deviates from its mean by `ε h` with
probability `O(1 / h)`. For large cubic graphs some sample keeps all counts near their means,
and the edge-score decomposition of that sample has bags of at most
`h · frontierLayoutBound ρ₀ T ε M` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The bag bound of the edge-score decomposition with the given parameters, per vertex. -/
noncomputable def frontierLayoutBound (ρ₀ T ε : ℝ) (M : ℕ) : ℝ :=
  max (3 / T ^ 2 + 2 * ε)
    (frontierBound ρ₀ + 3 * (2 * T / M) / Real.sqrt (2 * Real.pi) + 3 * ε)

theorem card_filter_eq_sum_indicator' {Ω κ : Type} (F : Finset κ) (A : κ → Set Ω) (ω : Ω) :
    ((F.filter fun k => ω ∈ A k).card : ℝ) = ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : ω ∈ A k <;> simp [h]

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

theorem edgeSupport_subset_ball {R : ℕ} {v : W} {e : Sym2 W} (he : e ∈ H.incidenceFinset v) :
    edgeSupport H R e ⊆ ball H v (R + 1) := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_sep_iff] at he
  obtain ⟨hedge, hv⟩ := he
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
  rw [edgeSupport_mk]
  refine Finset.union_subset (ball_mono H v (Nat.le_succ R)) ?_
  exact ball_subset_ball_of_adj H ((SimpleGraph.mem_edgeSet H).mp hedge) R

omit [DecidableEq W] in
theorem measurableSet_straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) :
    MeasurableSet (straddleEvent H q R t v) := by
  have : straddleEvent H q R t v = ⋃ e ∈ H.incidenceFinset v,
      ({ω | edgeScore H q R ω e < t} ∩ ⋃ e' ∈ H.incidenceFinset v, {ω | t ≤ edgeScore H q R ω e'}) := by
    ext ω
    simp only [straddleEvent, EdgeStraddles, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff, exists_prop]
  rw [this]
  refine Finset.measurableSet_biUnion _ fun e _ => ?_
  exact (measurableSet_lt (measurable_edgeScore H q R e) measurable_const).inter
    (Finset.measurableSet_biUnion _ fun e' _ =>
      measurableSet_le measurable_const (measurable_edgeScore H q R e'))

theorem dependsOn_straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) :
    DependsOn (· ∈ straddleEvent H q R t v) (ball H v (R + 1) : Set W) := by
  intro ω ω' h
  have hscore : ∀ e ∈ H.incidenceFinset v, edgeScore H q R ω e = edgeScore H q R ω' e :=
    fun e he => edgeScore_congr H (edgeSupport_subset_ball H he) fun i hi => h i hi
  simp only [straddleEvent, Set.mem_ofPred_eq, EdgeStraddles]
  apply propext
  constructor
  · rintro ⟨e, he, h1, e', he', h2⟩
    exact ⟨e, he, hscore e he ▸ h1, e', he', hscore e' he' ▸ h2⟩
  · rintro ⟨e, he, h1, e', he', h2⟩
    exact ⟨e, he, (hscore e he).symm ▸ h1, e', he', (hscore e' he').symm ▸ h2⟩

/-- An event about one edge score. -/
def edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) : Set (W → ℝ) :=
  {ω | p (edgeScore H q R ω e)}

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_edgeScoreEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (e : Sym2 W) : MeasurableSet (edgeScoreEvent H q R p e) :=
  measurable_edgeScore H q R e hp

omit [DecidableRel H.Adj] in
theorem dependsOn_edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) :
    DependsOn (· ∈ edgeScoreEvent H q R p e) (edgeSupport H R e : Set W) := by
  intro ω ω' h
  simp only [edgeScoreEvent, Set.mem_ofPred_eq]
  rw [edgeScore_congr H le_rfl fun i hi => h i hi]

omit [DecidableEq W] in
/-- Edge vectors of a graph with large kernel correlations are unit vectors. -/
theorem sum_edgeVector_sq_of_mem (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) : ∑ z, edgeVector H q R e z ^ 2 = 1 := by
  induction e using Sym2.ind with
  | _ u v =>
  have hadj : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  have hcorr := hρ.trans (sum_unitKernel_mul_ge H degree hq0 R hadj)
  exact sum_edgeVector_sq H (by rw [pairNormSq_eq]; linarith)

/-- **A good sample.** For a large cubic graph some Gaussian sample yields an edge-score path
decomposition whose bags have at most `h · frontierLayoutBound ρ₀ T ε M` vertices. -/
theorem exists_good_frontier_sample (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    (R : ℕ) {ρ₀ : ℝ} (hρ₀ : 17 / 32 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 3) * (overlapBound (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ D : PathDecomposition H, ∀ k,
      ((D.bag k).card : ℝ) ≤ Fintype.card W * frontierLayoutBound ρ₀ T ε M := by
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card W : ℝ) with hh
  set P := gaussPi W
  set Dn : ℝ := (overlapBound (R + 1) : ℝ)
  have hDR : (overlapBound R : ℝ) ≤ Dn := by
    unfold Dn overlapBound
    have : 2 ^ (2 * R + 2) ≤ 2 ^ (2 * (R + 1) + 2) := Nat.pow_le_pow_right two_pos (by omega)
    exact_mod_cast Nat.mul_le_mul_left 9 this
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := 2 * T / M with hδ
  have hδpos : 0 < δ := by positivity
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h with hc
  have hcpos : 0 < c := by positivity
  have hE := card_edgeFinset_of_regular H regular
  have hρ₀' : -1 < ρ₀ := by linarith
  have unit := fun {e : Sym2 W} (he : e ∈ H.edgeFinset) =>
    sum_edgeVector_sq_of_mem H degree hq0 hρ₀' hρ he
  -- The thresholds and the four families of events.
  let thr : ℕ → ℝ := fun i => -T + i * δ
  let straddle : ℕ → W → Set (W → ℝ) := fun i => straddleEvent H q R (thr i)
  let window : ℕ → Sym2 W → Set (W → ℝ) := fun i =>
    edgeScoreEvent H q R (fun x => thr i ≤ x ∧ x < thr i + δ)
  let low : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => x < -T)
  let high : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => T ≤ x)
  let bad : Set (W → ℝ) :=
    ((⋃ i ∈ Finset.range M,
      (deviation Finset.univ (straddle i) c ∪ deviation H.edgeFinset (window i) c)) ∪
      deviation H.edgeFinset low c) ∪ deviation H.edgeFinset high c
  -- Deviation probabilities.
  have straddleDev : ∀ i, P.real (deviation Finset.univ (straddle i) c) ≤ h * Dn / c ^ 2 := by
    intro i
    have := pi_deviation_le (fun _ : W => gaussianReal 0 1) Finset.univ (straddle i)
      (fun v => ball H v (R + 1)) (fun v _ => measurableSet_straddleEvent H q R (thr i) v)
      (fun v _ => dependsOn_straddleEvent H q R (thr i) v)
      (fun v _ => card_filter_not_disjoint_ball_le H degree (R + 1) v) hcpos
    rw [Finset.card_univ] at this
    exact this
  have edgeDev : ∀ (A : Sym2 W → Set (W → ℝ)), (∀ e, MeasurableSet (A e)) →
      (∀ e, DependsOn (· ∈ A e) (edgeSupport H R e : Set W)) →
      P.real (deviation H.edgeFinset A c) ≤ H.edgeFinset.card * Dn / c ^ 2 := by
    intro A hA hdep
    refine (pi_deviation_le (fun _ : W => gaussianReal 0 1) H.edgeFinset A (edgeSupport H R)
      (fun e _ => hA e) (fun e _ => hdep e)
      (fun e he => card_filter_not_disjoint_edgeSupport_le H degree R he) hcpos).trans ?_
    gcongr
  have windowDev : ∀ i, P.real (deviation H.edgeFinset (window i) c) ≤
      H.edgeFinset.card * Dn / c ^ 2 := fun i =>
    edgeDev _ (fun e => measurableSet_edgeScoreEvent H q R
      (measurableSet_le measurable_const measurable_id |>.inter
        (measurableSet_lt measurable_id measurable_const)) e)
      (fun e => dependsOn_edgeScoreEvent H q R _ e)
  have lowDev : P.real (deviation H.edgeFinset low c) ≤ H.edgeFinset.card * Dn / c ^ 2 :=
    edgeDev _ (fun e => measurableSet_edgeScoreEvent H q R
      (measurableSet_lt measurable_id measurable_const) e)
      (fun e => dependsOn_edgeScoreEvent H q R _ e)
  have highDev : P.real (deviation H.edgeFinset high c) ≤ H.edgeFinset.card * Dn / c ^ 2 :=
    edgeDev _ (fun e => measurableSet_edgeScoreEvent H q R
      (measurableSet_le measurable_const measurable_id) e)
      (fun e => dependsOn_edgeScoreEvent H q R _ e)
  -- The union bound.
  have hbad : P.real bad < 1 := by
    have hunion : P.real bad ≤ ∑ i ∈ Finset.range M,
        (h * Dn / c ^ 2 + H.edgeFinset.card * Dn / c ^ 2) +
          H.edgeFinset.card * Dn / c ^ 2 + H.edgeFinset.card * Dn / c ^ 2 := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_ highDev)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ lowDev)
      refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact (measureReal_union_le _ _).trans (add_le_add (straddleDev i) (windowDev i))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hE] at hunion
    refine hunion.trans_lt ?_
    have hD : 0 ≤ Dn := by positivity
    have key : (M * (h * Dn / c ^ 2 + 3 / 2 * h * Dn / c ^ 2) + 3 / 2 * h * Dn / c ^ 2 +
        3 / 2 * h * Dn / c ^ 2) = (5 / 2 * M + 3) * Dn / ε ^ 2 / h := by
      rw [hc]
      field_simp
      ring
    rw [key, div_lt_one hhpos]
    calc (5 / 2 * (M : ℝ) + 3) * Dn / ε ^ 2 ≤ (3 * M + 3) * Dn / ε ^ 2 := by
          gcongr
          linarith
      _ < h := large
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra hall
    push Not at hall
    have : bad = Set.univ := Set.eq_univ_of_forall hall
    rw [this, probReal_univ] at hbad
    exact lt_irrefl _ hbad
  simp only [bad, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  obtain ⟨⟨hmid, hlow⟩, hhigh⟩ := hω
  set X := edgeScore H q R ω
  -- Means.
  have straddleMean : ∀ i, ∑ v, P.real (straddle i v) ≤ h * frontierBound ρ₀ := by
    intro i
    calc _ ≤ ∑ _v : W, frontierBound ρ₀ := Finset.sum_le_sum fun v _ =>
          measureReal_straddleEvent_le H regular hq0 hρ₀ hρ (thr i) v
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have windowMean : ∀ i, ∑ e ∈ H.edgeFinset, P.real (window i e) ≤
      H.edgeFinset.card * (δ / Real.sqrt (2 * Real.pi)) := by
    intro i
    calc _ ≤ ∑ _e ∈ H.edgeFinset, δ / Real.sqrt (2 * Real.pi) := Finset.sum_le_sum fun e he =>
          gaussPi_window_le _ (unit he) (thr i) hδpos.le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have lowMean : ∑ e ∈ H.edgeFinset, P.real (low e) ≤ H.edgeFinset.card * (1 / T ^ 2) := by
    calc _ ≤ ∑ _e ∈ H.edgeFinset, 1 / T ^ 2 := Finset.sum_le_sum fun e he => by
          refine (measureReal_mono ?_).trans (gaussPi_tail_le _ (unit he) hT)
          intro ω' hω'
          simp only [low, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
          rw [abs_of_neg (by linarith)]
          linarith
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have highMean : ∑ e ∈ H.edgeFinset, P.real (high e) ≤ H.edgeFinset.card * (1 / T ^ 2) := by
    calc _ ≤ ∑ _e ∈ H.edgeFinset, 1 / T ^ 2 := Finset.sum_le_sum fun e he => by
          refine (measureReal_mono ?_).trans (gaussPi_tail_le _ (unit he) hT)
          intro ω' hω'
          simp only [high, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
          exact hω'.trans (le_abs_self _)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hB1 : h * (3 / T ^ 2 + 2 * ε) ≤ h * frontierLayoutBound ρ₀ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hhpos.le
  have hB2 : h * (frontierBound ρ₀ + 3 * δ / Real.sqrt (2 * Real.pi) + 3 * ε) ≤
      h * frontierLayoutBound ρ₀ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hhpos.le
  have tail : ∀ (A : Sym2 W → Set (W → ℝ)),
      ∑ e ∈ H.edgeFinset, P.real (A e) ≤ H.edgeFinset.card * (1 / T ^ 2) →
      ω ∉ deviation H.edgeFinset A c →
      2 * ((H.edgeFinset.filter fun e => ω ∈ A e).card : ℝ) ≤ h * (3 / T ^ 2 + 2 * ε) := by
    intro A hmean hdev
    have := lt_of_notMem_deviation hdev
    rw [← card_filter_eq_sum_indicator'] at this
    calc 2 * ((H.edgeFinset.filter fun e => ω ∈ A e).card : ℝ)
        ≤ 2 * (H.edgeFinset.card * (1 / T ^ 2) + c) := by linarith
      _ = h * (3 / T ^ 2 + 2 * ε) := by rw [hE, hc]; ring
  obtain ⟨D, hD⟩ := exists_pathDecomposition_of_edgeScore H regular X hδpos M
    (a := -T) (B := h * frontierLayoutBound ρ₀ T ε M)
    ((tail low lowMean hlow).trans hB1)
    (by
      have hT' : -T + M * δ = T := by rw [hδ]; field_simp; ring
      rw [hT']
      exact (tail high highMean hhigh).trans hB1)
    (by
      intro i hi
      have hiM : i ∈ Finset.range M := Finset.mem_range.mpr hi
      have hS := lt_of_notMem_deviation (hmid i hiM).1
      have hW := lt_of_notMem_deviation (hmid i hiM).2
      rw [← card_filter_eq_sum_indicator'] at hS hW
      have hS' : ((Finset.univ.filter fun v => EdgeStraddles H X (-T + i * δ) v).card : ℝ) =
          ((Finset.univ.filter fun v => ω ∈ straddle i v).card : ℝ) := rfl
      have hW' : ((H.edgeFinset.filter fun e =>
          -T + i * δ ≤ X e ∧ X e < -T + (i + 1) * δ).card : ℝ) =
          ((H.edgeFinset.filter fun e => ω ∈ window i e).card : ℝ) := by
        congr 2
        refine Finset.filter_congr fun e _ => ?_
        simp only [window, edgeScoreEvent, Set.mem_ofPred_eq, thr, X]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
      rw [hS', hW']
      calc _ ≤ (h * frontierBound ρ₀ + c) +
            2 * (H.edgeFinset.card * (δ / Real.sqrt (2 * Real.pi)) + c) := by
            gcongr
            · exact hS.le.trans (by linarith [straddleMean i])
            · exact hW.le.trans (by linarith [windowMean i])
        _ = h * (frontierBound ρ₀ + 3 * δ / Real.sqrt (2 * Real.pi) + 3 * ε) := by
            rw [hE, hc]; ring
        _ ≤ _ := hB2)
  exact ⟨D, hD⟩

end Algebraic.Cutwidth.Gaussian.Internal
