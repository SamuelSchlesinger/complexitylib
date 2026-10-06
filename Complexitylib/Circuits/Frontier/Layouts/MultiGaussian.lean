/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.VertexParameters
public import Complexitylib.Circuits.Frontier.Layouts.MultiOrder
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian vertex layouts with parallel edges

The radial kernels use a simple support graph. Events are indexed by multigraph edges,
so their expectations and variances retain multiplicity. Bounded multigraph degree bounds
both dependence overlap and the cost of moving a vertex across a threshold.
-/

@[expose] public section

namespace Complexity.Frontier.Gaussian

open MeasureTheory ProbabilityTheory Finset

variable {W E : Type} [Fintype W] [Fintype E]
  (H : SimpleGraph W) [DecidableRel H.Adj] (G : Multigraph W E)

open Classical in
/-- Edge-event overlap is bounded even with repeated endpoint pairs. -/
theorem multi_edge_overlap_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    (multiDegree : G.MaxDegreeLE d) (adj : ∀ e, H.Adj (G.src e) (G.tgt e))
    (R : ℕ) (e : E) :
    #{l | ¬ Disjoint (edgeSupport H R s(G.src e, G.tgt e))
      (edgeSupport H R s(G.src l, G.tgt l))} ≤ vertexOverlap d R := by
  classical
  have hsupp : edgeSupport H R s(G.src e, G.tgt e) ⊆ ball H (G.src e) (R + 1) := by
    rw [edgeSupport_mk]
    exact union_subset (ball_mono H _ (Nat.le_succ R))
      (ball_subset_ball_of_adj H (adj e) R)
  let near := ball H (G.src e) (2 * R + 1)
  have hsub : ({l | ¬ Disjoint (edgeSupport H R s(G.src e, G.tgt e))
      (edgeSupport H R s(G.src l, G.tgt l))} : Finset E) ⊆
      (G.touching (near : Set W)).toFinset := by
    intro l hl
    obtain ⟨z, hz₁, hz₂⟩ := not_disjoint_iff.mp (mem_filter.mp hl).2
    have close (v : W) (hv : z ∈ ball H v R) : v ∈ near := by
      have := mem_ball_of_not_disjoint H
        (not_disjoint_iff.mpr ⟨z, hsupp hz₁, hv⟩)
      simpa only [show R + 1 + R = 2 * R + 1 by ring] using this
    rw [Set.mem_toFinset]
    rw [edgeSupport_mk, mem_union] at hz₂
    exact hz₂.elim (fun h => Or.inl (close _ h)) (fun h => Or.inr (close _ h))
  calc _ ≤ (G.touching (near : Set W)).toFinset.card := card_le_card hsub
    _ = (G.touching (near : Set W)).ncard := (Set.ncard_eq_toFinset_card' _).symm
    _ ≤ d * near.card := G.ncard_touching_le multiDegree near
    _ ≤ d * d ^ (2 * R + 1 + 1) := Nat.mul_le_mul_left d
        (card_ball_le_degree H hd degree _ _)
    _ = vertexOverlap d R := by unfold vertexOverlap; rw [← pow_succ']

/-- Simultaneous control of all grid cuts, vertex windows, and tails. The sample determines
an actual vertex ordering, with no distinct-score assumption. -/
theorem exists_multi_vertex_sample {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    (multiDegree : G.MaxDegreeLE d) (adj : ∀ e, H.Adj (G.src e) (G.tgt e))
    {q : ℝ} (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ} (hρ0 : -1 < ρ)
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1 : ℕ) * q ^ 2) ^ R)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (M * (d + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t,
      ((G.crossingFinset {v | key v < t}).card : ℝ) ≤
        Real.arccos ρ / Real.pi * Fintype.card E + Fintype.card W *
          (d / T ^ 2 + d * (2 * T / M) / Real.sqrt (2 * Real.pi) + (d + 1) * ε) := by
  classical
  set h : ℝ := (Fintype.card W : ℝ)
  set m : ℝ := (Fintype.card E : ℝ)
  set D : ℝ := (vertexOverlap d R : ℝ)
  set P := gaussPi W
  set δ : ℝ := 2 * T / M
  set c : ℝ := ε * h
  set p : ℝ := Real.arccos ρ / Real.pi
  have hh : 0 < h := lt_of_le_of_lt (by positivity) large
  have hc : 0 < c := mul_pos hε hh
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hp : 0 ≤ p := div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
  have hm : m ≤ d * h := by
    dsimp [m, h]
    have hm' : Fintype.card E ≤ d * Fintype.card W := by
      simpa only [Nat.card_eq_fintype_card] using G.card_edges_le multiDegree
    exact_mod_cast hm'
  let thr (i : ℕ) : ℝ := -T + i * δ
  let cross (i : ℕ) (e : E) := crossingEvent H q R (thr i) s(G.src e, G.tgt e)
  let window (i : ℕ) := vertexEvent H q R (fun x => thr i ≤ x ∧ x < thr i + δ)
  let low := vertexEvent H q R (fun x => x < -T)
  let high := vertexEvent H q R (fun x => T ≤ x)
  let bad : Set (W → ℝ) :=
    ((⋃ i ∈ range M, (deviation univ (cross i) c ∪ deviation univ (window i) c)) ∪
      deviation univ low c) ∪ deviation univ high c
  have crossDev (i : ℕ) : P.real (deviation univ (cross i) c) ≤ m * D / c ^ 2 :=
    pi_deviation_le (fun _ : W => gaussianReal 0 1) univ (cross i)
      (fun e => edgeSupport H R s(G.src e, G.tgt e))
      (fun e _ => measurableSet_crossingEvent H q R (thr i) s(G.src e, G.tgt e))
      (fun e _ => dependsOn_crossingEvent H q R (thr i) s(G.src e, G.tgt e))
      (fun e _ => multi_edge_overlap_le H G hd degree multiDegree adj R e) hc
  have vertexDev {f : ℝ → Prop} (hf : MeasurableSet {x | f x}) :
      P.real (deviation univ (vertexEvent H q R f) c) ≤ h * D / c ^ 2 := by
    have := pi_deviation_le (fun _ : W => gaussianReal 0 1) univ (vertexEvent H q R f)
      (fun v => ball H v R) (fun v _ => measurableSet_vertexEvent H q R hf v)
      (fun v _ => dependsOn_vertexEvent H q R f v)
      (fun v _ => ball_overlap_le H hd degree R v) hc
    simpa only [card_univ, P, deviation, gaussPi, h, D] using this
  have hbad : P.real bad < 1 := by
    have hunion : P.real bad ≤ ∑ _i ∈ range M, (m * D / c ^ 2 + h * D / c ^ 2) +
        h * D / c ^ 2 + h * D / c ^ 2 := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (vertexDev (measurableSet_le measurable_const measurable_id)))
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (vertexDev (measurableSet_lt measurable_id measurable_const)))
      refine (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun i _ => ?_)
      exact (measureReal_union_le _ _).trans (add_le_add (crossDev i)
        (vertexDev ((measurableSet_le measurable_const measurable_id).inter
          (measurableSet_lt measurable_id measurable_const))))
    rw [sum_const, card_range, nsmul_eq_mul] at hunion
    have hm' : m * D / c ^ 2 ≤ d * h * D / c ^ 2 := by gcongr
    have hcalc : (M * (d * h * D / c ^ 2 + h * D / c ^ 2) +
        h * D / c ^ 2 + h * D / c ^ 2) = (M * (d + 1) + 2) * D / ε ^ 2 / h := by
      dsimp [c]; field_simp; ring
    have hlast : (M * (d + 1) + 2) * D / ε ^ 2 / h < 1 := (div_lt_one hh).mpr large
    nlinarith [mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (α := ℝ) M)]
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra! hall
    have : bad = Set.univ := Set.eq_univ_of_forall hall
    rw [this, probReal_univ] at hbad
    exact lt_irrefl _ hbad
  simp only [bad, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  obtain ⟨⟨hmid, hlow⟩, hhigh⟩ := hω
  set score := vertexScore H q R ω
  set B := p * m + h * (d / T ^ 2 + d * δ / Real.sqrt (2 * Real.pi) + (d + 1) * ε)
  have vertexMean {f : ℝ → Prop} {b : ℝ}
      (hb : ∀ v, P.real (vertexEvent H q R f v) ≤ b) :
      ∑ v, P.real (vertexEvent H q R f v) ≤ h * b := by
    exact (sum_le_sum fun v _ => hb v).trans_eq (by simp [h])
  have tailMean (v : W) : P.real (low v) ≤ 1 / T ^ 2 ∧ P.real (high v) ≤ 1 / T ^ 2 :=
    ⟨(measureReal_mono fun ω' hω' => by
      change vertexScore H q R ω' v < -T at hω'
      change T ≤ |vertexScore H q R ω' v|
      rw [abs_of_neg (by linarith)]; linarith).trans
        (gaussPi_tail_le _ (sum_unitKernel_sq H q R v) hT),
    (measureReal_mono fun ω' hω' => by
      change T ≤ vertexScore H q R ω' v at hω'
      exact hω'.trans (le_abs_self _)).trans
        (gaussPi_tail_le _ (sum_unitKernel_sq H q R v) hT)⟩
  have tail (f : ℝ → Prop) [DecidablePred f]
      (hmean : ∀ v, P.real (vertexEvent H q R f v) ≤ 1 / T ^ 2)
      (hdev : ω ∉ deviation univ (vertexEvent H q R f) c) :
      d * (#{v | f (score v)} : ℝ) ≤ B := by
    have hlt := lt_of_notMem_deviation hdev
    have hcount := card_filter_le_sum_indicator univ (vertexEvent H q R f) ω
      (fun v => f (score v)) (fun v _ hv => hv)
    have hmean := vertexMean hmean
    have hbound : (#{v | f (score v)} : ℝ) ≤ h / T ^ 2 + c := by
      convert hcount.trans (hlt.le.trans (add_le_add hmean (le_refl c))) using 1; ring
    have hmult := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (α := ℝ) d)
    have hnonneg : 0 ≤ p * m + h * (d * δ / Real.sqrt (2 * Real.pi) + ε) := by positivity
    have hidentity : B = d * (h / T ^ 2 + c) +
        (p * m + h * (d * δ / Real.sqrt (2 * Real.pi) + ε)) := by dsimp [B, c]; ring
    rw [hidentity]
    linarith
  have crossCount (t : ℝ) : ((G.crossingFinset {v | score v < t}).card : ℝ) ≤
      ∑ e, (crossingEvent H q R t s(G.src e, G.tgt e)).indicator (fun _ => (1 : ℝ)) ω := by
    have heq : G.crossingFinset {v | score v < t} =
        univ.filter (fun e => ω ∈ crossingEvent H q R t s(G.src e, G.tgt e)) := by
      ext e
      simp only [Multigraph.mem_crossingFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      change (¬(score (G.src e) < t ↔ score (G.tgt e) < t)) ↔
        Between t (score (G.src e)) (score (G.tgt e))
      simp only [Between]
      grind
    rw [heq]
    exact card_filter_le_sum_indicator univ
      (fun e => crossingEvent H q R t s(G.src e, G.tgt e)) ω
      (fun e => ω ∈ crossingEvent H q R t s(G.src e, G.tgt e)) (fun _ _ h => h)
  obtain ⟨key, hinj, hcut⟩ := G.exists_key_of_vertexScore multiDegree score hδ M
    (a := -T) (B := B) (tail (· < -T) (fun v => (tailMean v).1) hlow)
    (by
      have htop : -T + M * δ = T := by dsimp [δ]; field_simp; ring
      rw [htop]
      exact tail (T ≤ ·) (fun v => (tailMean v).2) hhigh)
    (by
      intro i hi
      have hiM : i ∈ range M := mem_range.mpr hi
      have hC := lt_of_notMem_deviation (hmid i hiM).1
      have hW := lt_of_notMem_deviation (hmid i hiM).2
      have hCc := crossCount (thr i)
      have hWc := card_filter_le_sum_indicator univ (window i) ω
        (fun v => -T + i * δ ≤ score v ∧ score v < -T + (i + 1) * δ)
        (fun v _ hv => ⟨hv.1, by dsimp [thr]; linarith [hv.2]⟩)
      have hCm : ∑ e ∈ univ, P.real (cross i e) ≤ m * p :=
        (sum_le_sum fun e _ => measureReal_crossingEvent_le H hd degree hq R hρ0 hρ
          (thr i) (SimpleGraph.mem_edgeFinset.mpr (adj e))).trans_eq (by simp [m, p])
      have hWm := vertexMean (f := fun x => thr i ≤ x ∧ x < thr i + δ)
        (b := δ / Real.sqrt (2 * Real.pi))
        (fun v => gaussPi_window_le _ (sum_unitKernel_sq H q R v) (thr i) hδ.le)
      have h1 : ((G.crossingFinset {v | score v < -T + i * δ}).card : ℝ) ≤ m * p + c := by
        linarith
      have h2 : (#{v | -T + i * δ ≤ score v ∧ score v < -T + (i + 1) * δ} : ℝ) ≤
          h * (δ / Real.sqrt (2 * Real.pi)) + c := by linarith
      have hmult := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) d)
      have hnonneg : 0 ≤ h * (d / T ^ 2) := by positivity
      have hidentity : B = (m * p + c) +
          d * (h * (δ / Real.sqrt (2 * Real.pi)) + c) + h * (d / T ^ 2) := by
        dsimp [B, c]; ring
      rw [hidentity]
      linarith)
  exact ⟨key, hinj, hcut⟩

end Complexity.Frontier.Gaussian

namespace Complexity.Frontier.Gaussian

/-- The Gaussian per-edge layout coefficient holds for loopless multigraphs as well. -/
theorem multigraph_vertexLayout_bound {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (W E : Type) [Fintype W] [Fintype E] (G : Multigraph W E),
      G.Loopless → G.MaxDegreeLE d → N₀ < Fintype.card W →
      ∃ key : W → ℕ, Function.Injective key ∧ ∀ t,
        ((G.crossingFinset {v | key v < t}).card : ℝ) ≤
          vertexCoefficient d * Fintype.card E + ξ * Fintype.card W := by
  classical
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by dsimp [D]; exact_mod_cast hd
  set g := vertexCorrelation d
  have hg : 0 < g := vertexCorrelation_pos hd
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (Real.continuous_arccos.continuousAt (x := g)) (Real.pi * ξ / (4 * D)) (by positivity)
  set ρ := g - min η g / 2
  have hmin : 0 < min η g := lt_min hη hg
  have hρg : ρ < g := by dsimp [ρ]; linarith
  have hρ0 : -1 < ρ := by dsimp [ρ]; linarith [min_le_right η g]
  have hcoef : Real.arccos ρ / Real.pi ≤ vertexCoefficient d + ξ / (4 * D) := by
    have hdist : dist ρ g < η := by
      rw [Real.dist_eq, show ρ - g = -(min η g / 2) by dsimp [ρ]; ring,
        abs_neg, abs_of_pos (by positivity)]
      linarith [min_le_left η g]
    have H := (le_abs_self _).trans (hcont hdist).le
    rw [div_le_iff₀ Real.pi_pos]
    dsimp [vertexCoefficient]
    have heq : (Real.arccos g / Real.pi + ξ / (4 * D)) * Real.pi =
        Real.arccos g + Real.pi * ξ / (4 * D) := by field_simp
    rw [show vertexCorrelation d = g from rfl, heq]
    linarith
  obtain ⟨q, R, hq, hcorr⟩ := exists_decay_radius_degree hd hρg
  set T := 1 + 4 * D / ξ
  set ε := ξ / (4 * (D + 1))
  set M : ℕ := ⌈8 * D * T / ξ⌉₊ + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hM : 0 < M := Nat.succ_pos _
  have hMR : 8 * D * T / ξ ≤ (M : ℝ) := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (8 * D * T / ξ)]
  have htail : D / T ^ 2 ≤ ξ / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hT)]
    have hx : 0 ≤ 4 * D / ξ := by positivity
    have hsq : 4 * D / ξ ≤ T ^ 2 := by dsimp [T]; nlinarith [sq_nonneg (4 * D / ξ)]
    have H := mul_le_mul_of_nonneg_left hsq hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at H
    linarith
  have hgrid : D * (2 * T / M) / Real.sqrt (2 * Real.pi) ≤ ξ / 4 := by
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith [Real.two_le_pi])
    have hfrac : D * (2 * T / M) ≤ ξ / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)]
      have H := (div_le_iff₀ hξ).mp hMR
      linarith
    exact (div_le_self (by positivity) hsqrt).trans hfrac
  have herr : D / T ^ 2 + D * (2 * T / M) / Real.sqrt (2 * Real.pi) + (D + 1) * ε ≤
      3 * ξ / 4 := by
    have heq : (D + 1) * ε = ξ / 4 := by dsimp [ε]; field_simp
    linarith
  refine ⟨⌈(M * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2⌉₊,
    fun W E _ _ G hl multiDegree large => ?_⟩
  let H := G.support
  have degree (v : W) : H.degree v ≤ d :=
    (G.support_degree_le v).trans (multiDegree v)
  have hlarge : (M * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨key, hinj, hcut⟩ := exists_multi_vertex_sample H G hd degree multiDegree
    (G.support_src_tgt hl) hq R hρ0 hcorr hT hε hM hlarge
  refine ⟨key, hinj, fun t => (hcut t).trans ?_⟩
  have hE : (Fintype.card E : ℝ) ≤ D * Fintype.card W := by
    dsimp [D]
    have hm : Fintype.card E ≤ d * Fintype.card W := by
      simpa only [Nat.card_eq_fintype_card] using G.card_edges_le multiDegree
    exact_mod_cast hm
  have herror : ξ / (4 * D) * Fintype.card E ≤ ξ / 4 * Fintype.card W := by
    have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ ξ / (4 * D))
    convert h using 1; field_simp
  have h1 := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (Fintype.card E))
  have h2 := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (α := ℝ) (Fintype.card W))
  nlinarith

end Complexity.Frontier.Gaussian
