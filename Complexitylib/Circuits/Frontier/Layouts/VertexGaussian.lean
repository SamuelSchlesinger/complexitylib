/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Gaussian
public import Complexitylib.Circuits.Frontier.Layouts.VertexOrder
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian vertex layouts in bounded degree

Normalize the truncated radial kernel at each vertex, take its Gaussian score, and sort.
Every edge crosses a fixed threshold with probability at most `arccos(ρ) / π`. Local
dependence controls a finite grid of cuts, score windows, and tails simultaneously. The
deterministic ordering lemma then controls all prefixes, including ties.
-/

@[expose] public section

namespace Complexity.Frontier.Gaussian

open MeasureTheory ProbabilityTheory Finset

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- A vertex's unit radial-kernel Gaussian score. -/
noncomputable def vertexScore (q : ℝ) (R : ℕ) (ω : W → ℝ) (v : W) : ℝ :=
  form (unitKernel H q R v) ω

/-- The event that a vertex's score satisfies `p`. -/
def vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) : Set (W → ℝ) :=
  {ω | p (vertexScore H q R ω v)}

/-- The event that the threshold `t` separates the scores of an edge's endpoints. -/
def crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) : Sym2 W → Set (W → ℝ) :=
  Sym2.lift ⟨fun u v => {ω | Between t (vertexScore H q R ω u) (vertexScore H q R ω v)},
    fun _ _ => by ext ω; simp only [Set.mem_ofPred_eq, Between, or_comm]⟩

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_vertexEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (v : W) : MeasurableSet (vertexEvent H q R p v) :=
  measurable_form _ hp

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    MeasurableSet (crossingEvent H q R t e) := by
  induction e using Sym2.ind with
  | _ u v => exact measurableSet_between (measurable_form _) (measurable_form _) t

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem vertexScore_congr (q : ℝ) (R : ℕ) (v : W) {ω ω' : W → ℝ}
    (h : ∀ z ∈ ball H v R, ω z = ω' z) : vertexScore H q R ω v = vertexScore H q R ω' v :=
  form_congr (fun _z hz => unitKernel_eq_zero_of_notMem_ball H hz) h

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem dependsOn_vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) :
    DependsOn (· ∈ vertexEvent H q R p v) (ball H v R : Set W) := by
  intro ω ω' h
  simp only [vertexEvent, Set.mem_ofPred_eq]
  rw [vertexScore_congr H q R v h]

omit [DecidableRel H.Adj] in
theorem dependsOn_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    DependsOn (· ∈ crossingEvent H q R t e) (edgeSupport H R e : Set W) := by
  induction e using Sym2.ind with
  | _ u v =>
  intro ω ω' h
  change (Between t (vertexScore H q R ω u) (vertexScore H q R ω v)) =
    (Between t (vertexScore H q R ω' u) (vertexScore H q R ω' v))
  rw [vertexScore_congr H q R u (fun z hz => h z (mem_union.mpr (Or.inl hz))),
    vertexScore_congr H q R v (fun z hz => h z (mem_union.mpr (Or.inr hz)))]

/-- One overlap bound suffices for both vertex and edge events. -/
def vertexOverlap (d R : ℕ) : ℕ := d ^ (2 * R + 3)

theorem ball_overlap_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d) (R : ℕ) (v : W) :
    #{w | ¬ Disjoint (ball H v R) (ball H w R)} ≤ vertexOverlap d R := by
  calc _ ≤ (ball H v (R + R)).card :=
        card_le_card fun w hw => mem_ball_of_not_disjoint H (mem_filter.mp hw).2
    _ ≤ d ^ (R + R + 1) := card_ball_le_degree H hd degree v (R + R)
    _ ≤ vertexOverlap d R := Nat.pow_le_pow_right (by lia) (by lia)

theorem edge_overlap_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d) (R : ℕ)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    #{l ∈ H.edgeFinset | ¬ Disjoint (edgeSupport H R e) (edgeSupport H R l)} ≤
      vertexOverlap d R := by
  induction e using Sym2.ind with
  | _ u v =>
  have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  have hsupp : edgeSupport H R s(u, v) ⊆ ball H u (R + 1) := by
    rw [edgeSupport_mk]
    exact union_subset (ball_mono H u (Nat.le_succ R)) (ball_subset_ball_of_adj H huv R)
  have hsub : {l ∈ H.edgeFinset | ¬ Disjoint (edgeSupport H R s(u, v)) (edgeSupport H R l)} ⊆
      (ball H u (2 * R + 1)).biUnion (fun c => H.incidenceFinset c) := by
    intro l hl
    obtain ⟨hlE, hdisj⟩ := mem_filter.mp hl
    induction l using Sym2.ind with
    | _ a b =>
    have hab : H.Adj a b := SimpleGraph.mem_edgeFinset.mp hlE
    obtain ⟨z, hz₁, hz₂⟩ := not_disjoint_iff.mp hdisj
    have near (c : W) (hc : z ∈ ball H c R) : c ∈ ball H u (2 * R + 1) := by
      have := mem_ball_of_not_disjoint H
        (not_disjoint_iff.mpr ⟨z, hsupp hz₁, hc⟩)
      rwa [show R + 1 + R = 2 * R + 1 by ring] at this
    rw [edgeSupport_mk, mem_union] at hz₂
    rcases hz₂ with hza | hzb
    · exact mem_biUnion.mpr ⟨a, near a hza, SimpleGraph.mem_incidenceFinset.mpr
        ⟨(SimpleGraph.mem_edgeSet H).mpr hab, by simp⟩⟩
    · exact mem_biUnion.mpr ⟨b, near b hzb, SimpleGraph.mem_incidenceFinset.mpr
        ⟨(SimpleGraph.mem_edgeSet H).mpr hab, by simp⟩⟩
  calc _ ≤ ((ball H u (2 * R + 1)).biUnion fun c => H.incidenceFinset c).card := card_le_card hsub
    _ ≤ d * (ball H u (2 * R + 1)).card := card_incidence_biUnion_le H degree _
    _ ≤ d * d ^ (2 * R + 1 + 1) := Nat.mul_le_mul_left d
        (card_ball_le_degree H hd degree u _)
    _ = vertexOverlap d R := by unfold vertexOverlap; rw [← pow_succ']

omit [DecidableEq W] in
theorem measureReal_crossingEvent_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    {q : ℝ} (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ} (hρ0 : -1 < ρ)
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1 : ℕ) * q ^ 2) ^ R)
    (t : ℝ) {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    (gaussPi W).real (crossingEvent H q R t e) ≤ Real.arccos ρ / Real.pi := by
  induction e using Sym2.ind with
  | _ u v =>
  have hcorr := hρ.trans (sum_unitKernel_mul_ge_degree H hd degree hq R
    (SimpleGraph.mem_edgeFinset.mp he))
  exact (gaussPi_between_le_arccos (sum_unitKernel_sq H q R u) (sum_unitKernel_sq H q R v)
    (hρ0.trans_le hcorr) t).trans (div_le_div_of_nonneg_right
      (Real.arccos_le_arccos hcorr) Real.pi_pos.le)

omit [DecidableEq W] in
/-- A bounded-degree graph has at most `d |V|` edges (the weaker form of handshaking
convenient for the concentration constants). -/
theorem card_edges_le_degree_mul {d : ℕ} (degree : ∀ v, H.degree v ≤ d) :
    H.edgeFinset.card ≤ d * Fintype.card W := by
  have hs := H.sum_degrees_eq_twice_card_edges
  have hb := sum_le_sum (s := univ) (fun v _ => degree v)
  simp only [sum_const, card_univ, smul_eq_mul] at hb
  lia

omit [DecidableEq W] in
/-- Simultaneous control of all grid cuts, vertex windows, and tails. The sample determines
an actual vertex ordering, with no distinct-score assumption. -/
theorem exists_vertex_sample {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    {q : ℝ} (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ} (hρ0 : -1 < ρ)
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1 : ℕ) * q ^ 2) ^ R)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (M * (d + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t,
      ((H.crossingFinset {v | key v < t}).card : ℝ) ≤
        Real.arccos ρ / Real.pi * H.edgeFinset.card + Fintype.card W *
          (d / T ^ 2 + d * (2 * T / M) / Real.sqrt (2 * Real.pi) + (d + 1) * ε) := by
  classical
  set h : ℝ := (Fintype.card W : ℝ)
  set m : ℝ := (H.edgeFinset.card : ℝ)
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
    exact_mod_cast card_edges_le_degree_mul H degree
  let thr (i : ℕ) : ℝ := -T + i * δ
  let cross (i : ℕ) := crossingEvent H q R (thr i)
  let window (i : ℕ) := vertexEvent H q R (fun x => thr i ≤ x ∧ x < thr i + δ)
  let low := vertexEvent H q R (fun x => x < -T)
  let high := vertexEvent H q R (fun x => T ≤ x)
  let bad : Set (W → ℝ) :=
    ((⋃ i ∈ range M, (deviation H.edgeFinset (cross i) c ∪ deviation univ (window i) c)) ∪
      deviation univ low c) ∪ deviation univ high c
  have crossDev (i : ℕ) : P.real (deviation H.edgeFinset (cross i) c) ≤ m * D / c ^ 2 :=
    pi_deviation_le (fun _ : W => gaussianReal 0 1) H.edgeFinset (cross i) (edgeSupport H R)
      (fun e _ => measurableSet_crossingEvent H q R (thr i) e)
      (fun e _ => dependsOn_crossingEvent H q R (thr i) e)
      (fun e he => edge_overlap_le H hd degree R he) hc
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
  have crossCount (t : ℝ) : ((H.crossingFinset {v | score v < t}).card : ℝ) ≤
      ∑ e ∈ H.edgeFinset, (crossingEvent H q R t e).indicator (fun _ => (1 : ℝ)) ω := by
    have heq : H.crossingFinset {v | score v < t} =
        H.edgeFinset.filter (fun e => ω ∈ crossingEvent H q R t e) := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
      simp only [SimpleGraph.mem_crossingFinset_mk, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      change H.Adj u v ∧ _ ↔ H.Adj u v ∧
        Between t (vertexScore H q R ω u) (vertexScore H q R ω v)
      simp only [Finset.mem_univ, true_and, not_lt, Between, score]
    rw [heq]
    exact card_filter_le_sum_indicator H.edgeFinset (crossingEvent H q R t) ω
      (fun e => ω ∈ crossingEvent H q R t e) (fun _ _ h => h)
  obtain ⟨key, hinj, hcut⟩ := exists_key_of_vertexScore H degree score hδ M
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
      have hCm : ∑ e ∈ H.edgeFinset, P.real (cross i e) ≤ m * p :=
        (sum_le_sum fun e he => measureReal_crossingEvent_le H hd degree hq R hρ0 hρ
          (thr i) he).trans_eq (by simp [m, p])
      have hWm := vertexMean (f := fun x => thr i ≤ x ∧ x < thr i + δ)
        (b := δ / Real.sqrt (2 * Real.pi))
        (fun v => gaussPi_window_le _ (sum_unitKernel_sq H q R v) (thr i) hδ.le)
      have h1 : ((H.crossingFinset {v | score v < -T + i * δ}).card : ℝ) ≤ m * p + c := by
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
