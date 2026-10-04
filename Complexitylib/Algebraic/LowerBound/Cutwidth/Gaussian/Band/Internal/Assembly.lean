/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Order
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Assembly

/-!
# A good sample for the band-jump decomposition

Fix `0 < c < T`. The band-jump decomposition (`Gaussian.Band.Order`) needs bounds at the
thresholds outside the band `[-c, c)` and, for every block of band edges, on the vertices
straddling `±c` plus the vertices of the block. Take the blocks to be the band clusters.

* Outside the band, a low grid on `[-T, -c]` and a high grid on `[c, T]` with `M` steps each,
  and the two tails, are controlled by second-moment deviations as for the edge-score
  decomposition. Every grid point `t` has `|t| ≥ c`, so its straddling probability is at most
  `exp (-c²/2) · frontierBound ρ₀`.
* The vertices of a block lie in one band cluster. Either that cluster has at most `K`
  vertices, or all of them lie in clusters of more than `K` vertices. If the expected number
  of the latter is at most `η h`, Markov's inequality keeps it below `2 η h` with probability
  at least `1/2`.

For large cubic graphs some sample avoids every bad event, and the bags of its band-jump
decomposition have at most `h · bandLayoutBound ρ₀ c T ε η M + K` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory
open scoped Classical

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-! ### Measurability of the cluster event -/

/-- The graph of the edges of `H` selected by a Boolean mask. -/
def maskGraph (β : Sym2 W → Bool) : SimpleGraph W where
  Adj u v := H.Adj u v ∧ β s(u, v) = true
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun u h => H.ne_of_adj h.1 rfl⟩

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
theorem bandGraph_eq_maskGraph (score : Sym2 W → ℝ) (c : ℝ) :
    bandGraph H score c = maskGraph H (fun e => decide (-c ≤ score e ∧ score e < c)) := by
  ext u v
  simp [bandGraph, maskGraph]

omit [DecidableEq W] [DecidableRel H.Adj] in
/-- The cluster event depends on the sample only through the finitely many band indicators. -/
theorem measurableSet_bigBandEvent (q : ℝ) (R : ℕ) (c : ℝ) (K : ℕ) (v : W) :
    MeasurableSet (bigBandEvent H q R c K v) := by
  set f : (W → ℝ) → Sym2 W → Bool := fun ω e =>
    decide (-c ≤ edgeScore H q R ω e ∧ edgeScore H q R ω e < c) with hf
  have hmeas : Measurable f := by
    refine measurable_pi_iff.mpr fun e => measurable_to_bool ?_
    have : (fun ω => f ω e) ⁻¹' {true} =
        {ω | -c ≤ edgeScore H q R ω e} ∩ {ω | edgeScore H q R ω e < c} := by
      ext ω
      simp [hf]
    rw [this]
    exact (measurableSet_le measurable_const (measurable_edgeScore H q R e)).inter
      (measurableSet_lt (measurable_edgeScore H q R e) measurable_const)
  have : bigBandEvent H q R c K v = f ⁻¹' {β | K < (Finset.univ.filter fun u =>
      (maskGraph H β).Reachable v u).card} := by
    ext ω
    simp only [bigBandEvent, Set.mem_ofPred_eq, Set.mem_preimage, hf]
    rw [bandGraph_eq_maskGraph]
  rw [this]
  exact (Set.to_countable _).measurableSet.preimage hmeas

omit [DecidableRel H.Adj] in
theorem mem_bigBandEvent {q : ℝ} {R : ℕ} {c : ℝ} {K : ℕ} {v : W} {ω : W → ℝ} :
    ω ∈ bigBandEvent H q R c K v ↔
      K < (Finset.univ.filter fun u =>
        (bandGraph H (edgeScore H q R ω) c).Reachable v u).card := by
  simp only [bigBandEvent, Set.mem_ofPred_eq]
  convert Iff.rfl

/-! ### Blocks of band edges -/

/-- The block of an edge: the index of the band cluster of one of its endpoints. -/
noncomputable def bandBlock (score : Sym2 W → ℝ) (c : ℝ) (e : Sym2 W) : ℕ :=
  (Fintype.equivFin (bandGraph H score c).ConnectedComponent
    ((bandGraph H score c).connectedComponentMk (Quot.out e).1) : ℕ)

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
/-- A band edge of `H` at `v` lies in the band cluster of `v`. -/
theorem connectedComponentMk_out_eq {score : Sym2 W → ℝ} {c : ℝ} {e : Sym2 W}
    (he : e ∈ H.edgeSet) (hband : -c ≤ score e ∧ score e < c) {v : W} (hv : v ∈ e) :
    (bandGraph H score c).connectedComponentMk (Quot.out e).1 =
      (bandGraph H score c).connectedComponentMk v := by
  have hout : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e
  rw [← hout] at he hband hv
  have hadj : (bandGraph H score c).Adj (Quot.out e).1 (Quot.out e).2 :=
    ⟨(SimpleGraph.mem_edgeSet H).mp he, hband⟩
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · rfl
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj

/-- Band edges sharing a vertex share a block. -/
theorem bandBlock_eq (score : Sym2 W → ℝ) (c : ℝ) :
    ∀ v, ∀ e ∈ H.incidenceFinset v, ∀ e' ∈ H.incidenceFinset v,
      -c ≤ score e → score e < c → -c ≤ score e' → score e' < c →
        bandBlock H score c e = bandBlock H score c e' := by
  intro v e he e' he' h₁ h₂ h₁' h₂'
  rw [SimpleGraph.mem_incidenceFinset] at he he'
  unfold bandBlock
  rw [connectedComponentMk_out_eq H he.1 ⟨h₁, h₂⟩ he.2,
    connectedComponentMk_out_eq H he'.1 ⟨h₁', h₂'⟩ he'.2]

/-- **Vertices of a block.** The vertices touching the band edges of one block lie in one
band cluster, so they number at most `K` or lie in clusters of more than `K` vertices. -/
theorem card_filter_bandBlock_le (score : Sym2 W → ℝ) (c : ℝ) (K j : ℕ) :
    ((Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧
        bandBlock H score c e = j).card : ℝ) ≤
      K + ((Finset.univ.filter fun v => K < (Finset.univ.filter fun u =>
        (bandGraph H score c).Reachable v u).card).card : ℝ) := by
  set G := bandGraph H score c
  set S := Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧
    score e < c ∧ bandBlock H score c e = j
  set Big := Finset.univ.filter fun v => K < (Finset.univ.filter fun u => G.Reachable v u).card
  -- Any two vertices of the block are joined in the band graph.
  have joined : ∀ v ∈ S, ∀ w ∈ S, G.Reachable v w := by
    intro v hv w hw
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset]
      at hv hw
    obtain ⟨e, he, hve, h₁, h₂, hej⟩ := hv
    obtain ⟨e', he', hwe', h₁', h₂', hej'⟩ := hw
    have hblock : bandBlock H score c e = bandBlock H score c e' := hej.trans hej'.symm
    unfold bandBlock at hblock
    rw [connectedComponentMk_out_eq H he ⟨h₁, h₂⟩ hve,
      connectedComponentMk_out_eq H he' ⟨h₁', h₂'⟩ hwe'] at hblock
    exact SimpleGraph.ConnectedComponent.eq.mp
      ((Fintype.equivFin _).injective (Fin.val_injective hblock))
  have hS : S.card ≤ max K Big.card := by
    rcases S.eq_empty_or_nonempty with h | ⟨v₀, hv₀⟩
    · rw [h, Finset.card_empty]
      exact Nat.zero_le _
    have hsub : S ⊆ Finset.univ.filter fun u => G.Reachable v₀ u := fun w hw =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, joined v₀ hv₀ w hw⟩
    by_cases hsmall : (Finset.univ.filter fun u => G.Reachable v₀ u).card ≤ K
    · exact ((Finset.card_le_card hsub).trans hsmall).trans (le_max_left _ _)
    · refine (Finset.card_le_card fun w hw => ?_).trans (le_max_right _ _)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hreach : (Finset.univ.filter fun u => G.Reachable w u) =
          Finset.univ.filter fun u => G.Reachable v₀ u := by
        refine Finset.filter_congr fun u _ => ?_
        have h := joined v₀ hv₀ w hw
        exact ⟨fun hwu => h.trans hwu, fun hvu => h.symm.trans hvu⟩
      rw [hreach]
      exact not_le.mp hsmall
  have : (S.card : ℝ) ≤ max (K : ℝ) Big.card := by exact_mod_cast hS
  exact this.trans (max_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
    (le_add_of_nonneg_left (Nat.cast_nonneg _)))

/-! ### Markov's inequality for a count of events -/

/-- If the expected number of events is at most `m > 0`, at least `2 m` of them occur with
probability at most `1/2`. -/
theorem measureReal_two_mul_le_sum_indicator_le {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ F, MeasurableSet (A i)) {m : ℝ} (hm : 0 < m)
    (hsum : ∑ i ∈ F, μ.real (A i) ≤ m) :
    μ.real {ω | 2 * m ≤ ∑ i ∈ F, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤ 1 / 2 := by
  have hint : ∀ i ∈ F, Integrable ((A i).indicator (fun _ => (1 : ℝ))) μ :=
    fun i hi => (integrable_const (1 : ℝ)).indicator (hA i hi)
  have markov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω => ∑ i ∈ F, (A i).indicator (fun _ => (1 : ℝ)) ω)
    (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun i _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (integrable_finsetSum _ hint) (2 * m)
  rw [integral_finsetSum _ hint] at markov
  have hmean : ∑ i ∈ F, ∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ =
      ∑ i ∈ F, μ.real (A i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [integral_indicator_const _ (hA i hi), smul_eq_mul, mul_one]
  rw [hmean] at markov
  have hP := measureReal_nonneg (μ := μ) (s := {ω | 2 * m ≤ ∑ i ∈ F,
    (A i).indicator (fun _ => (1 : ℝ)) ω})
  nlinarith

/-! ### The good sample -/

/-- The bag bound of the band-jump decomposition with the given parameters, per vertex, before
the additive cluster size `K`. -/
noncomputable def bandLayoutBound (ρ₀ c T ε η : ℝ) (M : ℕ) : ℝ :=
  max (3 / T ^ 2 + 2 * ε)
    (Real.exp (-(c ^ 2) / 2) * frontierBound ρ₀ + 3 * ((T - c) / M) / Real.sqrt (2 * Real.pi) +
      3 * ε + 2 * η)

theorem frontierBound_nonneg (ρ₀ : ℝ) : 0 ≤ frontierBound ρ₀ := by
  unfold frontierBound
  have := Real.arccos_nonneg ((1 + 3 * ρ₀) / 4)
  have := Real.pi_pos
  positivity

/-- **A good sample.** If the expected number of vertices in band clusters of more than `K`
vertices is at most `η h`, a large cubic graph has a band-jump path decomposition whose bags
have at most `h · bandLayoutBound ρ₀ c T ε η M + K` vertices. -/
theorem exists_good_band_sample (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    (R : ℕ) {ρ₀ : ℝ} (hρ₀ : 17 / 32 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {c T ε η : ℝ} (hc : 0 < c)
    (hcT : c < T) (hε : 0 < ε) (hη : 0 < η) {M : ℕ} (hM : 0 < M) {K : ℕ}
    (hK : ∑ v, (gaussPi W).real (bigBandEvent H q R c K v) ≤ η * Fintype.card W)
    (large : (10 * M + 10) * (overlapBound (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ D : PathDecomposition H, ∀ k,
      ((D.bag k).card : ℝ) ≤ Fintype.card W * bandLayoutBound ρ₀ c T ε η M + K := by
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card W : ℝ) with hh
  set P := gaussPi W
  set Dn : ℝ := (overlapBound (R + 1) : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hT : 0 < T := hc.trans hcT
  set δ : ℝ := (T - c) / M with hδ
  have hδpos : 0 < δ := div_pos (by linarith) hMpos
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set s : ℝ := ε * h with hs
  have hspos : 0 < s := by positivity
  have hE := card_edgeFinset_of_regular H regular
  have unit := fun {e : Sym2 W} (he : e ∈ H.edgeFinset) =>
    sum_edgeVector_sq_of_mem H degree hq0 (by linarith : -1 < ρ₀) hρ he
  set decay : ℝ := Real.exp (-(c ^ 2) / 2) * frontierBound ρ₀ with hdecay
  -- The events.
  let window : ℝ → Sym2 W → Set (W → ℝ) := fun t =>
    edgeScoreEvent H q R (fun x => t ≤ x ∧ x < t + δ)
  let grid : ℝ → Set (W → ℝ) := fun a => ⋃ i ∈ Finset.range M,
    (deviation Finset.univ (straddleEvent H q R (a + i * δ)) s ∪
      deviation H.edgeFinset (window (a + i * δ)) s)
  let low : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => x < -T)
  let high : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => T ≤ x)
  let big : W → Set (W → ℝ) := bigBandEvent H q R c K
  let markov : Set (W → ℝ) :=
    {ω | 2 * (η * h) ≤ ∑ v ∈ Finset.univ, (big v).indicator (fun _ => (1 : ℝ)) ω}
  let bad : Set (W → ℝ) :=
    ((((grid (-T) ∪ grid c) ∪ deviation Finset.univ (straddleEvent H q R (-c)) s) ∪
      deviation H.edgeFinset low s) ∪ deviation H.edgeFinset high s) ∪ markov
  -- Deviation probabilities.
  have straddleDev : ∀ t, P.real (deviation Finset.univ (straddleEvent H q R t) s) ≤
      h * Dn / s ^ 2 := by
    intro t
    have := pi_deviation_le (fun _ : W => gaussianReal 0 1) Finset.univ (straddleEvent H q R t)
      (fun v => ball H v (R + 1)) (fun v _ => measurableSet_straddleEvent H q R t v)
      (fun v _ => dependsOn_straddleEvent H q R t v)
      (fun v _ => card_filter_not_disjoint_ball_le H degree (R + 1) v) hspos
    rw [Finset.card_univ] at this
    exact this
  have hDR : (overlapBound R : ℝ) ≤ Dn := by
    unfold Dn overlapBound
    have : 2 ^ (2 * R + 2) ≤ 2 ^ (2 * (R + 1) + 2) := Nat.pow_le_pow_right two_pos (by omega)
    exact_mod_cast Nat.mul_le_mul_left 9 this
  have edgeDev : ∀ (A : Sym2 W → Set (W → ℝ)), (∀ e, MeasurableSet (A e)) →
      (∀ e, DependsOn (· ∈ A e) (edgeSupport H R e : Set W)) →
      P.real (deviation H.edgeFinset A s) ≤ H.edgeFinset.card * Dn / s ^ 2 := by
    intro A hA hdep
    refine (pi_deviation_le (fun _ : W => gaussianReal 0 1) H.edgeFinset A (edgeSupport H R)
      (fun e _ => hA e) (fun e _ => hdep e)
      (fun e he => card_filter_not_disjoint_edgeSupport_le H degree R he) hspos).trans ?_
    gcongr
  have windowDev : ∀ t, P.real (deviation H.edgeFinset (window t) s) ≤
      H.edgeFinset.card * Dn / s ^ 2 := fun t =>
    edgeDev _ (fun e => measurableSet_edgeScoreEvent H q R
      (measurableSet_le measurable_const measurable_id |>.inter
        (measurableSet_lt measurable_id measurable_const)) e)
      (fun e => dependsOn_edgeScoreEvent H q R _ e)
  have lowDev : P.real (deviation H.edgeFinset low s) ≤ H.edgeFinset.card * Dn / s ^ 2 :=
    edgeDev _ (fun e => measurableSet_edgeScoreEvent H q R
      (measurableSet_lt measurable_id measurable_const) e)
      (fun e => dependsOn_edgeScoreEvent H q R _ e)
  have highDev : P.real (deviation H.edgeFinset high s) ≤ H.edgeFinset.card * Dn / s ^ 2 :=
    edgeDev _ (fun e => measurableSet_edgeScoreEvent H q R
      (measurableSet_le measurable_const measurable_id) e)
      (fun e => dependsOn_edgeScoreEvent H q R _ e)
  have gridDev : ∀ a, P.real (grid a) ≤
      M * (h * Dn / s ^ 2 + H.edgeFinset.card * Dn / s ^ 2) := by
    intro a
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc _ ≤ ∑ _i ∈ Finset.range M, (h * Dn / s ^ 2 + H.edgeFinset.card * Dn / s ^ 2) :=
          Finset.sum_le_sum fun i _ =>
            (measureReal_union_le _ _).trans (add_le_add (straddleDev _) (windowDev _))
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have markovP : P.real markov ≤ 1 / 2 :=
    measureReal_two_mul_le_sum_indicator_le Finset.univ big
      (fun v _ => measurableSet_bigBandEvent H q R c K v) (by positivity) hK
  -- The union bound.
  have hbad : P.real bad < 1 := by
    have hunion : P.real bad ≤ (M * (h * Dn / s ^ 2 + H.edgeFinset.card * Dn / s ^ 2) +
        M * (h * Dn / s ^ 2 + H.edgeFinset.card * Dn / s ^ 2) + h * Dn / s ^ 2 +
        H.edgeFinset.card * Dn / s ^ 2 + H.edgeFinset.card * Dn / s ^ 2) + 1 / 2 := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_ markovP)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ highDev)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ lowDev)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ (straddleDev _))
      exact (measureReal_union_le _ _).trans (add_le_add (gridDev _) (gridDev _))
    rw [hE] at hunion
    refine hunion.trans_lt ?_
    have key : M * (h * Dn / s ^ 2 + 3 / 2 * h * Dn / s ^ 2) +
        M * (h * Dn / s ^ 2 + 3 / 2 * h * Dn / s ^ 2) + h * Dn / s ^ 2 +
        3 / 2 * h * Dn / s ^ 2 + 3 / 2 * h * Dn / s ^ 2 = (5 * M + 4) * (Dn / ε ^ 2) / h := by
      rw [hs]
      field_simp
      ring
    rw [key]
    have hX : 0 ≤ Dn / ε ^ 2 := by positivity
    have hlarge : (10 * M + 10) * (Dn / ε ^ 2) < h := by
      rw [← mul_div_assoc]
      exact large
    have : (5 * M + 4) * (Dn / ε ^ 2) / h < 1 / 2 := by
      rw [div_lt_iff₀ hhpos]
      nlinarith
    linarith
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra hall
    push Not at hall
    have : bad = Set.univ := Set.eq_univ_of_forall hall
    rw [this, probReal_univ] at hbad
    exact lt_irrefl _ hbad
  simp only [bad, Set.mem_union, not_or] at hω
  obtain ⟨⟨⟨⟨⟨hgridL, hgridH⟩, hmidS⟩, hlow⟩, hhigh⟩, hmark⟩ := hω
  set X := edgeScore H q R ω
  set B : ℝ := h * bandLayoutBound ρ₀ c T ε η M + K with hB
  -- Means.
  have straddleMean : ∀ t, c ^ 2 ≤ t ^ 2 → ∑ v, P.real (straddleEvent H q R t v) ≤ h * decay := by
    intro t ht
    have hexp : Real.exp (-(t ^ 2) / 2) ≤ Real.exp (-(c ^ 2) / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    calc _ ≤ ∑ _v : W, decay := Finset.sum_le_sum fun v _ =>
          (measureReal_straddleEvent_le_exp H regular hq0 hρ₀ hρ t v).trans
            (mul_le_mul_of_nonneg_right hexp (frontierBound_nonneg ρ₀))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have windowMean : ∀ t, ∑ e ∈ H.edgeFinset, P.real (window t e) ≤
      H.edgeFinset.card * (δ / Real.sqrt (2 * Real.pi)) := by
    intro t
    calc _ ≤ ∑ _e ∈ H.edgeFinset, δ / Real.sqrt (2 * Real.pi) := Finset.sum_le_sum fun e he =>
          gaussPi_window_le _ (unit he) t hδpos.le
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
  -- The bag bound dominates each count.
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hB1 : h * (3 / T ^ 2 + 2 * ε) ≤ B := by
    have := mul_le_mul_of_nonneg_left (le_max_left (3 / T ^ 2 + 2 * ε)
      (decay + 3 * δ / Real.sqrt (2 * Real.pi) + 3 * ε + 2 * η)) hhpos.le
    rw [hB, bandLayoutBound]
    linarith
  have hB2 : h * (decay + 3 * δ / Real.sqrt (2 * Real.pi) + 3 * ε + 2 * η) + K ≤ B := by
    have := mul_le_mul_of_nonneg_left (le_max_right (3 / T ^ 2 + 2 * ε)
      (decay + 3 * δ / Real.sqrt (2 * Real.pi) + 3 * ε + 2 * η)) hhpos.le
    rw [hB, bandLayoutBound]
    linarith
  have hgridpos : 0 ≤ 3 * δ / Real.sqrt (2 * Real.pi) := by positivity
  -- Good counts.
  have tail : ∀ (A : Sym2 W → Set (W → ℝ)),
      ∑ e ∈ H.edgeFinset, P.real (A e) ≤ H.edgeFinset.card * (1 / T ^ 2) →
      ω ∉ deviation H.edgeFinset A s →
      2 * ((H.edgeFinset.filter fun e => ω ∈ A e).card : ℝ) ≤ h * (3 / T ^ 2 + 2 * ε) := by
    intro A hmean hdev
    have := lt_of_notMem_deviation hdev
    rw [← card_filter_eq_sum_indicator'] at this
    calc 2 * ((H.edgeFinset.filter fun e => ω ∈ A e).card : ℝ)
        ≤ 2 * (H.edgeFinset.card * (1 / T ^ 2) + s) := by linarith
      _ = h * (3 / T ^ 2 + 2 * ε) := by rw [hE, hs]; ring
  have straddleGood : ∀ t, c ^ 2 ≤ t ^ 2 →
      ω ∉ deviation Finset.univ (straddleEvent H q R t) s →
      ((Finset.univ.filter fun v => EdgeStraddles H X t v).card : ℝ) < h * decay + s := by
    intro t ht hdev
    have hS := lt_of_notMem_deviation hdev
    rw [← card_filter_eq_sum_indicator'] at hS
    exact hS.trans_le (by linarith [straddleMean t ht])
  have gridGood : ∀ a, ω ∉ grid a → (∀ i < M, c ^ 2 ≤ (a + i * δ) ^ 2) → ∀ i < M,
      ((Finset.univ.filter fun v => EdgeStraddles H X (a + i * δ) v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e =>
          a + i * δ ≤ X e ∧ X e < a + (i + 1) * δ).card : ℝ) ≤ B := by
    intro a ha hsq i hi
    have hiM : i ∈ Finset.range M := Finset.mem_range.mpr hi
    simp only [grid, Set.mem_iUnion, Set.mem_union, not_exists, not_or] at ha
    obtain ⟨hS, hW⟩ := ha i hiM
    have hS := straddleGood _ (hsq i hi) hS
    have hW := lt_of_notMem_deviation hW
    rw [← card_filter_eq_sum_indicator'] at hW
    have hW' : ((H.edgeFinset.filter fun e =>
        a + i * δ ≤ X e ∧ X e < a + (i + 1) * δ).card : ℝ) =
        ((H.edgeFinset.filter fun e => ω ∈ window (a + i * δ) e).card : ℝ) := by
      congr 2
      refine Finset.filter_congr fun e _ => ?_
      simp only [window, edgeScoreEvent, Set.mem_ofPred_eq, X]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
    rw [hW']
    calc _ ≤ (h * decay + s) + 2 * (H.edgeFinset.card * (δ / Real.sqrt (2 * Real.pi)) + s) := by
          gcongr
          exact hW.le.trans (by linarith [windowMean (a + i * δ)])
      _ = h * (decay + 3 * δ / Real.sqrt (2 * Real.pi) + 3 * ε) := by rw [hE, hs]; ring
      _ ≤ B := by linarith [mul_nonneg hhpos.le hη.le]
  -- Clusters.
  have hN : ((Finset.univ.filter fun v => K < (Finset.univ.filter fun u =>
      (bandGraph H X c).Reachable v u).card).card : ℝ) < 2 * (η * h) := by
    simp only [markov, Set.mem_ofPred_eq, not_le] at hmark
    rw [← card_filter_eq_sum_indicator'] at hmark
    refine lt_of_eq_of_lt ?_ hmark
    congr 2
    exact Finset.filter_congr fun v _ => (mem_bigBandEvent H).symm
  have lowCount : ((H.edgeFinset.filter fun e => X e < -T).card : ℝ) =
      ((H.edgeFinset.filter fun e => ω ∈ low e).card : ℝ) := by
    congr 2
  have highCount : ((H.edgeFinset.filter fun e => T ≤ X e).card : ℝ) =
      ((H.edgeFinset.filter fun e => ω ∈ high e).card : ℝ) := by
    congr 2
  have hMc : -T + M * δ = -c := by
    rw [hδ]
    field_simp
    ring
  have hTc : c + M * δ = T := by
    rw [hδ]
    field_simp
    ring
  obtain ⟨D, hD⟩ := Gaussian.exists_pathDecomposition_of_bandJump H regular X hc
    (bandBlock H X c) (bandBlock_eq H X c) (B := B)
    (fun t ht => Gaussian.card_filter_edgeScore_le_of_grids H X hδpos hδpos M M
      (a₁ := -T) (a₂ := c) hMc.ge le_rfl
      (by rw [lowCount]; exact (tail low lowMean hlow).trans hB1)
      (by rw [hTc, highCount]; exact (tail high highMean hhigh).trans hB1)
      (gridGood (-T) hgridL fun i hi => by
        have hi' : (i : ℝ) ≤ M := by exact_mod_cast hi.le
        have hiδ : (i : ℝ) * δ ≤ M * δ := mul_le_mul_of_nonneg_right hi' hδpos.le
        have ht : c ≤ -(-T + i * δ) := by linarith
        calc c ^ 2 ≤ (-(-T + i * δ)) ^ 2 := pow_le_pow_left₀ hc.le ht 2
          _ = (-T + i * δ) ^ 2 := neg_sq _)
      (gridGood c hgridH fun i _ => by
        have : 0 ≤ (i : ℝ) * δ := by positivity
        exact pow_le_pow_left₀ hc.le (by linarith) 2)
      t ht)
    (fun j => by
      have hblk := card_filter_bandBlock_le H X c K j
      have hSm := straddleGood (-c) (by rw [neg_sq]) hmidS
      have hSp : ((Finset.univ.filter fun v => EdgeStraddles H X c v).card : ℝ) <
          h * decay + s := by
        simp only [grid, Set.mem_iUnion, Set.mem_union, not_exists, not_or] at hgridH
        have := straddleGood (c + ((0 : ℕ) : ℝ) * δ) (by simp) (hgridH 0
          (Finset.mem_range.mpr hM)).1
        simpa using this
      constructor <;>
        linarith [mul_nonneg hhpos.le hgridpos, mul_nonneg hhpos.le hε.le])
  exact ⟨D, fun k => (hD k).trans_eq (by rw [hB])⟩

end Algebraic.Cutwidth.Gaussian.Internal
