/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Expectation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Grid

/-!
# A good Gaussian sample

Fix thresholds `-T + i δ` with `δ = 2T / M`. For each threshold count the separated
edges and the scores in the following window, and count both tails. Each count deviates
from its mean by at least `ε h` with probability `O(1 / h)` by the second-moment bound,
so for large cubic graphs some sample keeps all `2M + 2` counts within `ε h` of their
means. The grid bound then controls every prefix of that sample's score order.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory

/-- The per-vertex prefix-cut bound of the layout with the given parameters. -/
noncomputable def layoutBound (ρ₀ T ε : ℝ) (M : ℕ) : ℝ :=
  max (3 / T ^ 2 + 3 * ε)
    (3 / 2 * crossBound ρ₀ + 4 * ε + 3 * (2 * T / M) / Real.sqrt (2 * Real.pi))

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_scoreEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (v : W) : MeasurableSet (scoreEvent H q R p v) :=
  Gaussian.measurable_form (unitKernel H q R v) hp

omit [DecidableEq W] in
theorem card_edgeFinset_of_regular (regular : H.IsRegularOfDegree 3) :
    (H.edgeFinset.card : ℝ) = 3 / 2 * Fintype.card W := by
  have hsum := H.sum_degrees_eq_twice_card_edges
  simp only [regular.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have : ((Fintype.card W * 3 : ℕ) : ℝ) = ((2 * H.edgeFinset.card : ℕ) : ℝ) := by
    exact_mod_cast hsum
  push_cast at this
  linarith

/-- The deviation event of a count of local events. -/
def deviation {κ : Type} (F : Finset κ) (A : κ → Set (W → ℝ)) (c : ℝ) : Set (W → ℝ) :=
  {ω | c ≤ |∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
    ∑ k ∈ F, (gaussPi W).real (A k)|}

omit [DecidableEq W] in
theorem lt_of_notMem_deviation {κ : Type} {F : Finset κ} {A : κ → Set (W → ℝ)} {c : ℝ}
    {ω : W → ℝ} (h : ω ∉ deviation F A c) :
    ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω < ∑ k ∈ F, (gaussPi W).real (A k) + c := by
  simp only [deviation, Set.mem_ofPred_eq, not_le] at h
  linarith [le_abs_self (∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
    ∑ k ∈ F, (gaussPi W).real (A k))]

/-- **A good sample.** For a large cubic graph some Gaussian sample orders the vertices so
that every prefix cut is at most `h · layoutBound ρ₀ T ε M`. -/
theorem exists_good_sample (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    (R : ℕ) {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 2) * (overlapBound R : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ ω : W → ℝ, ∀ t : ℕ,
      ((H.cutFinset (Finset.univ.filter fun w => scoreKey (score H q R ω) w < t)).card : ℝ) ≤
        Fintype.card W * layoutBound ρ₀ T ε M := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card W : ℝ) with hh
  set P := gaussPi W
  set Dn : ℝ := (overlapBound R : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := 2 * T / M with hδ
  have hδpos : 0 < δ := by positivity
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h with hc
  have hcpos : 0 < c := by positivity
  have hE := card_edgeFinset_of_regular H regular
  -- The thresholds and the four families of events.
  let thr : ℕ → ℝ := fun i => -T + i * δ
  let cross : ℕ → Sym2 W → Set (W → ℝ) := fun i => crossEvent H q R (thr i)
  let window : ℕ → W → Set (W → ℝ) := fun i => windowEvent H q R (thr i) δ
  let low : W → Set (W → ℝ) := scoreEvent H q R (fun x => x < -T)
  let high : W → Set (W → ℝ) := scoreEvent H q R (fun x => T ≤ x)
  let bad : Set (W → ℝ) :=
    ((⋃ i ∈ Finset.range M,
      (deviation H.edgeFinset (cross i) c ∪ deviation Finset.univ (window i) c)) ∪
      deviation Finset.univ low c) ∪ deviation Finset.univ high c
  -- Deviation probabilities.
  have edgeDev : ∀ i, P.real (deviation H.edgeFinset (cross i) c) ≤
      H.edgeFinset.card * Dn / c ^ 2 := fun i =>
    pi_deviation_le (fun _ => gaussianReal 0 1) H.edgeFinset (cross i) (edgeSupport H R)
      (fun e _ => measurableSet_crossEvent H q R (thr i) e)
      (fun e _ => dependsOn_crossEvent H q R (thr i) e)
      (fun e he => card_filter_not_disjoint_edgeSupport_le H degree R he) hcpos
  have vertexDev : ∀ (A : W → Set (W → ℝ)), (∀ v, MeasurableSet (A v)) →
      (∀ v, DependsOn (· ∈ A v) (ball H v R : Set W)) →
      P.real (deviation Finset.univ A c) ≤ h * Dn / c ^ 2 := by
    intro A hA hdep
    have := pi_deviation_le (fun _ : W => gaussianReal 0 1) Finset.univ A
      (fun v => ball H v R) (fun v _ => hA v) (fun v _ => hdep v)
      (fun v _ => card_filter_not_disjoint_ball_le H degree R v) hcpos
    rw [Finset.card_univ] at this
    exact this
  have windowDev : ∀ i, P.real (deviation Finset.univ (window i) c) ≤ h * Dn / c ^ 2 :=
    fun i => vertexDev _ (fun v => measurableSet_scoreEvent H q R
      (measurableSet_le measurable_const measurable_id |>.inter
        (measurableSet_lt measurable_id measurable_const)) v)
      (fun v => dependsOn_scoreEvent H q R _ v)
  have lowDev : P.real (deviation Finset.univ low c) ≤ h * Dn / c ^ 2 :=
    vertexDev _ (fun v => measurableSet_scoreEvent H q R
      (measurableSet_lt measurable_id measurable_const) v)
      (fun v => dependsOn_scoreEvent H q R _ v)
  have highDev : P.real (deviation Finset.univ high c) ≤ h * Dn / c ^ 2 :=
    vertexDev _ (fun v => measurableSet_scoreEvent H q R
      (measurableSet_le measurable_const measurable_id) v)
      (fun v => dependsOn_scoreEvent H q R _ v)
  -- The union bound.
  have hbad : P.real bad < 1 := by
    have hunion : P.real bad ≤ ∑ i ∈ Finset.range M,
        (H.edgeFinset.card * Dn / c ^ 2 + h * Dn / c ^ 2) + h * Dn / c ^ 2 +
          h * Dn / c ^ 2 := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_ highDev)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ lowDev)
      refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact (measureReal_union_le _ _).trans (add_le_add (edgeDev i) (windowDev i))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hE] at hunion
    refine hunion.trans_lt ?_
    have hD : 0 ≤ Dn := by positivity
    have key : (M * (3 / 2 * h * Dn / c ^ 2 + h * Dn / c ^ 2) + h * Dn / c ^ 2 +
        h * Dn / c ^ 2) = (5 / 2 * M + 2) * Dn / ε ^ 2 / h := by
      rw [hc]
      field_simp
      ring
    rw [key, div_lt_one hhpos]
    calc (5 / 2 * (M : ℝ) + 2) * Dn / ε ^ 2 ≤ (3 * M + 2) * Dn / ε ^ 2 := by
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
  refine ⟨ω, fun t => ?_⟩
  set X := score H q R ω
  -- Means.
  have crossMean : ∀ i, ∑ e ∈ H.edgeFinset, P.real (cross i e) ≤
      H.edgeFinset.card * crossBound ρ₀ := by
    intro i
    calc _ ≤ ∑ _e ∈ H.edgeFinset, crossBound ρ₀ := Finset.sum_le_sum fun e he =>
          measureReal_crossEvent_le H degree hq0 hρ₀ hρ (thr i) he
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have windowMean : ∀ i, ∑ v, P.real (window i v) ≤ h * (δ / Real.sqrt (2 * Real.pi)) := by
    intro i
    calc _ ≤ ∑ _v : W, δ / Real.sqrt (2 * Real.pi) := Finset.sum_le_sum fun v _ =>
          measureReal_windowEvent_le H q R (thr i) hδpos.le v
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have lowMean : ∑ v, P.real (low v) ≤ h * (1 / T ^ 2) := by
    calc _ ≤ ∑ _v : W, 1 / T ^ 2 := Finset.sum_le_sum fun v _ =>
          measureReal_lowEvent_le H q R hT v
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have highMean : ∑ v, P.real (high v) ≤ h * (1 / T ^ 2) := by
    calc _ ≤ ∑ _v : W, 1 / T ^ 2 := Finset.sum_le_sum fun v _ =>
          measureReal_highEvent_le H q R hT v
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hB1 : h * (3 / T ^ 2 + 3 * ε) ≤ h * layoutBound ρ₀ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hhpos.le
  have hB2 : h * (3 / 2 * crossBound ρ₀ + 4 * ε + 3 * δ / Real.sqrt (2 * Real.pi)) ≤
      h * layoutBound ρ₀ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hhpos.le
  apply card_cutFinset_scoreKey_le H degree X hδpos M (a := -T)
  · -- The lower tail.
    have hcount := card_filter_eq_sum_indicator H q R (fun x => x < -T) ω
    have := lt_of_notMem_deviation hlow
    rw [← hcount] at this
    calc 3 * ((Finset.univ.filter fun v => X v < -T).card : ℝ)
        ≤ 3 * (h * (1 / T ^ 2) + c) := by
          gcongr
          exact this.le.trans (by linarith)
      _ = h * (3 / T ^ 2 + 3 * ε) := by rw [hc]; ring
      _ ≤ _ := hB1
  · -- The upper tail.
    have hT' : -T + M * δ = T := by rw [hδ]; field_simp; ring
    rw [hT']
    have hcount := card_filter_eq_sum_indicator H q R (fun x => T ≤ x) ω
    have := lt_of_notMem_deviation hhigh
    rw [← hcount] at this
    calc 3 * ((Finset.univ.filter fun v => T ≤ X v).card : ℝ)
        ≤ 3 * (h * (1 / T ^ 2) + c) := by
          gcongr
          exact this.le.trans (by linarith)
      _ = h * (3 / T ^ 2 + 3 * ε) := by rw [hc]; ring
      _ ≤ _ := hB1
  · -- A threshold and its window.
    intro i hi
    have hiM : i ∈ Finset.range M := Finset.mem_range.mpr hi
    have hcut := card_cutFinset_eq_sum_indicator H q R (thr i) ω
    have hC := lt_of_notMem_deviation ((hmid i hiM).1)
    have hwin : ((Finset.univ.filter fun v => -T + i * δ ≤ X v ∧ X v < -T + (i + 1) * δ).card :
        ℝ) = ∑ v, (window i v).indicator (fun _ => (1 : ℝ)) ω := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      have hiff : (-T + i * δ ≤ X v ∧ X v < -T + (i + 1) * δ) ↔
          (-T + i * δ ≤ X v ∧ X v < -T + i * δ + δ) := by
        constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
      simp only [window, windowEvent, scoreEvent, thr, Set.indicator_apply, Set.mem_ofPred_eq,
        hiff, X]
    have hN := lt_of_notMem_deviation ((hmid i hiM).2)
    calc ((H.cutFinset (Finset.univ.filter fun v => X v < -T + i * δ)).card : ℝ) +
          3 * ((Finset.univ.filter fun v => -T + i * δ ≤ X v ∧
            X v < -T + (i + 1) * δ).card : ℝ)
        ≤ (H.edgeFinset.card * crossBound ρ₀ + c) +
            3 * (h * (δ / Real.sqrt (2 * Real.pi)) + c) := by
          rw [hwin]
          have hcut' : ((H.cutFinset (Finset.univ.filter fun v => X v < -T + i * δ)).card : ℝ)
              = ∑ e ∈ H.edgeFinset, (cross i e).indicator (fun _ => (1 : ℝ)) ω := hcut
          rw [hcut']
          gcongr
          · exact hC.le.trans (by linarith [crossMean i])
          · exact hN.le.trans (by linarith [windowMean i])
      _ = h * (3 / 2 * crossBound ρ₀ + 4 * ε + 3 * δ / Real.sqrt (2 * Real.pi)) := by
          rw [hE, hc]; ring
      _ ≤ _ := hB2

end Algebraic.Cutwidth.Gaussian.Internal
