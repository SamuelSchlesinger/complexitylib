/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Kernel
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.SecondMoment
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# Locality of the Gaussian scores

The score of a vertex is a Gaussian form in the coordinates of its kernel ball. Hence the
event that a threshold separates the endpoints of an edge depends only on the union of
the endpoint balls, and each such union meets the unions of boundedly many edges. The same
holds for events about a single score.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The Gaussian score of a vertex at a sample point. -/
noncomputable def score (q : ℝ) (R : ℕ) (ω : W → ℝ) (v : W) : ℝ :=
  form (unitKernel H q R v) ω

theorem form_congr {ι : Type} [Fintype ι] {α : ι → ℝ} {S : Finset ι}
    (hα : ∀ i ∉ S, α i = 0) {ω ω' : ι → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    form α ω = form α ω' := by
  unfold form
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · rw [h i hi]
  · simp [hα i hi]

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem score_congr {q : ℝ} {R : ℕ} {v : W} {S : Finset W} (hS : ball H v R ⊆ S)
    {ω ω' : W → ℝ} (h : ∀ i ∈ S, ω i = ω' i) : score H q R ω v = score H q R ω' v :=
  form_congr (S := S) (fun _ hi => unitKernel_eq_zero_of_notMem_ball H fun hb => hi (hS hb)) h

theorem between_comm {t x y : ℝ} : Between t x y ↔ Between t y x := by
  unfold Between
  tauto

theorem measurableSet_between {Ω : Type} [MeasurableSpace Ω] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    MeasurableSet {ω | Between t (f ω) (g ω)} := by
  unfold Between
  exact ((measurableSet_lt hf measurable_const).inter (measurableSet_le measurable_const hg)).union
    ((measurableSet_lt hg measurable_const).inter (measurableSet_le measurable_const hf))

/-- A threshold separates the scores of the two endpoints of an edge. -/
def Crosses (t : ℝ) (X : W → ℝ) : Sym2 W → Prop :=
  Sym2.lift ⟨fun u v => Between t (X u) (X v), fun _ _ => propext between_comm⟩

omit [Fintype W] [DecidableEq W] in
@[simp] theorem crosses_mk {t : ℝ} {X : W → ℝ} {u v : W} :
    Crosses t X s(u, v) ↔ Between t (X u) (X v) := Iff.rfl

omit [DecidableRel H.Adj] [DecidableEq W] in
/-- The cut of a threshold set consists of the edges the threshold separates. -/
theorem mem_cutFinset_filter_lt_iff (X : W → ℝ) (t : ℝ) (e : Sym2 W) :
    e ∈ H.cutFinset (Finset.univ.filter fun v => X v < t) ↔
      e ∈ H.edgeSet ∧ Crosses t X e := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_cutFinset_mk, SimpleGraph.mem_edgeSet, crosses_mk]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Between]

/-- The coordinates on which the crossing event of an edge depends. -/
noncomputable def edgeSupport (R : ℕ) : Sym2 W → Finset W :=
  Sym2.lift ⟨fun u v => ball H u R ∪ ball H v R, fun _ _ => Finset.union_comm _ _⟩

omit [DecidableRel H.Adj] in
@[simp] theorem edgeSupport_mk (R : ℕ) (u v : W) :
    edgeSupport H R s(u, v) = ball H u R ∪ ball H v R := rfl

/-- The crossing event of an edge. -/
def crossEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) : Set (W → ℝ) :=
  {ω | Crosses t (score H q R ω) e}

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_crossEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    MeasurableSet (crossEvent H q R t e) := by
  induction e using Sym2.ind with
  | _ u v =>
    exact measurableSet_between (Gaussian.measurable_form _) (Gaussian.measurable_form _) t

omit [DecidableRel H.Adj] in
theorem dependsOn_crossEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    DependsOn (· ∈ crossEvent H q R t e) (edgeSupport H R e : Set W) := by
  induction e using Sym2.ind with
  | _ u v =>
    intro ω ω' h
    simp only [crossEvent, Set.mem_ofPred_eq, crosses_mk]
    rw [score_congr H Finset.subset_union_left h, score_congr H Finset.subset_union_right h]

/-- An event about one score. -/
def scoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) : Set (W → ℝ) :=
  {ω | p (score H q R ω v)}

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem dependsOn_scoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) :
    DependsOn (· ∈ scoreEvent H q R p v) (ball H v R : Set W) := by
  intro ω ω' h
  simp only [scoreEvent, Set.mem_ofPred_eq]
  rw [score_congr H le_rfl h]

/-- The overlap constant for supports of radius `R`. -/
def overlapBound (R : ℕ) : ℕ := 9 * 2 ^ (2 * R + 2)

/-- The crossing-event supports of boundedly many edges meet that of a given edge. -/
theorem card_filter_not_disjoint_edgeSupport_le (degree : ∀ v, H.degree v ≤ 3) (R : ℕ)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    (H.edgeFinset.filter fun l => ¬ Disjoint (edgeSupport H R e) (edgeSupport H R l)).card ≤
      overlapBound R := by
  induction e using Sym2.ind with
  | _ u v =>
  have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  have hsupp : edgeSupport H R s(u, v) ⊆ ball H u (R + 1) := by
    rw [edgeSupport_mk]
    refine Finset.union_subset ?_ (ball_subset_ball_of_adj H huv R)
    intro z hz
    rw [mem_ball] at hz ⊢
    exact hz.trans (by exact_mod_cast Nat.le_succ R)
  have hsub : (H.edgeFinset.filter fun l =>
      ¬ Disjoint (edgeSupport H R s(u, v)) (edgeSupport H R l)) ⊆
      (ball H u (2 * R + 1)).biUnion fun c => H.incidenceFinset c := by
    intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨hlE, hdisj⟩ := hl
    induction l using Sym2.ind with
    | _ a b =>
    have hab : H.Adj a b := SimpleGraph.mem_edgeFinset.mp hlE
    obtain ⟨z, hz₁, hz₂⟩ := Finset.not_disjoint_iff.mp hdisj
    have hzu := hsupp hz₁
    rw [edgeSupport_mk, Finset.mem_union] at hz₂
    have near : ∀ c, z ∈ ball H c R → c ∈ ball H u (2 * R + 1) := by
      intro c hc
      have := mem_ball_of_not_disjoint H (a := u) (b := c) (r := R + 1) (r' := R)
        (Finset.not_disjoint_iff.mpr ⟨z, hzu, hc⟩)
      rwa [show R + 1 + R = 2 * R + 1 by ring] at this
    rw [Finset.mem_biUnion]
    rcases hz₂ with hza | hzb
    · exact ⟨a, near a hza, by simpa [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.incidenceSet] using hab⟩
    · exact ⟨b, near b hzb, by simpa [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.incidenceSet] using hab⟩
  calc _ ≤ ((ball H u (2 * R + 1)).biUnion fun c => H.incidenceFinset c).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ c ∈ ball H u (2 * R + 1), (H.incidenceFinset c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ ball H u (2 * R + 1), 3 := Finset.sum_le_sum fun c _ => by
        rw [SimpleGraph.card_incidenceFinset_eq_degree]; exact degree c
    _ = 3 * (ball H u (2 * R + 1)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 3 * (3 * 2 ^ (2 * R + 1 + 1)) := by
        gcongr; exact card_ball_le H degree u (2 * R + 1)
    _ = overlapBound R := by unfold overlapBound; ring

/-- The score-event supports of boundedly many vertices meet that of a given vertex. -/
theorem card_filter_not_disjoint_ball_le (degree : ∀ v, H.degree v ≤ 3) (R : ℕ) (v : W) :
    (Finset.univ.filter fun w => ¬ Disjoint (ball H v R) (ball H w R)).card ≤
      overlapBound R := by
  have hsub : (Finset.univ.filter fun w => ¬ Disjoint (ball H v R) (ball H w R)) ⊆
      ball H v (R + R) := by
    intro w hw
    exact mem_ball_of_not_disjoint H (Finset.mem_filter.mp hw).2
  calc _ ≤ (ball H v (R + R)).card := Finset.card_le_card hsub
    _ ≤ 3 * 2 ^ (R + R + 1) := card_ball_le H degree v (R + R)
    _ ≤ overlapBound R := by
        unfold overlapBound
        have : 2 ^ (R + R + 1) ≤ 2 ^ (2 * R + 2) := Nat.pow_le_pow_right two_pos (by omega)
        omega

end Algebraic.Cutwidth.Gaussian.Internal
