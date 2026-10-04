/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Second moments of local event counts

Under a product of probability measures, two events that depend on disjoint finite
sets of coordinates have independent indicators, so their covariance vanishes; any
two unit indicators have covariance at most one. Summing over pairs bounds the
variance of the event count, and Chebyshev's inequality bounds its deviation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory

/-- The unit indicator of a measurable set is square integrable under a finite measure. -/
theorem memLp_indicator_one {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {s : Set α} (hs : MeasurableSet s) :
    MemLp (s.indicator fun _ => (1 : ℝ)) 2 ν :=
  memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top ν s))

/-- Two unit indicators have covariance at most one under a probability measure. -/
theorem covariance_indicator_le_one {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    cov[s.indicator fun _ => (1 : ℝ), t.indicator fun _ => (1 : ℝ); ν] ≤ 1 := by
  rw [covariance_eq_sub (memLp_indicator_one hs) (memLp_indicator_one ht)]
  have hst : (s.indicator fun _ => (1 : ℝ)) * t.indicator (fun _ => (1 : ℝ)) =
      (s ∩ t).indicator fun _ => (1 : ℝ) :=
    Set.inter_indicator_one.symm
  rw [hst, integral_indicator_const _ (hs.inter ht), integral_indicator_const _ hs,
    integral_indicator_const _ ht]
  simp only [smul_eq_mul, mul_one]
  have h₁ : ν.real (s ∩ t) ≤ 1 := measureReal_le_one
  have h₂ : 0 ≤ ν.real s := measureReal_nonneg
  have h₃ : 0 ≤ ν.real t := measureReal_nonneg
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype ι] in
/-- The indicator of a measurable set depending only on the coordinates in `S` is a
measurable function of those coordinates. -/
theorem exists_indicator_eq_comp {S : Finset ι} {A : Set (Π i, Ω i)} (hA : MeasurableSet A)
    (hdep : ∀ ω ω' : Π i, Ω i, (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A))
    (ω₀ : Π i, Ω i) :
    ∃ g : (Π i : S, Ω i) → ℝ, Measurable g ∧
      A.indicator (fun _ => (1 : ℝ)) = g ∘ fun ω (i : S) => ω i := by
  refine ⟨fun y => A.indicator (fun _ => (1 : ℝ)) (Function.updateFinset ω₀ S y),
    (measurable_const.indicator hA).comp measurable_updateFinset, ?_⟩
  funext ω
  have hmem : Function.updateFinset ω₀ S (fun i : S => ω i) ∈ A ↔ ω ∈ A :=
    hdep _ _ fun i hi => by simp [Function.updateFinset, hi]
  exact Set.indicator_eq_indicator (f := fun _ => (1 : ℝ)) (g := fun _ => (1 : ℝ))
    hmem.symm rfl

/-- Events depending on disjoint coordinate sets have independent indicators under a
product of probability measures. -/
theorem indepFun_indicator_of_disjoint {S T : Finset ι} {A B : Set (Π i, Ω i)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdepA : ∀ ω ω' : Π i, Ω i, (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A))
    (hdepB : ∀ ω ω' : Π i, Ω i, (∀ i ∈ T, ω i = ω' i) → (ω ∈ B ↔ ω' ∈ B))
    (hST : Disjoint S T) :
    IndepFun (A.indicator fun _ => (1 : ℝ)) (B.indicator fun _ => (1 : ℝ)) (Measure.pi μ) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure (Measure.pi μ)
  obtain ⟨g, hg, hgA⟩ := exists_indicator_eq_comp hA hdepA ω₀
  obtain ⟨h, hh, hhB⟩ := exists_indicator_eq_comp hB hdepB ω₀
  have hind : iIndepFun (fun i (ω : Π i, Ω i) => ω i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun i => (id : Ω i → Ω i)) fun _ => aemeasurable_id
  rw [hgA, hhB]
  exact (hind.indepFun_finset S T hST fun i => measurable_pi_apply i).comp hg hh

/-- The variance of a count of local events is at most the number of events times a
bound on how many of their coordinate sets each coordinate set meets. -/
theorem variance_sum_indicator_le {κ : Type*} (F : Finset κ) (A : κ → Set (Π i, Ω i))
    (S : κ → Finset ι) (measurable : ∀ k ∈ F, MeasurableSet (A k))
    (depends : ∀ k ∈ F, ∀ ω ω' : Π i, Ω i, (∀ i ∈ S k, ω i = ω' i) → (ω ∈ A k ↔ ω' ∈ A k))
    {D : ℕ} (overlap : ∀ k ∈ F, (F.filter fun l => ¬ Disjoint (S k) (S l)).card ≤ D) :
    Var[fun ω => ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω; Measure.pi μ] ≤
      F.card * D := by
  rw [variance_fun_sum' fun k hk => memLp_indicator_one (measurable k hk)]
  calc ∑ k ∈ F, ∑ l ∈ F, cov[(A k).indicator fun _ => (1 : ℝ),
        (A l).indicator fun _ => (1 : ℝ); Measure.pi μ]
      ≤ ∑ k ∈ F, ∑ l ∈ F, if ¬ Disjoint (S k) (S l) then (1 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => ?_
        by_cases hkl : Disjoint (S k) (S l)
        · rw [ite_eq_right (not_not.mpr hkl), (indepFun_indicator_of_disjoint (measurable k hk)
            (measurable l hl) (depends k hk) (depends l hl) hkl).covariance_eq_zero
            (memLp_indicator_one (measurable k hk)) (memLp_indicator_one (measurable l hl))]
        · rw [ite_eq_left hkl]
          exact covariance_indicator_le_one (measurable k hk) (measurable l hl)
    _ = ∑ k ∈ F, ((F.filter fun l => ¬ Disjoint (S k) (S l)).card : ℝ) := by
        simp only [Finset.sum_boole]
    _ ≤ ∑ _k ∈ F, (D : ℝ) :=
        Finset.sum_le_sum fun k hk => by exact_mod_cast overlap k hk
    _ = F.card * D := by simp

/-- **Chebyshev for local event counts.** The count deviates from its mean by at least
`c` with probability at most `|F| D / c²`. -/
theorem pi_deviation_le {κ : Type*} (F : Finset κ) (A : κ → Set (Π i, Ω i))
    (S : κ → Finset ι) (measurable : ∀ k ∈ F, MeasurableSet (A k))
    (depends : ∀ k ∈ F, ∀ ω ω' : Π i, Ω i, (∀ i ∈ S k, ω i = ω' i) → (ω ∈ A k ↔ ω' ∈ A k))
    {D : ℕ} (overlap : ∀ k ∈ F, (F.filter fun l => ¬ Disjoint (S k) (S l)).card ≤ D)
    {c : ℝ} (hc : 0 < c) :
    (Measure.pi μ).real {ω | c ≤ |∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
        ∑ k ∈ F, (Measure.pi μ).real (A k)|} ≤ F.card * D / c ^ 2 := by
  have hY : MemLp (fun ω => ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω) 2
      (Measure.pi μ) :=
    memLp_finsetSum F fun k hk => memLp_indicator_one (measurable k hk)
  have hmean : ∫ ω, ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω ∂Measure.pi μ =
      ∑ k ∈ F, (Measure.pi μ).real (A k) := by
    rw [integral_finsetSum _ fun k hk =>
      (memLp_indicator_one (measurable k hk)).integrable one_le_two]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_indicator_const _ (measurable k hk), smul_eq_mul, mul_one]
  have cheb := meas_ge_le_variance_div_sq hY hc
  rw [hmean] at cheb
  have hvar := variance_sum_indicator_le F A S measurable depends overlap (μ := μ)
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (cheb.trans ?_)
  exact ENNReal.ofReal_le_ofReal (by gcongr)

end Algebraic.Cutwidth.Gaussian.Internal
