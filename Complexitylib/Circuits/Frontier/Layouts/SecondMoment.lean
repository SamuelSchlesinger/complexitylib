/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance

/-!
# Second-moment concentration for local events

Let `Y` count the events `A k`, `k ∈ F`, under a product of probability measures, where each
event depends only on the coordinates in a finite set `S k`, and each `S k` meets at most `D` of
the sets `S l`, `l ∈ F`.

* Two events whose coordinate sets are disjoint are functions of disjoint blocks of independent
  coordinates, so their indicators are independent and have covariance zero.
* Any two indicators have covariance at most one.

Summing the covariances over pairs gives `Var Y ≤ |F| D`, and Chebyshev's inequality bounds the
probability that `Y` deviates from its mean `∑ k, P(A k)` by at least `c` by `|F| D / c ^ 2`.
Locality is expressed by Mathlib's `DependsOn`, and the coordinate spaces are arbitrary.

## Main results

* `Frontier.Gaussian.pi_variance_sum_indicator_le`: `Var Y ≤ |F| D`.
* `Frontier.Gaussian.pi_deviation_le`: `P(|Y - E Y| ≥ c) ≤ |F| D / c ^ 2`.
-/

@[expose] public section

namespace Complexity.Frontier.Gaussian

open MeasureTheory ProbabilityTheory

/-- The unit indicator of a measurable set is square integrable under a finite measure. -/
private theorem memLp_indicator_one {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {s : Set α} (hs : MeasurableSet s) :
    MemLp (s.indicator fun _ => (1 : ℝ)) 2 ν :=
  memLp_indicator_const 2 hs.nullMeasurableSet 1 (Or.inr (measure_ne_top ν s))

/-- Two unit indicators have covariance `P(s ∩ t) - P(s) P(t) ≤ 1`. -/
private theorem covariance_indicator_le_one {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    cov[s.indicator fun _ => (1 : ℝ), t.indicator fun _ => (1 : ℝ); ν] ≤ 1 := by
  have hst : (s.indicator fun _ => (1 : ℝ)) * t.indicator (fun _ => (1 : ℝ)) =
      (s ∩ t).indicator fun _ => (1 : ℝ) :=
    Set.inter_indicator_one.symm
  rw [covariance_eq_sub (memLp_indicator_one hs) (memLp_indicator_one ht), hst,
    integral_indicator_const _ (hs.inter ht), integral_indicator_const _ hs,
    integral_indicator_const _ ht]
  simp only [smul_eq_mul, mul_one]
  have h₁ : ν.real (s ∩ t) ≤ 1 := measureReal_le_one
  nlinarith [measureReal_nonneg (μ := ν) (s := s), measureReal_nonneg (μ := ν) (s := t)]

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype ι] in
/-- The indicator of a measurable event depending only on the coordinates in `S` is a
measurable function of those coordinates: freeze the others at `ω₀`. -/
private theorem exists_indicator_eq_comp {S : Finset ι} {A : Set (Π i, Ω i)}
    (hA : MeasurableSet A) (hdep : DependsOn (· ∈ A) (S : Set ι)) (ω₀ : Π i, Ω i) :
    ∃ g : (Π i : S, Ω i) → ℝ, Measurable g ∧
      A.indicator (fun _ => (1 : ℝ)) = g ∘ fun ω (i : S) => ω i := by
  classical
  refine ⟨fun y => A.indicator (fun _ => (1 : ℝ)) (Function.updateFinset ω₀ S y),
    (measurable_const.indicator hA).comp measurable_updateFinset, ?_⟩
  funext ω
  have hmem : (Function.updateFinset ω₀ S (fun i : S => ω i) ∈ A) = (ω ∈ A) :=
    hdep fun i hi => by simp [Function.updateFinset, Finset.mem_coe.1 hi]
  exact Set.indicator_eq_indicator (f := fun _ => (1 : ℝ)) (g := fun _ => (1 : ℝ))
    (iff_of_eq hmem).symm rfl

/-- Events depending on disjoint sets of coordinates have independent indicators under a
product of probability measures. -/
private theorem indepFun_indicator_of_disjoint {S T : Finset ι} {A B : Set (Π i, Ω i)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hdepA : DependsOn (· ∈ A) (S : Set ι))
    (hdepB : DependsOn (· ∈ B) (T : Set ι)) (hST : Disjoint S T) :
    IndepFun (A.indicator fun _ => (1 : ℝ)) (B.indicator fun _ => (1 : ℝ)) (Measure.pi μ) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure (Measure.pi μ)
  obtain ⟨g, hg, hgA⟩ := exists_indicator_eq_comp hA hdepA ω₀
  obtain ⟨h, hh, hhB⟩ := exists_indicator_eq_comp hB hdepB ω₀
  have hind : iIndepFun (fun i (ω : Π i, Ω i) => ω i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun i => (id : Ω i → Ω i)) fun _ => aemeasurable_id
  rw [hgA, hhB]
  exact (hind.indepFun_finset S T hST fun i => measurable_pi_apply i).comp hg hh

/-- **Variance of a count of local events.** Under a product of probability measures,
if each event depends only on the coordinates in `S k` and each `S k` meets at most `D`
of the coordinate sets, the number of events that occur has variance at most `|F| D`. -/
theorem pi_variance_sum_indicator_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (F : Finset κ) (A : κ → Set (Π i, Ω i))
    (S : κ → Finset ι) (measurable : ∀ k ∈ F, MeasurableSet (A k))
    (depends : ∀ k ∈ F, DependsOn (· ∈ A k) (S k : Set ι))
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
    _ ≤ ∑ _k ∈ F, (D : ℝ) := Finset.sum_le_sum fun k hk => by exact_mod_cast overlap k hk
    _ = F.card * D := by simp

/-- **Second-moment concentration for local events.** Under a product of probability
measures on arbitrary measurable spaces, the number of events that occur deviates from
its mean by at least `c` with probability at most `|F| D / c ^ 2`, when each event depends
on a finite set of coordinates and each coordinate set meets at most `D` of them. -/
theorem pi_deviation_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (F : Finset κ) (A : κ → Set (Π i, Ω i))
    (S : κ → Finset ι) (measurable : ∀ k ∈ F, MeasurableSet (A k))
    (depends : ∀ k ∈ F, DependsOn (· ∈ A k) (S k : Set ι))
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
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (cheb.trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (by gcongr; exact pi_variance_sum_indicator_le μ F A S measurable depends overlap)

end Complexity.Frontier.Gaussian
