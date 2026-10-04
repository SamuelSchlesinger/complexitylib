/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.SecondMoment.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.SecondMoment.Internal

/-!
# Second-moment concentration for local events

Let `Y` count the events `A k`, `k ∈ F`, under a product of probability measures, where
each event depends only on the coordinates in a finite set `S k`, and each `S k` meets at
most `D` of the sets `S l`, `l ∈ F`. Indicators of events with disjoint coordinate sets
are independent, so their covariance vanishes; every other pair has covariance at most
one. Hence `Var Y ≤ |F| D`, and Chebyshev's inequality bounds the probability that `Y`
deviates from its mean `∑ k, P(A k)` by at least `c` by `|F| D / c²`.

The first two theorems hold for any product of probability measures on measurable
spaces; `pi_real_deviation_le` specializes the deviation bound to real coordinates,
with locality expressed by `DependsOn`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open MeasureTheory ProbabilityTheory

/-- **Variance of a count of local events.** Under a product of probability measures,
if each event depends only on the coordinates in `S k` and each `S k` meets at most `D`
of the coordinate sets, the number of events that occur has variance at most `|F| D`. -/
theorem pi_variance_sum_indicator_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (F : Finset κ) (A : κ → Set (Π i, Ω i))
    (S : κ → Finset ι) (measurable : ∀ k ∈ F, MeasurableSet (A k))
    (depends : ∀ k ∈ F, ∀ ω ω' : Π i, Ω i, (∀ i ∈ S k, ω i = ω' i) → (ω ∈ A k ↔ ω' ∈ A k))
    {D : ℕ} (overlap : ∀ k ∈ F, (F.filter fun l => ¬ Disjoint (S k) (S l)).card ≤ D) :
    Var[fun ω => ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω; Measure.pi μ] ≤
      F.card * D :=
  Internal.variance_sum_indicator_le F A S measurable depends overlap

/-- **Second-moment concentration for local events.** Under a product of probability
measures on arbitrary measurable spaces, the number of events that occur deviates from
its mean by at least `c` with probability at most `|F| D / c²`, when each event depends
on a finite set of coordinates and each coordinate set meets at most `D` of them. -/
theorem pi_deviation_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (F : Finset κ) (A : κ → Set (Π i, Ω i))
    (S : κ → Finset ι) (measurable : ∀ k ∈ F, MeasurableSet (A k))
    (depends : ∀ k ∈ F, ∀ ω ω' : Π i, Ω i, (∀ i ∈ S k, ω i = ω' i) → (ω ∈ A k ↔ ω' ∈ A k))
    {D : ℕ} (overlap : ∀ k ∈ F, (F.filter fun l => ¬ Disjoint (S k) (S l)).card ≤ D)
    {c : ℝ} (hc : 0 < c) :
    (Measure.pi μ).real {ω | c ≤ |∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
        ∑ k ∈ F, (Measure.pi μ).real (A k)|} ≤ F.card * D / c ^ 2 :=
  Internal.pi_deviation_le F A S measurable depends overlap hc

/-- **Second-moment concentration for local events.** Under a product of probability
measures, the number of events that occur deviates from its mean by at least `c` with
probability at most `|F| D / c²`, when each event depends on a finite set of coordinates
and each coordinate set meets at most `D` of them. -/
theorem pi_real_deviation_le {ι κ : Type} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (F : Finset κ) (A : κ → Set (ι → ℝ)) (S : κ → Finset ι)
    (measurable : ∀ k ∈ F, MeasurableSet (A k)) (depends : ∀ k ∈ F, DependsOn (S k) (A k))
    {D : ℕ} (overlap : ∀ k ∈ F, (F.filter fun l => ¬ Disjoint (S k) (S l)).card ≤ D)
    {c : ℝ} (hc : 0 < c) :
    (Measure.pi μ).real {ω | c ≤ |∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
        ∑ k ∈ F, (Measure.pi μ).real (A k)|} ≤ F.card * D / c ^ 2 :=
  pi_deviation_le μ F A S measurable depends overlap hc

end Algebraic.Cutwidth.Gaussian
