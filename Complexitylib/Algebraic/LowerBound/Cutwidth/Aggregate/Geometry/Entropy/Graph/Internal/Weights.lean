/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite
public import Mathlib.Data.Finset.Insert

/-!
# Combining conditional message weights

A normalized conditional kernel extends a weight on an earlier tuple. The kernels
may depend on earlier coordinates, and positivity is needed only on realized inputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

variable {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Relabelling a finite message space preserves a weight certificate. -/
noncomputable def WeightBound.equiv {key : X → Y} {cost : ℝ}
    (bound : WeightBound key cost) (e : Y ≃ Z) :
    WeightBound (fun x => e (key x)) cost where
  weight z := bound.weight (e.symm z)
  nonneg z := bound.nonneg _
  mass := by simpa using (e.symm.sum_comp bound.weight).trans bound.mass
  positive x := by simpa using bound.positive x
  log_bound := by simpa using bound.log_bound

/-- A message on a subsingleton output space has zero cost. -/
noncomputable def WeightBound.subsingleton [Unique Y]
    (key : X → Y) : WeightBound key 0 where
  weight _ := 1
  nonneg _ := zero_le_one
  mass := by simp
  positive _ := zero_lt_one
  log_bound := by simp

/-- A parent-independent probability weight is a conditional kernel. -/
noncomputable def WeightBound.toConditional {key : X → Y} {cost : ℝ}
    (bound : WeightBound key cost) (parent : X → Z) :
    ConditionalWeightBound key parent cost where
  weight _ := bound.weight
  nonneg _ := bound.nonneg
  mass _ := bound.mass
  positive := bound.positive
  log_bound := bound.log_bound

/-- A kernel depending on selected coordinates can be read from a larger parent key. -/
noncomputable def ConditionalWeightBound.pullParent {key : X → Y} {parent : X → Z}
    {cost : ℝ} (readout : W → Z) (whole : X → W)
    (agree : ∀ x, readout (whole x) = parent x)
    (bound : ConditionalWeightBound key parent cost) :
    ConditionalWeightBound key whole cost where
  weight w := bound.weight (readout w)
  nonneg w := bound.nonneg _
  mass w := bound.mass _
  positive x := by simpa only [agree] using bound.positive x
  log_bound := by simpa only [agree] using bound.log_bound

/-- Multiplying an earlier weight by a normalized conditional kernel adds their costs. -/
noncomputable def WeightBound.pairConditional {parent : X → Z} {key : X → Y}
    {a b : ℝ} (previous : WeightBound parent a)
    (next : ConditionalWeightBound key parent b) :
    WeightBound (fun x => (key x, parent x)) (a + b) where
  weight yz := previous.weight yz.2 * next.weight yz.2 yz.1
  nonneg yz := mul_nonneg (previous.nonneg _) (next.nonneg _ _)
  mass := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, next.mass, mul_one]
    exact previous.mass
  positive x := mul_pos (previous.positive x) (next.positive x)
  log_bound := by
    simp_rw [Real.log_mul (previous.positive _).ne' (next.positive _).ne']
    rw [Finset.sum_add_distrib]
    nlinarith [previous.log_bound, next.log_bound]

/-- A deterministic readout cannot increase the certified message cost. -/
noncomputable def WeightBound.map {key : X → Y} {cost : ℝ}
    (bound : WeightBound key cost) (readout : Y → Z) :
    WeightBound (fun x => readout (key x)) cost := by
  let weight (z : Z) := ∑ y ∈ Finset.univ.filter (fun y => readout y = z), bound.weight y
  have included (y : Y) : bound.weight y ≤ weight (readout y) :=
    Finset.single_le_sum (fun z _ => bound.nonneg z) (by simp)
  refine {
    weight := weight
    nonneg := fun z => Finset.sum_nonneg fun y _ => bound.nonneg y
    mass := ?_
    positive := fun x => lt_of_lt_of_le (bound.positive x) (included (key x))
    log_bound := le_trans bound.log_bound ?_ }
  · exact (Finset.sum_fiberwise Finset.univ readout bound.weight).trans bound.mass
  · exact Finset.sum_le_sum fun x _ => Real.log_le_log (bound.positive x) (included (key x))

/-- A constant message has a zero-cost point-mass certificate. -/
noncomputable def WeightBound.const (value : Y) : WeightBound (fun _ : X => value) 0 :=
  (WeightBound.subsingleton (fun _ : X => ())).map (fun _ => value)

/-- An arbitrary Boolean message has the uniform one-bit certificate. -/
noncomputable def WeightBound.boolean (key : X → Bool) : WeightBound key (Real.log 2) where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  mass := by norm_num [Fintype.sum_bool]
  positive _ := by norm_num
  log_bound := by simp [Real.log_inv]

/-- Product weights add costs even when the two actual messages are dependent. -/
noncomputable def WeightBound.prod {left : X → Y} {right : X → Z} {a b : ℝ}
    (first : WeightBound left a) (second : WeightBound right b) :
    WeightBound (fun x => (left x, right x)) (a + b) :=
  (second.pairConditional (first.toConditional right)).mono (le_of_eq (add_comm b a))

/-- Coordinatewise probability weights add their costs without an independence premise. -/
noncomputable def WeightBound.pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : ι → Type*} [∀ i, Fintype (T i)] {key : ∀ i, X → T i} {cost : ι → ℝ}
    (bound : ∀ i, WeightBound (key i) (cost i)) :
    WeightBound (fun x i => key i x) (∑ i, cost i) where
  weight message := ∏ i, (bound i).weight (message i)
  nonneg message := Finset.prod_nonneg fun i _ => (bound i).nonneg _
  mass := by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun i _ => (bound i).mass
  positive x := Finset.prod_pos fun i _ => (bound i).positive x
  log_bound := by
    simp_rw [Real.log_prod (fun i _ => ((bound i).positive _).ne')]
    rw [Finset.sum_comm]
    have total := Finset.sum_le_sum (s := Finset.univ) fun i _ => (bound i).log_bound
    simpa only [← Finset.mul_sum] using total

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
