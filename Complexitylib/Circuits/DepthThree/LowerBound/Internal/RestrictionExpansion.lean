/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionPaths
public import Mathlib.Data.List.Induction
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: restriction expansion

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionExpansion.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open Finset
open scoped BigOperators

namespace DepthThreeLowerBound

universe u v

variable {V : Type u} {I : Type v} [DecidableEq V] [instDecidableEqI : DecidableEq I]
  [instFintypeI : Fintype I]

/-- The real indicator that a clause is violated. -/
def violationValue (violation : I → Bool) (i : I) : ℝ :=
  if violation i = true then 1 else 0

/-- The total number of violated clauses in the indexed family. -/
def totalCount (violation : I → Bool) : ℕ :=
  (univ.filter fun i => violation i = true).card

/-- The number of violated clauses in the easy part of the family. -/
def easyCount (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (U : Finset V) : ℕ :=
  (univ.filter fun i => (residual scope T U i).card ≤ b ∧ violation i = true).card

/-- The number of violated clauses covered by the revealed coordinates. -/
def coveredCount (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (U : Finset V) : ℕ :=
  (univ.filter fun i => residual scope T U i = ∅ ∧ violation i = true).card

/-- The product of violation indicators along a path. -/
def pathNumerator (violation : I → Bool) (P : List I) : ℝ :=
  (P.map (violationValue violation)).prod

/-- The product of covered-clause counts along a path. -/
def pathDenominator (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (P : List I) : ℝ :=
  P.reverseRecOn 1 fun Q i d => d * (easyCount scope T b violation
    (revealed scope T (Q ++ [i])) : ℝ)

/-- The numerator-to-denominator contribution of a path. -/
def pathTerm (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (P : List I) : ℝ :=
  pathNumerator violation P / pathDenominator scope T b violation P

/-- The residual factor after the clauses on a path have been selected. -/
def pathResidual (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (P : List I) : ℝ :=
  P.reverseRecOn 0 fun Q i _ => pathNumerator violation (Q ++ [i]) /
    ((totalCount violation : ℝ) * pathDenominator scope T b violation Q)

omit [DecidableEq I] [Fintype I] in
@[simp] theorem pathNumerator_nil
    {I : Type v}


    (violation : I → Bool) :
    pathNumerator violation [] = 1 := by simp [pathNumerator]
omit [DecidableEq I] [Fintype I] in
@[simp] theorem pathNumerator_snoc
    {I : Type v}


    (violation : I → Bool) (P : List I) (i : I) :
    pathNumerator violation (P ++ [i]) =
      pathNumerator violation P * violationValue violation i := by
  classical
  simp [pathNumerator]
@[simp] theorem pathDenominator_nil (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) : pathDenominator scope T b violation [] = 1 := by
  simp [pathDenominator]

@[simp] theorem pathDenominator_snoc (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) (i : I) :
    pathDenominator scope T b violation (P ++ [i]) =
      pathDenominator scope T b violation P *
        (easyCount scope T b violation (revealed scope T (P ++ [i])) : ℝ) := by
  simp [pathDenominator]

@[simp] theorem pathResidual_snoc (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) (i : I) :
    pathResidual scope T b violation (P ++ [i]) =
      pathNumerator violation (P ++ [i]) /
        ((totalCount violation : ℝ) * pathDenominator scope T b violation P) := by
  simp [pathResidual]

omit [DecidableEq I] [Fintype I] in
theorem pathNumerator_ne_zero_iff
    {I : Type v}


    (violation : I → Bool) (P : List I) :
    pathNumerator violation P ≠ 0 ↔ ∀ i ∈ P, violation i = true := by
  classical
  induction P with
  | nil => simp [pathNumerator]
  | cons i P ih =>
      have hi : violationValue violation i ≠ 0 ↔ violation i = true := by
        cases h : violation i <;> simp [violationValue, h]
      simpa only [pathNumerator, List.map_cons, List.prod_cons, mul_ne_zero_iff,
        List.forall_mem_cons] using and_congr hi ih
omit [DecidableEq I] in
theorem coveredCount_le_easyCount
    {V : Type u}
    {I : Type v}
    [DecidableEq V]

    [instFintypeI : Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (U : Finset V) :
    coveredCount scope T violation U ≤ easyCount scope T b violation U := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨by rw [hi.1]; simp, hi.2⟩
omit [DecidableEq I] in
theorem easyCount_le_totalCount
    {V : Type u}
    {I : Type v}
    [DecidableEq V]

    [instFintypeI : Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (U : Finset V) :
    easyCount scope T b violation U ≤ totalCount violation := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.2
theorem length_le_coveredCount_of_support (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b n) (hs : pathNumerator violation P ≠ 0) :
    P.length ≤ coveredCount scope T violation (revealed scope T P) := by
  have hnd := nodup_of_mem_paths hP
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro i hi
  have him : i ∈ P := List.mem_toFinset.mp hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨residual_eq_empty_of_mem him, (pathNumerator_ne_zero_iff violation P).mp hs i him⟩

theorem easyCount_pos_of_support (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b (n + 1)) (hs : pathNumerator violation P ≠ 0) :
    0 < easyCount scope T b violation (revealed scope T P) := by
  have h := (length_le_coveredCount_of_support scope T b violation hP hs).trans
    (coveredCount_le_easyCount scope T b violation _)
  rw [length_of_mem_paths hP] at h
  exact (Nat.succ_pos n).trans_le h

theorem pathDenominator_pos_of_support (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b n) (hs : pathNumerator violation P ≠ 0) :
    0 < pathDenominator scope T b violation P := by
  induction n generalizing P with
  | zero =>
      have he : P = [] := List.length_eq_zero_iff.mp (length_of_mem_paths hP)
      subst P
      simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      have hQs : pathNumerator violation Q ≠ 0 := by
        exact (mul_ne_zero_iff.mp (by simpa only [pathNumerator_snoc] using hs)).1
      rw [pathDenominator_snoc]
      exact mul_pos (ih hQ hQs)
        (Nat.cast_pos.mpr (easyCount_pos_of_support scope T b violation hP hs))

omit [DecidableEq I] [Fintype I] in
private theorem cast_count
    {I : Type v}


    (violation : I → Bool) (s : Finset I) :
    ((s.filter fun i => violation i = true).card : ℝ) =
      ∑ i ∈ s, violationValue violation i := by
  classical
  simp [violationValue]
omit instDecidableEqI in
theorem totalCount_eq_easy_add_hard (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (U : Finset V) :
    (totalCount violation : ℝ) = (easyCount scope T b violation U : ℝ) +
      ∑ i ∈ hardIndices scope T b U, violationValue violation i := by
  have h := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset I))
    (p := fun i => (residual scope T U i).card ≤ b) (violationValue violation)
  have heasy : (easyCount scope T b violation U : ℝ) =
      ∑ i ∈ univ.filter (fun i => (residual scope T U i).card ≤ b),
        violationValue violation i := by
    rw [← cast_count]
    simp [easyCount, Finset.filter_filter]
  rw [heasy]
  simpa only [totalCount, cast_count, hardIndices, not_le] using h.symm

theorem path_residual_identity (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b (n + 1)) (hq : totalCount violation ≠ 0) :
    pathResidual scope T b violation P = pathTerm scope T b violation P -
      ∑ i ∈ hardIndices scope T b (revealed scope T P),
        pathResidual scope T b violation (P ++ [i]) := by
  by_cases hs : pathNumerator violation P = 0
  · obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
    simp only [pathResidual_snoc, pathTerm, hs, zero_div, pathNumerator_snoc,
      zero_mul, Finset.sum_const_zero, sub_zero]
  · have hd := ne_of_gt (pathDenominator_pos_of_support scope T b violation hP hs)
    have ha := ne_of_gt (Nat.cast_pos.mpr
      (easyCount_pos_of_support scope T b violation hP hs) :
        (0 : ℝ) < easyCount scope T b violation (revealed scope T P))
    have hqr : (totalCount violation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have hext : (∑ i ∈ hardIndices scope T b (revealed scope T P),
        pathResidual scope T b violation (P ++ [i])) =
        pathNumerator violation P /
          ((totalCount violation : ℝ) * pathDenominator scope T b violation P) *
          ∑ i ∈ hardIndices scope T b (revealed scope T P), violationValue violation i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pathResidual_snoc, pathNumerator_snoc]
      ring
    rw [hext]
    have hcounts := totalCount_eq_easy_add_hard scope T b violation (revealed scope T P)
    have hsum : (∑ i ∈ hardIndices scope T b (revealed scope T P),
        violationValue violation i) = (totalCount violation : ℝ) -
          (easyCount scope T b violation (revealed scope T P) : ℝ) := by
      linarith
    rw [hsum]
    obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
    have hQnum : pathNumerator violation Q ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa only [pathNumerator_snoc] using hs)).1
    have hQden := ne_of_gt (pathDenominator_pos_of_support scope T b violation hQ hQnum)
    simp only [pathResidual_snoc, pathTerm, pathDenominator_snoc]
    have halg (z q d a : ℝ) (hq' : q ≠ 0) (hd' : d ≠ 0) (ha' : a ≠ 0) :
        z / (q * d) = z / (d * a) - z / (q * (d * a)) * (q - a) := by
      field_simp [hq', hd', ha']
      ; ring
    exact halg _ _ _ _ hqr hQden ha

theorem sum_path_residual_identity (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (n : ℕ) (hq : totalCount violation ≠ 0) :
    (∑ P ∈ paths scope T b (n + 1), pathResidual scope T b violation P) =
      (∑ P ∈ paths scope T b (n + 1), pathTerm scope T b violation P) -
        ∑ P ∈ paths scope T b (n + 2), pathResidual scope T b violation P := by
  calc
    _ = ∑ P ∈ paths scope T b (n + 1),
        (pathTerm scope T b violation P -
          ∑ i ∈ hardIndices scope T b (revealed scope T P),
            pathResidual scope T b violation (P ++ [i])) := by
      apply Finset.sum_congr rfl
      intro P hP
      exact path_residual_identity scope T b violation hP hq
    _ = _ := by
      rw [Finset.sum_sub_distrib,
        sum_paths_succ scope T b (n + 1) (pathResidual scope T b violation)]

theorem sum_initial_residual (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool)
    (he : easyCount scope T b violation ∅ = 0) (hq : totalCount violation ≠ 0) :
    (∑ P ∈ paths scope T b 1, pathResidual scope T b violation P) = 1 := by
  have hs (i : I) : pathResidual scope T b violation [i] =
      violationValue violation i / (totalCount violation : ℝ) := by
    change pathResidual scope T b violation ([] ++ [i]) = _
    rw [pathResidual_snoc, pathNumerator_snoc]
    simp
  have hcounts := totalCount_eq_easy_add_hard scope T b violation ∅
  have hsum : (∑ i ∈ hardIndices scope T b ∅, violationValue violation i) =
      (totalCount violation : ℝ) := by simpa [he] using hcounts.symm
  rw [show (1 : ℕ) = 0 + 1 by rfl, sum_paths_succ]
  simp only [paths, Finset.sum_singleton, revealed, List.toFinset_nil,
    Finset.biUnion_empty, List.nil_append, hs]
  rw [← Finset.sum_div, hsum, div_self (Nat.cast_ne_zero.mpr hq)]

theorem finite_alternating_telescoping (t r : ℕ → ℝ)
    (h : ∀ n, r (n + 1) = t (n + 1) - r (n + 2)) (N : ℕ) :
    (∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) * t (j + 1)) =
      -r 1 + (-1 : ℝ) ^ N * r (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, h N]
      simp only [pow_succ]
      ring

theorem pathTerm_zero_of_totalCount_zero (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b (n + 1)) (hq : totalCount violation = 0) :
    pathTerm scope T b violation P = 0 := by
  have hz : pathNumerator violation P = 0 := by
    by_contra hs
    have h := (length_le_coveredCount_of_support scope T b violation hP hs).trans
      ((coveredCount_le_easyCount scope T b violation _).trans
        (easyCount_le_totalCount scope T b violation _))
    rw [length_of_mem_paths hP, hq] at h
    omega
  simp [pathTerm, hz]

theorem finite_violation_expansion (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) :
    (if totalCount violation = 0 then (1 : ℝ) else 0) =
      (if easyCount scope T b violation ∅ = 0 then (1 : ℝ) else 0) *
        (1 + ∑ j ∈ Finset.range (T.card / (b + 1)),
          (-1 : ℝ) ^ (j + 1) *
            ∑ P ∈ paths scope T b (j + 1), pathTerm scope T b violation P) := by
  by_cases he : easyCount scope T b violation ∅ = 0
  · by_cases hq : totalCount violation = 0
    · have hz (j : ℕ) :
          (∑ P ∈ paths scope T b (j + 1), pathTerm scope T b violation P) = 0 := by
        apply Finset.sum_eq_zero
        intro P hP
        exact pathTerm_zero_of_totalCount_zero scope T b violation hP hq
      simp [he, hq, hz]
    · let t : ℕ → ℝ := fun j =>
        ∑ P ∈ paths scope T b j, pathTerm scope T b violation P
      let r : ℕ → ℝ := fun j =>
        ∑ P ∈ paths scope T b j, pathResidual scope T b violation P
      have hr : ∀ n, r (n + 1) = t (n + 1) - r (n + 2) :=
        fun n => sum_path_residual_identity scope T b violation n hq
      have hfirst : r 1 = 1 := sum_initial_residual scope T b violation he hq
      have hlast : r (T.card / (b + 1) + 1) = 0 := by
        dsimp [r]
        rw [paths_horizon_eq_empty]
        simp
      have htel := finite_alternating_telescoping t r hr (T.card / (b + 1))
      rw [hfirst, hlast, mul_zero, add_zero] at htel
      simp only [he, hq, ite_eq_left, ite_false, one_mul]
      change 0 = 1 + ∑ j ∈ Finset.range (T.card / (b + 1)),
        (-1 : ℝ) ^ (j + 1) * t (j + 1)
      rw [htel]
      norm_num
  · have hq : totalCount violation ≠ 0 := by
      intro hq
      apply he
      exact Nat.eq_zero_of_le_zero (hq ▸ easyCount_le_totalCount scope T b violation ∅)
    simp [he, hq]

end DepthThreeLowerBound

end

end Complexity
