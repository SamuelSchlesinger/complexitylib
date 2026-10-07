/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Unrestricted depth-three lower bound: restriction paths

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionPaths.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3

namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} {I : Type uDepth2} [DecidableEq V] [instDecidableEqI : DecidableEq I]

/-- The variables revealed by the selected sequence of clause scopes. -/
def revealed (scope : I → Finset V) (T : Finset V) (P : List I) : Finset V :=
  P.toFinset.biUnion fun i => scope i ∩ T

/-- Coordinates remaining after the currently revealed set is removed. -/
def residual (scope : I → Finset V) (T U : Finset V) (i : I) : Finset V :=
  scope i ∩ (T \ U)

@[simp] theorem revealed_nil (scope : I → Finset V) (T : Finset V) :
    revealed scope T [] = ∅ := by simp [revealed]

theorem mem_revealed (scope : I → Finset V) (T : Finset V) (P : List I) (v : V) :
    v ∈ revealed scope T P ↔ ∃ i ∈ P, v ∈ scope i ∧ v ∈ T := by
  simp [revealed]

theorem revealed_subset (scope : I → Finset V) (T : Finset V) (P : List I) :
    revealed scope T P ⊆ T := by
  intro v hv
  obtain ⟨i, hi, hv, ht⟩ := (mem_revealed scope T P v).mp hv
  exact ht

theorem revealed_mono (scope : I → Finset V) (T : Finset V) {P Q : List I}
    (h : P ⊆ Q) : revealed scope T P ⊆ revealed scope T Q := by
  intro v hv
  obtain ⟨i, hi, hv, ht⟩ := (mem_revealed scope T P v).mp hv
  exact (mem_revealed scope T Q v).mpr ⟨i, h hi, hv, ht⟩

@[simp] theorem revealed_snoc (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    revealed scope T (P ++ [i]) = revealed scope T P ∪ (scope i ∩ T) := by
  ext v
  simp only [mem_revealed, List.mem_append, List.mem_singleton,
    Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨j, hj, hv⟩
    rcases hj with hj | rfl
    · exact Or.inl ⟨j, hj, hv⟩
    · exact Or.inr hv
  · rintro (⟨j, hj, hv⟩ | hv)
    · exact ⟨j, Or.inl hj, hv⟩
    · exact ⟨i, Or.inr rfl, hv⟩

omit [DecidableEq I] in
theorem residual_eq_sdiff
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]

    (scope : I → Finset V) (T U : Finset V) (i : I) :
    residual scope T U i = (scope i ∩ T) \ U := by
  classical
  ext v
  simp [residual, and_assoc]
theorem residual_eq_empty_of_mem {scope : I → Finset V} {T : Finset V}
    {P : List I} {i : I} (hi : i ∈ P) :
    residual scope T (revealed scope T P) i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [residual, Finset.mem_inter, Finset.mem_sdiff] at hv
  exact hv.2.2 ((mem_revealed scope T P v).mpr ⟨i, hi, hv.1, hv.2.1⟩)

theorem card_revealed_snoc (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    (revealed scope T (P ++ [i])).card =
      (revealed scope T P).card + (residual scope T (revealed scope T P) i).card := by
  rw [revealed_snoc, residual_eq_sdiff, Finset.union_comm]
  exact (Finset.card_sdiff_add_card (scope i ∩ T) (revealed scope T P)).symm.trans
    (Nat.add_comm _ _)

variable [Fintype I]

/-- Clause indices whose residual scope exceeds the width cutoff. -/
def hardIndices (scope : I → Finset V) (T : Finset V) (b : ℕ) (U : Finset V) :
    Finset I := Finset.univ.filter fun i => b < (residual scope T U i).card

omit [DecidableEq I] in
@[simp] theorem mem_hardIndices
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]

    [Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (U : Finset V) (i : I) :
    i ∈ hardIndices scope T b U ↔ b < (residual scope T U i).card := by
  classical
  simp [hardIndices]
/-- Admissible clause-index paths of the specified length. -/
def paths (scope : I → Finset V) (T : Finset V) (b : ℕ) : ℕ → Finset (List I)
  | 0 => {[]}
  | n + 1 => (paths scope T b n).biUnion fun P =>
      (hardIndices scope T b (revealed scope T P)).image fun i => P ++ [i]

@[simp] theorem paths_zero (scope : I → Finset V) (T : Finset V) (b : ℕ) :
    paths scope T b 0 = {[]} := rfl

theorem paths_succ (scope : I → Finset V) (T : Finset V) (b n : ℕ) :
    paths scope T b (n + 1) = (paths scope T b n).biUnion fun P =>
      (hardIndices scope T b (revealed scope T P)).image fun i => P ++ [i] := rfl

theorem mem_paths_zero (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (P : List I) : P ∈ paths scope T b 0 ↔ P = [] := by
  simp [paths]

theorem mem_paths_succ {scope : I → Finset V} {T : Finset V}
    {b n : ℕ} {P : List I} :
    P ∈ paths scope T b (n + 1) ↔
      ∃ Q ∈ paths scope T b n, ∃ i ∈ hardIndices scope T b (revealed scope T Q),
        Q ++ [i] = P := by
  simp only [paths_succ, Finset.mem_biUnion, Finset.mem_image]

theorem snoc_mem_paths (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} {i : I}
    (hP : P ∈ paths scope T b n)
    (hi : i ∈ hardIndices scope T b (revealed scope T P)) :
    P ++ [i] ∈ paths scope T b (n + 1) :=
  mem_paths_succ.mpr ⟨P, hP, i, hi, rfl⟩

theorem mem_paths_snoc_iff (scope : I → Finset V) (T : Finset V)
    (b n : ℕ) (P : List I) (i : I) :
    P ++ [i] ∈ paths scope T b (n + 1) ↔
      P ∈ paths scope T b n ∧ i ∈ hardIndices scope T b (revealed scope T P) := by
  constructor
  · intro h
    obtain ⟨Q, hQ, j, hj, heq⟩ := mem_paths_succ.mp h
    obtain ⟨hQP, hji⟩ := List.append_inj' heq rfl
    have hji' : j = i := by simpa using hji
    subst Q
    subst j
    exact ⟨hQ, hj⟩
  · rintro ⟨hP, hi⟩
    exact snoc_mem_paths scope T b hP hi

theorem length_of_mem_paths {scope : I → Finset V} {T : Finset V}
    {b : ℕ} {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) :
    P.length = n := by
  induction n generalizing P with
  | zero =>
      have h := (mem_paths_zero scope T b P).mp hP
      subst P
      rfl
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      simp [ih hQ]

theorem take_mem_paths (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n)
    {k : ℕ} (hk : k ≤ n) : P.take k ∈ paths scope T b k := by
  induction n generalizing P k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      by_cases hkn : k ≤ n
      · rw [List.take_append_of_le_length (by simpa [length_of_mem_paths hQ]
          using hkn)]
        exact ih hQ hkn
      · have hk' : k = n + 1 := by omega
        subst k
        rw [List.take_of_length_le (by simp [length_of_mem_paths hQ])]
        exact snoc_mem_paths scope T b hQ hi

theorem not_mem_of_hard (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {P : List I} {i : I}
    (hi : i ∈ hardIndices scope T b (revealed scope T P)) : i ∉ P := by
  intro hmem
  have hh := (mem_hardIndices scope T b (revealed scope T P) i).mp hi
  rw [residual_eq_empty_of_mem hmem, Finset.card_empty] at hh
  exact Nat.not_lt_zero _ hh

theorem nodup_of_mem_paths {scope : I → Finset V} {T : Finset V}
    {b : ℕ} {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) : P.Nodup := by
  induction n generalizing P with
  | zero =>
      have h := (mem_paths_zero scope T b P).mp hP
      subst P
      simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      exact (ih hQ).append (List.nodup_singleton i)
        (List.disjoint_singleton.mpr (not_mem_of_hard scope T b hi))

theorem mul_le_revealed_card (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) :
    n * (b + 1) ≤ (revealed scope T P).card := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      rw [Nat.succ_mul, card_revealed_snoc]
      exact Nat.add_le_add (ih hQ)
        (Nat.succ_le_of_lt ((mem_hardIndices scope T b (revealed scope T Q) i).mp hi))

theorem length_mul_le_revealed_card (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) :
    P.length * (b + 1) ≤ (revealed scope T P).card := by
  rw [length_of_mem_paths hP]
  exact mul_le_revealed_card scope T b hP

theorem paths_eq_empty_of_card_lt (scope : I → Finset V) (T : Finset V)
    (b n : ℕ) (hn : T.card < n * (b + 1)) : paths scope T b n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  have hle := (mul_le_revealed_card scope T b hP).trans
    (Finset.card_le_card (revealed_subset scope T P))
  exact (Nat.not_lt_of_ge hle) hn

theorem paths_horizon_eq_empty (scope : I → Finset V) (T : Finset V) (b : ℕ) :
    paths scope T b (T.card / (b + 1) + 1) = ∅ := by
  apply paths_eq_empty_of_card_lt
  exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos b)).mp (Nat.lt_succ_self _)

theorem sum_paths_succ (scope : I → Finset V) (T : Finset V) (b n : ℕ)
    {M : Type uDepth3} [AddCommMonoid M] (f : List I → M) :
    ∑ P ∈ paths scope T b (n + 1), f P =
      ∑ P ∈ paths scope T b n,
        ∑ i ∈ hardIndices scope T b (revealed scope T P), f (P ++ [i]) := by
  have hd : Set.PairwiseDisjoint (↑(paths scope T b n) : Set (List I))
      (fun P => (hardIndices scope T b (revealed scope T P)).image
        (fun i => P ++ [i])) := by
    intro P hP Q hQ hne
    apply Finset.disjoint_left.mpr
    intro R hR₁ hR₂
    obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hR₁
    obtain ⟨j, hj, hjR⟩ := Finset.mem_image.mp hR₂
    exact hne (List.append_inj_left' (hiR.trans hjR.symm) rfl)
  rw [paths_succ, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_image
  intro i hi j hj hij
  have h := List.append_inj_right' hij rfl
  simpa using h

end DepthThreeLowerBound

end Complexity
