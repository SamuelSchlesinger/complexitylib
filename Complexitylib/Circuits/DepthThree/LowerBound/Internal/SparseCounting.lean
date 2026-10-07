/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod

/-!
# Unrestricted depth-three lower bound: sparse counting

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseCounting.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1}
variable [instDecidableEqV : DecidableEq V]

/-- Clauses in the family with the specified cardinality. -/
def clausesOfSize (A : Finset (Clause V)) (u : ℕ) : Finset (Clause V) :=
  A.filter (fun C => C.card = u)

/-- Count clauses of the specified size containing a literal. -/
def literalOccurrences (A : Finset (Clause V)) (u : ℕ) (l : Literal V) : ℕ := by
  classical
  exact ((clausesOfSize A u).filter (fun C => l ∈ C)).card

omit [DecidableEq V] in
@[simp] theorem mem_clausesOfSize
    {V : Type uDepth1}

    {A : Finset (Clause V)} {u : ℕ} {C : Clause V} :
    C ∈ clausesOfSize A u ↔ C ∈ A ∧ C.card = u := by
  classical
  simp [clausesOfSize]
omit [DecidableEq V] in
theorem clausesOfSize_subset
    {V : Type uDepth1}

    (A : Finset (Clause V)) (u : ℕ) :
    clausesOfSize A u ⊆ A := Finset.filter_subset _ _
omit [DecidableEq V] in
theorem clausesOfSize_mono
    {V : Type uDepth1}

    {A B : Finset (Clause V)} (h : A ⊆ B) (u : ℕ) :
    clausesOfSize A u ⊆ clausesOfSize B u :=
  Finset.filter_subset_filter _ h
omit [DecidableEq V] in
theorem clausesOfSize_eq_self
    {V : Type uDepth1}

    (A : Finset (Clause V)) (u : ℕ)
    (h : ∀ C ∈ A, C.card = u) : clausesOfSize A u = A :=
  Finset.filter_eq_self.mpr h
omit [DecidableEq V] in
theorem clausesOfSize_eq_empty
    {V : Type uDepth1}

    (A : Finset (Clause V)) (u : ℕ)
    (h : ∀ C ∈ A, C.card ≠ u) : clausesOfSize A u = ∅ := by
  classical
  exact Finset.filter_eq_empty_iff.mpr (fun C hC => h C hC)
theorem literalOccurrences_mono {A B : Finset (Clause V)} (h : A ⊆ B)
    (u : ℕ) (l : Literal V) : literalOccurrences A u l ≤ literalOccurrences B u l := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (clausesOfSize_mono h u))

theorem literalOccurrences_le_card (A : Finset (Clause V)) (u : ℕ) (l : Literal V) :
    literalOccurrences A u l ≤ (clausesOfSize A u).card := by
  classical
  exact Finset.card_filter_le _ _

theorem literalOccurrences_one_le (A : Finset (Clause V)) (l : Literal V) :
    literalOccurrences A 1 l ≤ 1 := by
  classical
  unfold literalOccurrences
  apply Finset.card_le_one.mpr
  intro C hC D hD
  obtain ⟨hCA, hlC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hDA, hlD⟩ := Finset.mem_filter.mp hD
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (mem_clausesOfSize.mp hCA).2
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp (mem_clausesOfSize.mp hDA).2
  rw [hc] at hlC
  rw [hd] at hlD
  have hcd : c = d := (Finset.mem_singleton.mp hlC).symm.trans
    (Finset.mem_singleton.mp hlD)
  rw [hc, hd, hcd]

theorem clausesOfSize_union (A B : Finset (Clause V)) (u : ℕ) :
    clausesOfSize (A ∪ B) u = clausesOfSize A u ∪ clausesOfSize B u := by
  classical
  exact Finset.filter_union _ _ _

theorem literalOccurrences_union_le (A B : Finset (Clause V)) (u : ℕ) (l : Literal V) :
    literalOccurrences (A ∪ B) u l ≤
      literalOccurrences A u l + literalOccurrences B u l := by
  classical
  unfold literalOccurrences
  rw [clausesOfSize_union, Finset.filter_union]
  exact Finset.card_union_le _ _

theorem clausesOfSize_card_le [Fintype V] (A : Finset (Clause V)) (u n : ℕ)
    (hne : ∀ C ∈ clausesOfSize A u, C.Nonempty)
    (hocc : ∀ l, literalOccurrences A u l ≤ n) :
    (clausesOfSize A u).card ≤ (2 * Fintype.card V) * n := by
  classical
  calc
    (clausesOfSize A u).card = ∑ _C ∈ clausesOfSize A u, 1 :=
      Finset.card_eq_sum_ones _
    _ ≤ ∑ C ∈ clausesOfSize A u, C.card :=
      Finset.sum_le_sum (fun C hC => (hne C hC).card_pos)
    _ ≤ Fintype.card (Literal V) * n := Finset.sum_card_le hocc
    _ = (2 * Fintype.card V) * n := by
      simp only [Literal, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

theorem subsumed_by_clause_card_le (A : Finset (Clause V)) (u n : ℕ)
    (hocc : ∀ l, literalOccurrences A u l ≤ n)
    (D : Clause V) (hD : D.Nonempty) :
    ((clausesOfSize A u).filter (fun C => D ⊆ C)).card ≤ n := by
  classical
  obtain ⟨l, hl⟩ := hD
  have hsub : (clausesOfSize A u).filter (fun C => D ⊆ C) ⊆
      (clausesOfSize A u).filter (fun C => l ∈ C) := by
    intro C hC
    obtain ⟨hCA, hDC⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨hCA, hDC hl⟩
  exact (Finset.card_le_card hsub).trans (hocc l)

theorem deleted_clausesOfSize_card_le (A B R : Finset (Clause V)) (u n : ℕ)
    (hne : ∀ D ∈ B, D.Nonempty)
    (hocc : ∀ l, literalOccurrences A u l ≤ n)
    (hsub : R ⊆ clausesOfSize A u)
    (hcover : ∀ C ∈ R, ∃ D ∈ B, D ⊆ C) :
    R.card ≤ B.card * n := by
  classical
  let receiver := fun D : Clause V => (clausesOfSize A u).filter (fun C => D ⊆ C)
  have hR : R ⊆ B.biUnion receiver := by
    intro C hC
    obtain ⟨D, hDB, hDC⟩ := hcover C hC
    exact Finset.mem_biUnion.mpr
      ⟨D, hDB, Finset.mem_filter.mpr ⟨hsub hC, hDC⟩⟩
  exact (Finset.card_le_card hR).trans
    (Finset.card_biUnion_le_card_mul B receiver n
      (fun D hD => subsumed_by_clause_card_le A u n hocc D (hne D hD)))

/-- Clauses of the specified size subsumed by the selected batch. -/
def subsumedOfSize (A B : Finset (Clause V)) (u : ℕ) : Finset (Clause V) := by
  classical
  exact (clausesOfSize A u).filter (fun C => ∃ D ∈ B, D ⊆ C)

theorem subsumedOfSize_card_le (A B : Finset (Clause V)) (u n : ℕ)
    (hne : ∀ D ∈ B, D.Nonempty)
    (hocc : ∀ l, literalOccurrences A u l ≤ n) :
    (subsumedOfSize A B u).card ≤ B.card * n := by
  classical
  apply deleted_clausesOfSize_card_le A B (subsumedOfSize A B u) u n hne hocc
  · exact Finset.filter_subset _ _
  · intro C hC
    exact (Finset.mem_filter.mp hC).2

theorem clausesOfSize_update_balance
    (A B : Finset (Clause V)) (u : ℕ) (hfresh : Disjoint A B) :
    (clausesOfSize (B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C)) u).card +
        (subsumedOfSize A B u).card =
      (clausesOfSize A u).card + (clausesOfSize B u).card := by
  classical
  let P := fun C : Clause V => ∃ D ∈ B, D ⊆ C
  let S := (clausesOfSize A u).filter (fun C => ¬ P C)
  have hdecomp : clausesOfSize (B ∪ A.filter (fun C => ¬ P C)) u =
      clausesOfSize B u ∪ S := by
    ext C
    simp only [clausesOfSize, Finset.mem_filter, Finset.mem_union, S]
    constructor
    · rintro ⟨hC, hsize⟩
      rcases hC with hCB | ⟨hCA, hP⟩
      · exact Or.inl ⟨hCB, hsize⟩
      · exact Or.inr ⟨⟨hCA, hsize⟩, hP⟩
    · rintro (⟨hCB, hsize⟩ | ⟨⟨hCA, hsize⟩, hP⟩)
      · exact ⟨Or.inl hCB, hsize⟩
      · exact ⟨Or.inr ⟨hCA, hP⟩, hsize⟩
  have hdisj : Disjoint (clausesOfSize B u) S := by
    apply Finset.disjoint_left.mpr
    intro C hCB hCS
    exact Finset.disjoint_left.mp hfresh
      (Finset.mem_filter.mp (Finset.mem_filter.mp hCS).1).1
      (Finset.mem_filter.mp hCB).1
  have hpartition : (subsumedOfSize A B u).card + S.card =
      (clausesOfSize A u).card := by
    change ((clausesOfSize A u).filter P).card +
      ((clausesOfSize A u).filter (fun C => ¬ P C)).card = _
    have hfilters : Disjoint ((clausesOfSize A u).filter P)
        ((clausesOfSize A u).filter (fun C => ¬ P C)) := by
      apply Finset.disjoint_left.mpr
      intro C hC hC'
      exact (Finset.mem_filter.mp hC').2 (Finset.mem_filter.mp hC).2
    rw [← Finset.card_union_of_disjoint hfilters]
    apply congrArg Finset.card
    ext C
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hPC : P C <;> simp [hPC]
  change (clausesOfSize (B ∪ A.filter (fun C => ¬ P C)) u).card +
      (subsumedOfSize A B u).card = _
  rw [hdecomp, Finset.card_union_of_disjoint hdisj]
  calc
    (clausesOfSize B u).card + S.card + (subsumedOfSize A B u).card =
        ((subsumedOfSize A B u).card + S.card) + (clausesOfSize B u).card := by
      simp only [Nat.add_comm, Nat.add_left_comm]
    _ = _ := by rw [hpartition]

theorem literalOccurrences_update_le (A B : Finset (Clause V))
    (u : ℕ) (l : Literal V) :
    literalOccurrences (B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C)) u l ≤
      literalOccurrences A u l + literalOccurrences B u l := by
  classical
  have hsub : B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C) ⊆ A ∪ B := by
    intro C hC
    rcases Finset.mem_union.mp hC with hCB | hCA
    · exact Finset.mem_union.mpr (Or.inr hCB)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hCA).1)
  exact (literalOccurrences_mono hsub u l).trans
    (literalOccurrences_union_le A B u l)

end DepthThreeLowerBound

end

end Complexity
