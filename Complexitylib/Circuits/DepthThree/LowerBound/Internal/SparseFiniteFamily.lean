/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card

/-!
# Unrestricted depth-three lower bound: sparse finite family

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseFiniteFamily.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

variable {α : Type uDepth1}

/-- The finite family of minimal sparse CNFs used as tests. -/
noncomputable def sparseMinimalFamily (A : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact A.filter (fun C => ∀ D ∈ A, D ⊆ C → C ⊆ D)

theorem mem_sparseMinimalFamily {A : Finset (Finset α)} {C : Finset α} :
    C ∈ sparseMinimalFamily A ↔ C ∈ A ∧ ∀ D ∈ A, D ⊆ C → C ⊆ D := by
  classical
  simp only [sparseMinimalFamily, Finset.mem_filter]

theorem sparseMinimalFamily_subset (A : Finset (Finset α)) :
    sparseMinimalFamily A ⊆ A := by
  intro C hC
  exact (mem_sparseMinimalFamily.mp hC).1

theorem sparseMinimalFamily_antichain (A : Finset (Finset α)) :
    ∀ C ∈ sparseMinimalFamily A, ∀ D ∈ sparseMinimalFamily A, C ⊆ D → C = D := by
  intro C hC D hD hCD
  apply Finset.Subset.antisymm hCD
  exact (mem_sparseMinimalFamily.mp hD).2 C
    (sparseMinimalFamily_subset A hC) hCD

theorem exists_mem_sparseMinimalFamily_subset {A : Finset (Finset α)}
    {C : Finset α} (hC : C ∈ A) :
    ∃ D ∈ sparseMinimalFamily A, D ⊆ C := by
  classical
  let candidates := A.filter (fun D => D ⊆ C)
  have hne : candidates.Nonempty := by
    refine ⟨C, ?_⟩
    exact Finset.mem_filter.mpr ⟨hC, Finset.Subset.refl _⟩
  obtain ⟨D, hD, hmin⟩ := candidates.exists_min_image Finset.card hne
  have hDA : D ∈ A := (Finset.mem_filter.mp hD).1
  have hDC : D ⊆ C := (Finset.mem_filter.mp hD).2
  refine ⟨D, mem_sparseMinimalFamily.mpr ⟨hDA, ?_⟩, hDC⟩
  intro E hEA hED
  have hEc : E ∈ candidates :=
    Finset.mem_filter.mpr ⟨hEA, Finset.Subset.trans hED hDC⟩
  have hEq : E = D := Finset.eq_of_subset_of_card_le hED (hmin E hEc)
  exact Finset.subset_of_eq hEq.symm

theorem forall_sparseMinimalFamily_iff (A : Finset (Finset α))
    (P : Finset α → Prop)
    (hP : ∀ {C D}, C ⊆ D → P C → P D) :
    (∀ C ∈ sparseMinimalFamily A, P C) ↔ ∀ C ∈ A, P C := by
  constructor
  · intro h C hC
    obtain ⟨D, hD, hDC⟩ := exists_mem_sparseMinimalFamily_subset hC
    exact hP hDC (h D hD)
  · intro h C hC
    exact h C (sparseMinimalFamily_subset A hC)

theorem sparseMinimalFamily_empty :
    sparseMinimalFamily (∅ : Finset (Finset α)) = ∅ := by
  classical
  simp [sparseMinimalFamily]

end DepthThreeLowerBound

end Complexity
