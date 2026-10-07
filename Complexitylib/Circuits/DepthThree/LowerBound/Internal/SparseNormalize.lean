/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseFiniteFamily

/-!
# Unrestricted depth-three lower bound: sparse normalize

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseNormalize.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

variable {V : Type uDepth1}

theorem Clause.eval_of_not_normalized {C : Clause V} (hC : ¬ C.Normalized)
    (x : Cube V) : C.eval x = true := by
  classical
  by_contra hx
  apply hC
  intro v hf ht
  cases hv : x v with
  | false => exact hx (Clause.eval_eq_true C x |>.mpr ⟨(v, false), hf, hv⟩)
  | true => exact hx (Clause.eval_eq_true C x |>.mpr ⟨(v, true), ht, hv⟩)

theorem CNF.eval_of_empty_mem {H : CNF V} (hH : ∅ ∈ H) (x : Cube V) :
    H.eval x = false := by
  cases hx : H.eval x with
  | false => rfl
  | true =>
    have he := (CNF.eval_eq_true H x).mp hx ∅ hH
    simp only [Clause.eval_empty, Bool.false_eq_true] at he

/-- Normalize a CNF into its finite family of minimal clauses. -/
noncomputable def sparseNormalizedFamily (H : CNF V) : Finset (Clause V) := by
  classical
  exact H.toFinset.filter Clause.Normalized

theorem mem_sparseNormalizedFamily {H : CNF V} {C : Clause V} :
    C ∈ sparseNormalizedFamily H ↔ C ∈ H ∧ C.Normalized := by
  classical
  simp [sparseNormalizedFamily]

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem sparseNormalizedFamily_eval (H : CNF V) (x : Cube V) :
    CNF.eval (sparseNormalizedFamily H).toList x = H.eval x := by
  classical
  apply bool_eq_of_true_iff
  simp only [CNF.eval_eq_true, Finset.mem_toList]
  constructor
  · intro h C hC
    by_cases hn : C.Normalized
    · exact h C (mem_sparseNormalizedFamily.mpr ⟨hC, hn⟩)
    · exact Clause.eval_of_not_normalized hn x
  · intro h C hC
    exact h C (mem_sparseNormalizedFamily.mp hC).1

theorem sparseMinimalFamily_eval (A : Finset (Clause V)) (x : Cube V) :
    CNF.eval (sparseMinimalFamily A).toList x = CNF.eval A.toList x := by
  classical
  apply bool_eq_of_true_iff
  simp only [CNF.eval_eq_true, Finset.mem_toList]
  exact forall_sparseMinimalFamily_iff A (fun C => Clause.eval C x = true)
    (fun hCD hx => Clause.eval_mono hCD hx)

/-- A normalized clause family with its width and semantic guarantees. -/
structure SparseNormalization (H : CNF V) (b : ℕ) where
  /-- The currently active clauses. -/
  active : Finset (Clause V)
  normalized : ∀ C ∈ active, C.Normalized
  nonempty : ∀ C ∈ active, C.Nonempty
  antichain : ∀ C ∈ active, ∀ D ∈ active, C ⊆ D → C = D
  width_le : ∀ C ∈ active, C.width ≤ b
  eval_eq : ∀ x, CNF.eval active.toList x = H.eval x

/-- Normalize a CNF that contains no empty clause. -/
noncomputable def sparseNormalizeOfNoEmpty (H : CNF V) {b : ℕ}
    (hwidth : H.WidthAtMost b) (hempty : (∅ : Clause V) ∉ H) :
    SparseNormalization H b where
  active := sparseMinimalFamily (sparseNormalizedFamily H)
  normalized := by
    intro C hC
    exact (mem_sparseNormalizedFamily.mp
      (sparseMinimalFamily_subset _ hC)).2
  nonempty := by
    intro C hC
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hzero
    apply hempty
    have hCH := (mem_sparseNormalizedFamily.mp
      (sparseMinimalFamily_subset _ hC)).1
    simpa only [hzero] using hCH
  antichain := sparseMinimalFamily_antichain _
  width_le := by
    intro C hC
    exact hwidth C ((mem_sparseNormalizedFamily.mp
      (sparseMinimalFamily_subset _ hC)).1)
  eval_eq := by
    intro x
    exact (sparseMinimalFamily_eval (sparseNormalizedFamily H) x).trans
      (sparseNormalizedFamily_eval H x)

theorem exists_sparseNormalization_or_false (H : CNF V) {b : ℕ}
    (hwidth : H.WidthAtMost b) :
    (∀ x, H.eval x = false) ∨ Nonempty (SparseNormalization H b) := by
  classical
  by_cases hempty : (∅ : Clause V) ∈ H
  · exact Or.inl (CNF.eval_of_empty_mem hempty)
  · exact Or.inr ⟨sparseNormalizeOfNoEmpty H hwidth hempty⟩

end DepthThreeLowerBound

end Complexity
