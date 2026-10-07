/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Data.Fintype.BigOperators

/-!
# Sensitivity separation: fixed coordinates

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/FixedCoordinates.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- Exact finite counting when a specified set of coordinates is fixed. -/

noncomputable section
open scoped Classical

namespace Internal

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

/-- Functions with prescribed coordinates are equivalent to functions on the remaining
coordinates. -/
def fixedCoordinatesEquiv (s : Finset α) (v : α → β) :
    {f : α → β // ∀ i ∈ s, f i = v i} ≃ ({i : α // i ∉ s} → β) where
  toFun f i := f.val i.val
  invFun f := ⟨fun i => if h : i ∈ s then v i else f ⟨i,h⟩, by
    intro i hi
    simp only [dite_eq_left hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp only [dite_eq_left hi]
      exact (f.property i hi).symm
    · simp only [dite_eq_right hi]
  right_inv f := by
    funext i
    simp only [dite_eq_right i.property]

theorem card_fixedCoordinates (s : Finset α) (v : α → β)
    [DecidablePred (fun f : α → β => ∀ i ∈ s, f i = v i)] :
    (Finset.univ.filter fun f : α → β => ∀ i ∈ s, f i = v i).card =
      Fintype.card β ^ (Fintype.card α - s.card) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (fixedCoordinatesEquiv s v), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe]

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity
