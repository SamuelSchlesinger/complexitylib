/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.TournamentCounts

/-!
# Sensitivity separation: labeling constraints

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/LabelingConstraints.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- The labeling constraints are exactly fixed values on the internal edges. -/

noncomputable section
open scoped Classical

namespace Internal.Tournament
variable {k : ℕ} (T : Tournament k)

theorem mem_internalEdges {I : Finset (Fin k)} {p : Fin k × Fin k} :
    p ∈ T.internalEdges I ↔ (p.1 ∈ I ∧ p.2 ∈ I) ∧ T.Adj p.1 p.2 := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_product]

theorem labelingConstraint_iff {α β : Type} [Nonempty α]
    (s : Finset α) (v : α → Fin k) (m : α → β) (hv : Function.Injective v)
    (A : (Fin k × Fin k) → β) :
    (∀ i ∈ s, ∀ j ∈ s, T.Adj (v i) (v j) → A (v i,v j) = m j) ↔
      ∀ p ∈ T.internalEdges (s.image v), A p = m (Function.invFun v p.2) := by
  constructor
  · intro h p hp
    obtain ⟨⟨hp₁,hp₂⟩,ha⟩ := T.mem_internalEdges.mp hp
    obtain ⟨i,hi,hvi⟩ := Finset.mem_image.mp hp₁
    obtain ⟨j,hj,hvj⟩ := Finset.mem_image.mp hp₂
    have he : p = (v i,v j) := Prod.ext hvi.symm hvj.symm
    subst p
    rw [Function.leftInverse_invFun hv j]
    exact h i hi j hj ha
  · intro h i hi j hj ha
    have hp : (v i,v j) ∈ T.internalEdges (s.image v) :=
      T.mem_internalEdges.mpr ⟨⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,
        Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩,ha⟩
    simpa only [Function.leftInverse_invFun hv j] using h (v i,v j) hp

end Internal.Tournament

end

end Complexity.BooleanAnalysis.Sensitivity
