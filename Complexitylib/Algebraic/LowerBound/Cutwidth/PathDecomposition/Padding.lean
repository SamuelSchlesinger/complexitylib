/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Padding.Internal

/-!
# Padding path decompositions by a boundary

Insert a fixed boundary in every bag and at both ends. The added boundary
may overlap the induced copy of the original graph.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

/-- Extend an induced copy's decomposition by adding `X` to all bags and as
both endpoints. Every vertex outside the copy must lie in `X`. -/
theorem exists_pad {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (D : PathDecomposition G) (f : G ↪g H) (X : Finset W)
    (cover : ∀ w, w ∈ Set.range f ∨ w ∈ X) {b : Nat}
    (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ E : PathDecomposition H, E.StartsAt X ∧ E.EndsAt X ∧
      ∀ i, (E.bag i).card ≤ X.card + b :=
  Internal.exists_pad D f X cover bound

end Algebraic.Cutwidth.PathDecomposition
