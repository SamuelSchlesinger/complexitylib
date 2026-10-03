/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Mathlib.Data.Finset.SymmDiff

/-!
# Helpfulness of a vertex move

Monien and Preis measure a move by the crossing edges it removes minus
those it creates. Integer subtraction retains the cost of an unhelpful move.
When the moved set lies in one side, this is their helpfulness definition.
The definition also applies when vertices are flipped on both sides.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- The signed cut reduction obtained by flipping the vertices in `X`.
The intersection counts crossing edges removed by the flip; the difference
counts previously internal edges that become crossing. For `X ⊆ S`, this
is the helpfulness of moving `X` from side `S` to its complement. -/
noncomputable def helpfulness {W : Type} [Fintype W] (H : SimpleGraph W)
    (S X : Finset W) : ℤ :=
  ((H.cutFinset X ∩ H.cutFinset S).card : ℤ) - (H.cutFinset X \ H.cutFinset S).card

end Algebraic.Cutwidth
