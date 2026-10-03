/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs
public import Mathlib.Data.Nat.Log
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Endpoint.Internal

/-!
# Prescribed endpoints in subcubic graphs

The endpoint induction of Fomin and Høie's *Pathwidth of cubic graphs and
exact algorithms* (2006), Lemma 4, using the elementary base-two tree bound.
This finite result has no bisection hypothesis. `Bisection` uses it to prove
the cubic pathwidth theorem from the Monien–Preis bisection hypothesis.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

/-- Every finite graph of maximum degree three has a decomposition ending
at any prescribed set `X`, with the stated bag-size bound. The base-two
logarithmic remainder suffices for the asymptotic cubic pathwidth theorem. -/
theorem exists_subcubic_endsAt {W : Type} [Fintype W] (H : SimpleGraph W)
    (degree : ∀ v, H.degree v ≤ 3) (X : Finset W) :
    ∃ D : PathDecomposition H, D.EndsAt X ∧ ∀ i,
      (D.bag i).card ≤
        max X.card (Fintype.card W / 3 + 1) + Nat.clog 2 (Fintype.card W) + 1 :=
  Internal.exists_subcubic_endpoint H degree X

end Algebraic.Cutwidth.PathDecomposition
