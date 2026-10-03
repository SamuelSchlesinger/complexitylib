/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Clusters.Density.Internal

/-!
# Bounded positive sets from red-edge density

Monien and Preis's red/black lemma supplies a bounded set with more
internal red edges than external black edges when red density exceeds
one half. We prove that lemma using bounded connected partitions and
exact incidence counts. Small black components are attached whole, so
overlapping attachments preserve the witness and the size bound.

Source: Burkhard Monien and Robert Preis, *Upper bounds on the bisection
width of 3- and 4-regular graphs*, Journal of Discrete Algorithms 4 (2006),
475–498, https://doi.org/10.1016/j.jda.2005.12.009.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

/-- In a graph of combined red-plus-black degree three, the finite density
inequality forces a positive set of at most `3 M (1 + 3 M)` vertices.
The red graph may have parallel edges; each edge identity counts separately. -/
theorem exists_positive_of_density (loopless : R.Loopless)
    (degree : ∀ v, B.degree v + R.degree v = 3) (M : Nat) (positive : 0 < M)
    (density : (M + 4) * Fintype.card V < 2 * M * Fintype.card E) :
    ∃ X : Finset V, X.card ≤ 3 * M * (1 + 3 * M) ∧ Positive B R X :=
  Internal.exists_positive_of_density B R loopless degree M positive density

/-- Red density above `1/2 + ε` gives a positive set of at most
`3 M (1 + 3 M)` vertices whenever `2 ≤ ε M` and `M > 0`. -/
theorem exists_positive_of_red_density (loopless : R.Loopless)
    (degree : ∀ v, B.degree v + R.degree v = 3) (M : Nat) (positive : 0 < M)
    {ε : ℝ} (budget : 2 ≤ ε * M)
    (density : (1 / 2 + ε) * Fintype.card V < Fintype.card E) :
    ∃ X : Finset V, X.card ≤ 3 * M * (1 + 3 * M) ∧ Positive B R X :=
  Internal.exists_positive_of_red_density B R loopless degree M positive budget density

end Algebraic.Cutwidth.Bisection.RedBlack
