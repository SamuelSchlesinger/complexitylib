/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Amplification.Internal

/-!
# From bounded helpful sets to a prescribed cut reduction

This is the accumulation step in Monien and Preis's cubic bisection proof.
It assumes the local helpful-set lemma and proves the iteration, size bound,
and preservation of the density condition. It does not establish the local
helpful-set lemma itself.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

/-- If every remaining side of density above `a` has a helpful set of size
at most `M`, a margin of `k` yields a union of at most `k M` vertices whose
helpfulness is at least `k`. The last move may exceed the target reduction. -/
theorem exists_helpful_set_of_margin {W : Type} [Fintype W] (H : SimpleGraph W)
    (S : Finset W) {a : ℝ} (ha : 0 ≤ a) (M k : Nat)
    (margin : a * S.card + k < (H.cutFinset S).card)
    (find : ∀ T ⊆ S, a * T.card < (H.cutFinset T).card →
      ∃ X ⊆ T, X.card ≤ M ∧ 1 ≤ helpfulness H T X) :
    ∃ X ⊆ S, X.card ≤ k * M ∧ (k : ℤ) ≤ helpfulness H S X :=
  Internal.exists_helpful_set_of_margin H S ha M k margin find

end Algebraic.Cutwidth.Bisection
