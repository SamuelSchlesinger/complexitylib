/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Card
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Subset.Internal

/-!
# The finite subset split needed for a doubling step

Every set of size at most twice a bound is a disjoint union of two subsets
of size at most that bound. The statement includes zero bounds and
arbitrary finite cardinalities; no power-of-two or ambient finiteness
assumption is needed. The proof uses Mathlib's exact-cardinality subset
existence theorem and finite-set difference.
-/

public section

namespace Algebraic.Cutwidth.Extractor


/-- A subset within twice the capacity splits into disjoint parts within one capacity each. -/
theorem exists_union_of_card_le_two_mul {ι : Type*} [DecidableEq ι] (U : Finset ι) {k : Nat}
    (size : U.card ≤ 2 * k) :
    ∃ S T : Finset ι, S ⊆ U ∧ T ⊆ U ∧ Disjoint S T ∧ S ∪ T = U ∧
      S.card ≤ k ∧ T.card ≤ k :=
  Internal.exists_union_of_card_le_two_mul U size

end Algebraic.Cutwidth.Extractor
