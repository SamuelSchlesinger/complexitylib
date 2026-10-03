/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Card

/-!
# Splitting a bounded finite subset into two smaller parts

Choose a subset of size `k` when the original set is larger, and use its
complement for the second part. This elementary cardinality argument also
covers `k = 0` and sets smaller than the target capacity.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal


theorem exists_union_of_card_le_two_mul {ι : Type*} [DecidableEq ι] (U : Finset ι) {k : Nat}
    (size : U.card ≤ 2 * k) :
    ∃ S T : Finset ι, S ⊆ U ∧ T ⊆ U ∧ Disjoint S T ∧ S ∪ T = U ∧
      S.card ≤ k ∧ T.card ≤ k := by
  classical
  by_cases small : U.card ≤ k
  · refine ⟨U, ∅, Finset.Subset.refl _, Finset.empty_subset _, ?_, ?_, small, ?_⟩ <;> simp
  · obtain ⟨S, subset, card⟩ := Finset.exists_subset_card_eq (show k ≤ U.card by lia)
    refine ⟨S, U \ S, subset, Finset.sdiff_subset, Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset subset, card.le, ?_⟩
    rw [Finset.card_sdiff_of_subset subset, card]
    lia

end Algebraic.Cutwidth.Extractor.Internal
