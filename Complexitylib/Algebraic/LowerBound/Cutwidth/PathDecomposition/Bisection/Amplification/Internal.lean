/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement

/-!
# Accumulating helpful moves

The first step of Monien and Preis's bisection argument applies a bounded
helpful-set lemma until the total cut reduction reaches a chosen target.
The density margin preserves the local lemma's hypothesis at every step.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical symmDiff

theorem exists_helpful_set_of_margin {W : Type} [Fintype W] (H : SimpleGraph W)
    (S : Finset W) {a : ℝ} (ha : 0 ≤ a) (M k : Nat)
    (margin : a * S.card + k < (H.cutFinset S).card)
    (find : ∀ T ⊆ S, a * T.card < (H.cutFinset T).card →
      ∃ X ⊆ T, X.card ≤ M ∧ 1 ≤ helpfulness H T X) :
    ∃ X ⊆ S, X.card ≤ k * M ∧ (k : ℤ) ≤ helpfulness H S X := by
  have produce (i : Nat) : ∃ X ⊆ S, X.card ≤ i * M ∧
      ((k : ℤ) ≤ helpfulness H S X ∨ (i : ℤ) ≤ helpfulness H S X) := by
    induction i with
    | zero =>
      refine ⟨∅, Finset.empty_subset _, by simp, Or.inr ?_⟩
      simp [helpfulness, SimpleGraph.cutFinset]
    | succ i ih =>
      obtain ⟨X, hX, sizeX, progress⟩ := ih
      by_cases done : (k : ℤ) ≤ helpfulness H S X
      · exact ⟨X, hX, sizeX.trans (Nat.mul_le_mul_right M (Nat.le_succ i)), Or.inl done⟩
      have gain : (i : ℤ) ≤ helpfulness H S X := progress.resolve_left done
      have below : helpfulness H S X < (k : ℤ) := lt_of_not_ge done
      have gainEq : (helpfulness H S X : ℝ) =
          (H.cutFinset S).card - (H.cutFinset (S \ X)).card := by
        exact_mod_cast helpfulness_eq_sub_sdiff H hX
      have belowReal : (helpfulness H S X : ℝ) < k := by exact_mod_cast below
      have sideSize : ((S \ X).card : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : S \ X ⊆ S)
      have density : a * (S \ X).card < (H.cutFinset (S \ X)).card := by
        have := mul_le_mul_of_nonneg_left sideSize ha
        linarith
      obtain ⟨Y, hY, sizeY, helpful⟩ := find (S \ X) Finset.sdiff_subset density
      have disjoint : Disjoint X Y := Finset.disjoint_left.mpr
        (fun _ hv hw => (Finset.mem_sdiff.mp (hY hw)).2 hv)
      have gainUnion : helpfulness H S (X ∪ Y) =
          helpfulness H S X + helpfulness H (S \ X) Y := by
        rw [← Finset.symmDiff_eq_union disjoint, helpfulness_add,
          symmDiff_comm S X, symmDiff_of_le hX]
      refine ⟨X ∪ Y, Finset.union_subset hX (hY.trans Finset.sdiff_subset), ?_, Or.inr ?_⟩
      · calc (X ∪ Y).card ≤ X.card + Y.card := Finset.card_union_le _ _
          _ ≤ i * M + M := Nat.add_le_add sizeX sizeY
          _ = (i + 1) * M := by ring
      · rw [gainUnion]
        push_cast
        lia
  obtain ⟨X, hX, sizeX, progress⟩ := produce k
  exact ⟨X, hX, sizeX, progress.elim id id⟩

end Algebraic.Cutwidth.Bisection.Internal
