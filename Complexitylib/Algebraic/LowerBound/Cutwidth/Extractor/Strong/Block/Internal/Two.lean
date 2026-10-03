/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Internal
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Pair weights as two-block sources

Reindexing a pair by its two coordinates preserves normalization. Its
one-coordinate prefix mass is the first marginal, so the two prefix caps
are exactly the unconditional first cap and the conditional second cap.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem blockSource_two_probability_iff {α : Type*} [Fintype α] (p : α × α → ℝ) :
    IsProbabilityWeight (fun x : Fin 2 → α => p (x 0, x 1)) ↔
      IsProbabilityWeight p := by
  have mass : (∑ x : Fin 2 → α, p (x 0, x 1)) = ∑ ab, p ab :=
    (finTwoArrowEquiv α).sum_comp p
  constructor
  · rintro ⟨nonnegative, normalized⟩
    refine ⟨fun ab => ?_, mass.symm.trans normalized⟩
    simpa using nonnegative ![ab.1, ab.2]
  · rintro ⟨nonnegative, normalized⟩
    exact ⟨fun x => nonnegative (x 0, x 1), mass.trans normalized⟩

theorem blockPrefixWeight_two_one {α : Type*} [Fintype α]
    (p : α × α → ℝ) (u : Fin 1 → α) :
    blockPrefixWeight (fun x : Fin 2 → α => p (x 0, x 1)) (by decide : 1 ≤ 2) u =
      firstWeight p (u 0) := by
  classical
  unfold blockPrefixWeight mapWeight
  calc
    _ = ∑ ab : α × α, if ab.1 = u 0 then p ab else 0 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv α)
      intro x
      by_cases same : x 0 = u 0
      · have prefix_eq : blockPrefix (by decide : 1 ≤ 2) x = u := by
          funext j
          have hj : j = 0 := Fin.eq_zero j
          subst j
          exact same
        rw [ite_eq_left prefix_eq,
          ite_eq_left (show ((finTwoArrowEquiv α) x).1 = u 0 from same)]
        rfl
      · have prefix_ne : blockPrefix (by decide : 1 ≤ 2) x ≠ u := by
          intro equality
          exact same (congrFun equality 0)
        rw [ite_eq_right prefix_ne,
          ite_eq_right (show ((finTwoArrowEquiv α) x).1 ≠ u 0 from same)]
    _ = firstWeight p (u 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [firstWeight]

theorem blockSource_two_iff {α : Type*} [Fintype α] (p : α × α → ℝ) (K : Nat) :
    IsBlockSource (fun x : Fin 2 → α => p (x 0, x 1)) K ↔
      IsProbabilityWeight p ∧ CappedWeight (firstWeight p) K ∧
        ∀ a b, (K : ℝ) * p (a, b) ≤ firstWeight p a := by
  constructor
  · intro source
    refine ⟨(blockSource_two_probability_iff p).mp source.1, ?_, ?_⟩
    · intro a
      simpa only [blockPrefixWeight_two_one, blockPrefixWeight_zero, source.1.2] using
        source.2 0 (fun _ => a)
    · intro a b
      simpa [blockPrefixWeight_self, blockPrefixWeight_two_one, blockPrefix] using
        source.2 1 ![a, b]
  · rintro ⟨probability, first_cap, second_cap⟩
    have normalized := (blockSource_two_probability_iff p).mpr probability
    refine ⟨normalized, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · intro u
      simpa only [blockPrefixWeight_two_one, blockPrefixWeight_zero, normalized.2] using
        first_cap (u 0)
    · intro u
      simpa [blockPrefixWeight_self, blockPrefixWeight_two_one, blockPrefix] using
        second_cap (u 0) (u 1)

end Algebraic.Cutwidth.Extractor.Internal
