/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.TightCircuit
public import Complexitylib.Algebraic.Basis.DeMorgan.Mask
public import Complexitylib.Algebraic.BooleanCube.Neighbors

/-!
# Two exceptions and input-cube adjacency

Two exceptions at adjacent inputs form an input subcube and have size at
most `n`. Two exceptions at distance at least two depend on every input and
are non-unate, so they require at least `n+1` native gates. Both claims also
hold for the complemented indicator.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- A Boolean function with the specified value at two inputs and the opposite value elsewhere. -/
def pairIndicator (left right : Fin n → Bool) (value : Bool) : ScalarFunction Bool n :=
  fun input => if input = left ∨ input = right then value else !value

private theorem flip_ne_other (left right : Fin n → Bool) (far : 1 < hammingDist left right)
    (i : Fin n) : BooleanCube.flip left i ≠ right := by
  intro equal
  have distance := BooleanCube.hammingDist_flip left i
  rw [equal] at distance
  omega

/-- Every input remains essential when the two exceptions are nonadjacent. -/
theorem pairIndicator_essential (left right : Fin n → Bool) (value : Bool)
    (far : 1 < hammingDist left right) (i : Fin n) : EssentialAt (pairIndicator left right value) i := by
  refine ⟨left, BooleanCube.flip left i, ?_, ?_⟩
  · intro j different
    simp [BooleanCube.flip, different]
  · have first := BooleanCube.flip_ne left i
    have second := flip_ne_other left right far i
    cases value <;> simp [pairIndicator, first, second]

/-- Two nonadjacent exceptions force contradictory influence directions at a differing input. -/
theorem pairIndicator_not_unate (left right : Fin n → Bool) (value : Bool)
    (far : 1 < hammingDist left right) : ¬Unate (pairIndicator left right value) := by
  obtain ⟨i, member⟩ := Finset.card_pos.mp (Nat.lt_trans (by decide : 0 < 1) far)
  have different : left i ≠ right i := (Finset.mem_filter.mp member).2
  have reversed : 1 < hammingDist right left := by simpa [hammingDist_comm] using far
  have firstSelf := Function.update_eq_self i left
  have secondSelf := Function.update_eq_self i right
  have firstValue : pairIndicator left right value left = value := by simp [pairIndicator]
  have secondValue : pairIndicator left right value right = value := by simp [pairIndicator]
  have firstFlip : pairIndicator left right value (BooleanCube.flip left i) = !value := by
    simp [pairIndicator, BooleanCube.flip_ne, flip_ne_other left right far i]
  have secondFlip : pairIndicator left right value (BooleanCube.flip right i) = !value := by
    simp [pairIndicator, BooleanCube.flip_ne, flip_ne_other right left reversed i]
  intro unate
  rcases unate i with increasing | decreasing
  · have first := increasing left
    have second := increasing right
    cases hl : left i <;> cases hr : right i <;> cases value <;>
      simp only [hl, hr, BooleanCube.flip, Bool.not_false, Bool.not_true]
        at firstSelf secondSelf firstFlip secondFlip <;>
      simp_all <;> exact (by decide : ¬((true : Bool) ≤ false)) (by assumption)
  · have first := decreasing left
    have second := decreasing right
    cases hl : left i <;> cases hr : right i <;> cases value <;>
      simp only [hl, hr, BooleanCube.flip, Bool.not_false, Bool.not_true]
        at firstSelf secondSelf firstFlip secondFlip <;>
      simp_all <;> exact (by decide : ¬((true : Bool) ≤ false)) (by assumption)

/-- Two nonadjacent exceptions, to either constant, need at least `n+1` native gates. -/
theorem complexity_pairIndicator_ge (left right : Fin n → Bool) (value : Bool)
    (far : 1 < hammingDist left right) : n + 1 ≤ complexity (pairIndicator left right value) :=
  complexity_ge_of_essential_nonunate _ (pairIndicator_essential left right value far)
    (pairIndicator_not_unate left right value far)

private theorem pair_eq_mask (point : Fin n → Bool) (i : Fin n) (value : Bool) :
    pairIndicator point (BooleanCube.flip point i) value =
      mask (Finset.univ.erase i) point value := by
  funext input
  have condition : (input = point ∨ input = BooleanCube.flip point i) ↔
      ∀ j ∈ Finset.univ.erase i, input j = point j := by
    constructor
    · rintro (rfl | rfl) j member
      · rfl
      · exact Function.update_of_ne (Finset.mem_erase.mp member).1 _ _
    · intro agree
      by_cases same : input i = point i
      · left
        funext j
        by_cases equal : j = i
        · simpa [equal] using same
        · exact agree j (by simp [equal])
      · right
        funext j
        by_cases equal : j = i
        · subst j
          cases hi : input i <;> cases hp : point i <;> simp_all [BooleanCube.flip]
        · simpa [BooleanCube.flip, equal] using agree j (by simp [equal])
  simp only [pairIndicator, mask, condition]

/-- Adjacent exceptions, to either constant, fit within the input-width budget. -/
theorem complexity_pairIndicator_le_of_adjacent (positive : 0 < n)
    (left right : Fin n → Bool) (value : Bool) (adjacent : BooleanCube.graph.Adj left right) :
    complexity (pairIndicator left right value) ≤ n := by
  obtain ⟨i, rfl⟩ := (BooleanCube.adjacent_iff_flip left right).mp adjacent
  rw [pair_eq_mask]
  have bound := complexity_mask_le (Finset.univ.erase i) left value
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at bound
  omega

/-- At the input-width budget, distinct pairs are cheap exactly when their inputs are adjacent. -/
theorem complexity_pairIndicator_le_iff (positive : 0 < n)
    (left right : Fin n → Bool) (value : Bool) (different : left ≠ right) :
    complexity (pairIndicator left right value) ≤ n ↔ BooleanCube.graph.Adj left right := by
  constructor
  · intro small
    have nonzero : hammingDist left right ≠ 0 := by
      simpa using different
    by_contra notAdjacent
    have far : 1 < hammingDist left right := by change hammingDist left right ≠ 1 at notAdjacent; omega
    have lower := complexity_pairIndicator_ge left right value far
    omega
  · exact complexity_pairIndicator_le_of_adjacent positive left right value

end Algebraic.DeMorgan
