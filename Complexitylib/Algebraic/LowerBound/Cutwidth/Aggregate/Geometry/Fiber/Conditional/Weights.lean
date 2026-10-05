/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Entropy.Internal

/-!
# Message weights with several constant and biased classes

Frozen coordinates may have different constant values. Two disjoint biased classes
and the remaining Boolean coordinates reconstruct the full message without any
independence assumption on their outputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Entropy
open scoped BigOperators Classical

/-- Reconstruct a message from two weighted classes and the remaining nonconstant bits. -/
noncomputable def keyWeightBoundOfConstantClasses {X : Type*} [Fintype X] {g : ℕ}
    (message : X → Fin g → Bool) (T W O : Finset (Fin g))
    (disjoint : Disjoint T W) (outputs : Disjoint (T ∪ W) O)
    (value : Fin g → Bool) (constant : ∀ i ∈ O, ∀ x, message x i = value i) {cost : ℝ}
    (classes : WeightBound (fun x => ((fun i : T => message x i),
      fun i : W => message x i)) cost) :
    WeightBound message
      (cost + ((g : ℝ) - T.card - W.card - O.card) * Real.log 2) := by
  let R := {i : Fin g // i ∉ (T ∪ W) ∪ O}
  have other := WeightBound.pi fun i : R => WeightBound.boolean (fun x => message x i)
  let merge (z : ((T → Bool) × (W → Bool)) × (R → Bool)) (i : Fin g) :=
    if ht : i ∈ T then z.1.1 ⟨i, ht⟩ else
      if hw : i ∈ W then z.1.2 ⟨i, hw⟩ else
        if ho : i ∈ O then value i else z.2 ⟨i, by simp [ht, hw, ho]⟩
  have merged := (classes.prod other).map merge
  have remainder : Fintype.card R = g - ((T ∪ W) ∪ O).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_subtype_compl fun i : Fin g => i ∈ (T ∪ W) ∪ O
  have counts : T.card + W.card + O.card + Fintype.card R = g := by
    have bound := Finset.card_le_univ ((T ∪ W) ∪ O)
    rw [Finset.card_union_of_disjoint outputs, Finset.card_union_of_disjoint disjoint,
      Fintype.card_fin] at bound
    rw [remainder, Finset.card_union_of_disjoint outputs,
      Finset.card_union_of_disjoint disjoint]
    lia
  have realCounts : (T.card : ℝ) + W.card + O.card + Fintype.card R = g := by
    exact_mod_cast counts
  convert merged using 1
  · funext x i
    dsimp only [merge]
    split
    · rfl
    · split
      · rfl
      · split
        · exact constant i (by assumption) x
        · rfl
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← realCounts]
    ring

/-- Frozen narrow summaries and separately constant outputs have disjoint costs. -/
noncomputable def keyWeightBoundWithFrozen {X : Type*} [Fintype X] {g : ℕ}
    (message : X → Fin g → Bool) (T W S O : Finset (Fin g))
    (selected : S ⊆ T) (disjoint : Disjoint T W) (outputs : Disjoint (T ∪ W) O)
    (frozen : ∀ i ∈ S, ∀ x, message x i = false)
    (constant : ∀ i ∈ O, ∀ x, message x i = true) {ct cw : ℝ}
    (narrow : WeightBound (fun x => fun i : ↥(T \ S) => message x i) ((T \ S).card * ct))
    (wide : WeightBound (fun x => fun i : W => message x i) (W.card * cw)) :
    WeightBound message
      (((g : ℝ) - S.card - O.card) * Real.log 2 -
        ((T.card : ℝ) - S.card) * (Real.log 2 - ct) - W.card * (Real.log 2 - cw)) := by
  have apart : Disjoint (T \ S) W := disjoint.mono_left Finset.sdiff_subset
  have outside : Disjoint ((T \ S) ∪ W) (S ∪ O) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    rcases Finset.mem_union.mp hi with ht | hw
    · rcases Finset.mem_union.mp hj with hs | ho
      · exact (Finset.mem_sdiff.mp ht).2 hs
      · exact Finset.disjoint_left.mp outputs (Finset.mem_union_left _
          (Finset.mem_sdiff.mp ht).1) ho
    · rcases Finset.mem_union.mp hj with hs | ho
      · exact Finset.disjoint_left.mp disjoint (selected hs) hw
      · exact Finset.disjoint_left.mp outputs (Finset.mem_union_right _ hw) ho
  have const (i : Fin g) (hi : i ∈ S ∪ O) (x : X) :
      message x i = if i ∈ S then false else true := by
    by_cases hs : i ∈ S
    · simp [hs, frozen i hs x]
    · simpa [hs] using constant i ((Finset.mem_union.mp hi).resolve_left hs) x
  have bound := keyWeightBoundOfConstantClasses message (T \ S) W (S ∪ O)
    apart outside (fun i => if i ∈ S then false else true) const (narrow.prod wide)
  have so : Disjoint S O := outputs.mono_left
    (fun i hi => Finset.mem_union_left _ (selected hi))
  have card : ((T \ S).card : ℝ) = T.card - S.card := by
    rw [Finset.card_sdiff_of_subset selected, Nat.cast_sub (Finset.card_le_card selected)]
  rw [Finset.card_union_of_disjoint so, Nat.cast_add, card] at bound
  convert bound using 1
  ring

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional
