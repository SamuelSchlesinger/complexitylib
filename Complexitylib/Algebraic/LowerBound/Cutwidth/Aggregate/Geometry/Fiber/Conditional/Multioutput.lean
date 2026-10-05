/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Message
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Multioutput

/-!
# Conditional entropy for all outputs of a permutation

The full primary message is injective. Its majority event retains biased narrow
and wide conjunction summaries while designated conjunction-output summaries are
constant. Independent nonaffine output components supply the extra output charge.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Algebraic.Aggregate.Geometry Entropy
open scoped Classical

/-- On a permutation, the majority-conditioned primary message remains injective. -/
theorem input_add_conditional_le_size_sub_outputConjunctionCount {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (S : Finset (Fin c.size))
    (eligible : S ⊆ Algebraic.Aggregate.Geometry.Shared.exactTwo c.program)
    (disjoint : (S : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    (n : ℝ) + (messageLoss - pairSaving) * S.card +
      pairSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
      tripleSaving * (Joint.retainedWide c.program Finset.univ).card ≤
        c.size - outputConjunctionCount c := by
  let U : Finset (Fin n) := Finset.univ
  let O := outputConjunctions c
  let full (x : U → Bool) := key c.program U (glue U x (fun _ => false))
  have selected : S ⊆ Joint.retainedTwo c.program U := by
    simpa only [U, retainedTwo_univ] using eligible
  choose edge left right forced using fun i : S =>
    exists_edge_of_selectedPair (c.program.lines i.val) U
      (Finset.mem_filter.mp (selected i.property)).2.selectedPair
  have endpoints := endpoint_injective_of_disjoint c.program U S edge left right disjoint
  have outside : Disjoint (Joint.retainedTwo c.program U ∪ Joint.retainedWide c.program U) O := by
    apply Finset.disjoint_left.mpr
    intro i hi ho
    have empty := primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral i ho
    have pair : SelectedPair (c.program.lines i) U := by
      rcases Finset.mem_union.mp hi with ht | hw
      · exact (Finset.mem_filter.mp ht).2.selectedPair
      · exact (Finset.mem_filter.mp hw).2.selectedPair
    have marked := pair.multiPrimary
    simp [multiPrimary, empty] at marked
  have constant (i : Fin c.size) (hi : i ∈ O) (x : U → Bool) : full x i = true := by
    exact lineSummary_eq_true_of_primaryInputs_eq_empty _ (Finset.mem_filter.mp hi).2
      (primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral i hi)
      (glue U x (fun _ => false))
  have full_injective : Function.Injective full := by
    intro x y same
    have equal := key_injective_of_permutation c bijective
      (by intro i j; simpa using nonliteral i j false) same
    funext i
    simpa using congrFun equal i.val
  have fibers (y : Fin c.size → Bool) :
      (Finset.univ.filter fun x : ↥(majorityInputs edge) => full x.val = y).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx z hz
    apply Subtype.ext
    apply full_injective
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm
  have certificate := majorityKeyWeightBound c.program U S selected edge endpoints
    (fun x i => forced i x) O outside constant
  have bound := log_card_le_of_weight edge endpoints
    (fun x : ↥(majorityInputs edge) => full x.val) (by decide : 0 < 1)
    (fun y => by convert fibers y using 1; congr) certificate
  have cost :
      (((c.size : ℝ) - S.card - O.card) * Real.log 2 -
        ((Joint.retainedTwo c.program U).card - (S.card : ℝ)) *
          (Real.log 2 - Real.binEntropy (4 / 9)) -
        (Joint.retainedWide c.program U).card * (Real.log 2 - Real.binEntropy (8 / 27))) /
        Real.log 2 = c.size - S.card - O.card -
          pairSaving * ((Joint.retainedTwo c.program U).card - (S.card : ℝ)) -
          tripleSaving * (Joint.retainedWide c.program U).card := by
    unfold pairSaving tripleSaving
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [cost] at bound
  simp only [Fintype.card_coe, U, Finset.card_univ, Fintype.card_fin, Nat.cast_one,
    Real.logb_one, add_zero, retainedTwo_univ] at bound
  rw [messageLoss_eq_logb_three_sub_one]
  dsimp only [O, outputConjunctionCount] at bound ⊢
  nlinarith

/-- Output rank combines with all conditional narrow and wide savings. -/
theorem three_mul_input_add_conditional_le_two_mul_size {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation))
    (P : Algebraic.Aggregate.Geometry.Shared.PrimaryPairing c.program)
    (disjoint : (P.remaining : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    3 * (n : ℝ) + (messageLoss - pairSaving) *
        ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card - 2 * P.pairs.card) +
      pairSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
      tripleSaving * (Joint.retainedWide c.program Finset.univ).card ≤ 2 * c.size := by
  have information := input_add_conditional_le_size_sub_outputConjunctionCount
    c bijective nonliteral P.remaining Finset.sdiff_subset disjoint
  have rank : (n : ℝ) ≤ conjunctionCount c.program := by
    exact_mod_cast independent.output_le_conjunctionCount
  have outputs : (n : ℝ) + conjunctionCount c.program ≤
      c.size + outputConjunctionCount c := by
    exact_mod_cast input_add_conjunctionCount_le_size_add_outputConjunctionCount
      c bijective (by intro i j; simpa using nonliteral i j false)
  have pairing : ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card : ℝ) =
      2 * P.pairs.card + P.remaining.card := by exact_mod_cast P.card_exactTwo
  rw [pairing] at information ⊢
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional
