/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Message
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Conditional.Retention
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.OneWay

/-!
# Conditional entropy of actual one-way messages

A fixed-size receiving set retains a weighted collection of narrow and wide
summaries. The unmatched disjoint pairs lose at most one member per receiver
coordinate, so their majority event supports all three information savings.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

open Algebraic.Aggregate.Geometry Entropy
open scoped Classical

/-- Restricting the domain of a message cannot enlarge its fibers. -/
theorem card_subtype_fiber_le {X Y : Type*} [Fintype X] (event : Finset X)
    (key : X → Y) (y : Y) :
    (Finset.univ.filter fun x : event => key x.val = y).card ≤
      (Finset.univ.filter fun x => key x = y).card := by
  apply Finset.card_le_card_of_injOn (fun x : event => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro x _ z _ equal
    exact Subtype.ext equal

/-- Conditional entropy strengthens the sender bound on the same majority event. -/
theorem sender_le_of_conditional_summaries {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card) (S : Finset (Fin c.size))
    (selected : S ⊆ Joint.retainedTwo c.program U)
    (disjoint : (S : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    (U.card : ℝ) + (messageLoss - pairSaving) * S.card +
      pairSaving * (Joint.retainedTwo c.program U).card +
      tripleSaving * (Joint.retainedWide c.program U).card ≤
        c.size + 1 + Real.logb 2 K := by
  choose edge left right forced using fun i : S =>
    exists_edge_of_selectedPair (c.program.lines i.val) U
      (Finset.mem_filter.mp (selected i.property)).2.selectedPair
  have injective := endpoint_injective_of_disjoint c.program U S edge left right disjoint
  let full := (circuitOneWaySummary c U).key
  have fibers : ∀ y, (Finset.univ.filter fun x => full x = y).card ≤ K := by
    intro y
    convert (Entropy.card_fibre_lt_of_rectangleFree_both hK free freeNot U large
      (circuitOneWaySummary c U) y).le using 1
    congr
  have caps (y : Fin (c.size + 1) → Bool) :
      (Finset.univ.filter fun x : ↥(majorityInputs edge) => full x.val = y).card ≤ K := by
    convert (card_subtype_fiber_le (majorityInputs edge) full y).trans
      (by convert fibers y using 1; congr) using 1
    congr
  have certificate := majorityOutputKeyWeightBound c.program U S selected edge injective
    (fun x i => forced i x) (c.outputs 0)
  have bound := log_card_le_of_weight edge injective
    (fun x : ↥(majorityInputs edge) => full x.val) hK
    (fun y => by convert caps y using 1; congr) certificate
  have cost :
      (((c.size : ℝ) + 1 - S.card) * Real.log 2 -
        ((Joint.retainedTwo c.program U).card - (S.card : ℝ)) *
          (Real.log 2 - Real.binEntropy (4 / 9)) -
        (Joint.retainedWide c.program U).card * (Real.log 2 - Real.binEntropy (8 / 27))) /
        Real.log 2 = c.size + 1 - S.card -
          pairSaving * ((Joint.retainedTwo c.program U).card - (S.card : ℝ)) -
          tripleSaving * (Joint.retainedWide c.program U).card := by
    unfold pairSaving tripleSaving
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [cost] at bound
  simp only [Fintype.card_coe] at bound
  rw [messageLoss_eq_logb_three_sub_one]
  nlinarith

/-- Weighted cut retention and disjoint-pair loss give the conditional finite inequality. -/
theorem input_le_size_of_conditional_entropy {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 4 ≤ n)
    (P : Algebraic.Aggregate.Geometry.Shared.PrimaryPairing c.program)
    (disjoint : (P.remaining : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    (n : ℝ) + Shared.receiverRetention n (Nat.clog 2 K) *
        ((messageLoss - pairSaving) * P.remaining.card +
          pairSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
          tripleSaving * (Joint.retainedWide c.program Finset.univ).card) ≤
      c.size + 1 + Real.logb 2 K +
        (1 + messageLoss - pairSaving) * (Nat.clog 2 K + 1) := by
  let k := Nat.clog 2 K
  let a := n - (k + 1)
  have ha : 3 ≤ a := by dsimp only [a, k]; lia
  have han : a ≤ n := Nat.sub_le _ _
  obtain ⟨U, hU, retained⟩ := Joint.exists_subset_retained_weight c.program ha han
    pairSaving tripleSaving pairSaving_nonneg tripleSaving_nonneg
  have complement : Uᶜ.card = k + 1 := by
    have total : U.card + Uᶜ.card = n := by simp
    dsimp only [a, k] at hU ⊢
    lia
  let S := P.remaining.filter fun i => primaryInputs (c.program.lines i) ⊆ U
  have selected : S ⊆ Joint.retainedTwo c.program U := by
    intro i hi
    obtain ⟨remaining, contained⟩ := Finset.mem_filter.mp hi
    obtain ⟨conjunction, two⟩ := Algebraic.Aggregate.Geometry.Shared.mem_exactTwo.mp
      (Finset.mem_sdiff.mp remaining).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, conjunction, two, contained⟩
  have apart : (S : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j)) := by
    intro i hi j hj different
    exact disjoint (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 different
  have large : 2 * K ≤ 2 ^ Uᶜ.card := by
    rw [complement, Nat.pow_succ]
    have upper := Nat.le_pow_clog (by decide : 1 < 2) K
    dsimp only [k]
    lia
  have bound := sender_le_of_conditional_summaries c hK disperse.rectangleFree
    (Geometry.disperse_not disperse).rectangleFree U large S selected apart
  have loss : (P.remaining.card : ℝ) ≤ S.card + Uᶜ.card := by
    exact_mod_cast card_le_retained_add_complement c.program P.remaining U disjoint
  have positive : 0 ≤ messageLoss - pairSaving := sub_nonneg.mpr pairSaving_lt_messageLoss.le
  have weighted := mul_le_mul_of_nonneg_left loss positive
  have card : (U.card : ℝ) = n - k - 1 := by
    rw [hU]
    dsimp only [a]
    rw [Nat.cast_sub (by dsimp only [k]; lia), Nat.cast_add, Nat.cast_one]
    ring
  have ratio : Joint.tripleRetention n a = Shared.receiverRetention n k := by
    unfold Joint.tripleRetention Shared.receiverRetention
    have cast_a : (a : ℝ) = n - k - 1 := by simpa only [hU] using card
    rw [cast_a]
    ring
  have weaken := mul_le_mul_of_nonneg_right (receiverRetention_le_one range)
    (mul_nonneg positive (Nat.cast_nonneg P.remaining.card))
  rw [ratio] at retained
  rw [card] at bound
  rw [complement] at weighted
  push_cast at weighted
  dsimp only [k] at bound weighted retained
  nlinarith only [bound, weighted, retained, weaken]

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional
