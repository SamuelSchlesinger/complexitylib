/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Circuit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Counting
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Message
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Fibres
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.LowerBound

/-!
# Large majority fibers of actual one-way circuit messages

The unmatched conjunction summaries have disjoint primary supports. Fixing their
majority values leaves a large input set, while rectangle freeness bounds every
fiber of the remaining message. The spare output bit is explicitly counted.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- Disjoint selected conjunction summaries improve the actual sender's message bound. -/
theorem sender_le_of_disjoint_summaries {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card) (S : Finset (Fin c.size))
    (selected : ∀ i ∈ S, SelectedPair (c.program.lines i) U)
    (disjoint : (S : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    (U.card : ℝ) + messageLoss * S.card ≤ c.size + 1 + Real.logb 2 K := by
  classical
  choose edge left right forced using fun i : S =>
    exists_edge_of_selectedPair (c.program.lines i.val) U (selected i.val i.property)
  have injective := endpoint_injective_of_disjoint c.program U S edge left right disjoint
  let gateKey (x : U → Bool) := key c.program U (glue U x (fun _ => false))
  let full := (circuitOneWaySummary c U).key
  let R := {i : Fin c.size // i ∉ S}
  let residual (x : U → Bool) : Option R → Bool
    | none => full x (Fin.last c.size)
    | some i => gateKey x i.val
  have frozen (x : U → Bool) (hx : x ∈ majorityInputs edge) (i : S) :
      gateKey x i.val = false :=
    key_eq_false_of_majority gateKey S edge (fun x i => forced i x) hx i
  have refines : ∀ x ∈ majorityInputs edge, ∀ y ∈ majorityInputs edge,
      residual x = residual y → full x = full y := by
    intro x hx y hy same
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact congrFun same none
    · simp only [full, circuitOneWaySummary, outputKey, Fin.lastCases_castSucc]
      change gateKey x j = gateKey y j
      by_cases hj : j ∈ S
      · rw [frozen x hx ⟨j, hj⟩, frozen y hy ⟨j, hj⟩]
      · exact congrFun same (some ⟨j, hj⟩)
  have fibers : ∀ y, (Finset.univ.filter fun x => full x = y).card ≤ K := by
    intro y
    convert (Entropy.card_fibre_lt_of_rectangleFree_both hK free freeNot U large
      (circuitOneWaySummary c U) y).le using 1
    congr
  have caps (y : Option R → Bool) :
      ((majorityInputs edge).filter fun x => residual x = y).card ≤ K := by
    have source := card_fiber_le_of_refines_on (majorityInputs edge) full residual refines
      (K := K) (fun z => by convert fibers z using 1; congr) y
    convert source using 1
    congr
  have bound := log_card_le_of_boolean_fibers edge injective residual hK caps
  have counts : S.card + Fintype.card R = c.size := by
    have split := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin c.size))) (fun i => i ∈ S)
    simpa [R, Fintype.card_subtype] using split
  have realCounts : (S.card : ℝ) + Fintype.card R = c.size := by exact_mod_cast counts
  simp only [Fintype.card_coe, Fintype.card_option, Nat.cast_add, Nat.cast_one] at bound
  rw [messageLoss_eq_logb_three_sub_one]
  linarith

/-- The original unmatched summaries lose at most one large-fiber saving per receiver bit. -/
theorem input_le_size_of_fibers {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 4 ≤ n)
    (P : Algebraic.Aggregate.Geometry.Shared.PrimaryPairing c.program)
    (disjoint : (P.remaining : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    (n : ℝ) + messageLoss * P.remaining.card ≤
      c.size + 1 + Real.logb 2 K + (1 + messageLoss) * (Nat.clog 2 K + 1) := by
  let k := Nat.clog 2 K
  let a := n - (k + 1)
  obtain ⟨U, _, hU⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := a) (by simp [a])
  have complement : Uᶜ.card = k + 1 := by
    have total : U.card + Uᶜ.card = n := by simp
    dsimp only [a, k] at hU ⊢
    lia
  let S := P.remaining.filter fun i => primaryInputs (c.program.lines i) ⊆ U
  have selected (i : Fin c.size) (hi : i ∈ S) : SelectedPair (c.program.lines i) U := by
    obtain ⟨remaining, contained⟩ := Finset.mem_filter.mp hi
    obtain ⟨conjunction, two⟩ := Algebraic.Aggregate.Geometry.Shared.mem_exactTwo.mp
      (Finset.mem_sdiff.mp remaining).1
    exact Joint.RetainedTwo.selectedPair ⟨conjunction, two, contained⟩
  have apart : (S : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j)) := by
    intro i hi j hj different
    exact disjoint (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 different
  have large : 2 * K ≤ 2 ^ Uᶜ.card := by
    rw [complement, Nat.pow_succ]
    have upper := Nat.le_pow_clog (by decide : 1 < 2) K
    dsimp only [k]
    lia
  have bound := sender_le_of_disjoint_summaries c hK disperse.rectangleFree
    (Geometry.disperse_not disperse).rectangleFree U large S selected apart
  have retained : (P.remaining.card : ℝ) ≤ S.card + Uᶜ.card := by
    exact_mod_cast card_le_retained_add_complement c.program P.remaining U disjoint
  have weighted := mul_le_mul_of_nonneg_left retained messageLoss_pos.le
  have card : (U.card : ℝ) = n - k - 1 := by
    rw [hU]
    dsimp only [a]
    rw [Nat.cast_sub (by dsimp only [k]; lia), Nat.cast_add, Nat.cast_one]
    ring
  rw [card] at bound
  rw [complement] at weighted
  push_cast at weighted
  dsimp only [k] at bound weighted
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
