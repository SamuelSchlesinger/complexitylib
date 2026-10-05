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
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Entropy
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank

/-!
# Majority fibers of permutation circuit messages

Disjoint exact-two conjunctions simultaneously have their majority summaries on
a large set of inputs. These false coordinates and the constant true conjunction
output summaries can both be omitted from the injective full-primary message.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- Disjoint majority summaries and constant output summaries save separate message bits. -/
theorem input_add_majority_le_size_sub_outputConjunctionCount {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (S : Finset (Fin c.size)) (eligible : S ⊆ Algebraic.Aggregate.Geometry.Shared.exactTwo
      c.program)
    (disjoint : (S : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    (n : ℝ) + messageLoss * S.card ≤ c.size - outputConjunctionCount c := by
  let U : Finset (Fin n) := Finset.univ
  let O := outputConjunctions c
  let R := {i : Fin c.size // i ∉ S ∪ O}
  let full (x : U → Bool) := key c.program U (glue U x (fun _ => false))
  let reduced (x : U → Bool) (i : R) := full x i.val
  have pairs (i : S) : SelectedPair (c.program.lines i.val) U := by
    have hi := (Finset.mem_filter.mp (eligible i.property)).2
    exact Joint.RetainedTwo.selectedPair ⟨hi.1, hi.2, Finset.subset_univ _⟩
  choose edge left right forced using fun i : S =>
    exists_edge_of_selectedPair (c.program.lines i.val) U (pairs i)
  have endpoints := endpoint_injective_of_disjoint c.program U S edge left right disjoint
  have full_forced (x : U → Bool) (i : S) :
      full x i.val = true → (edge i).eval x = true := forced i x
  have constant (i : Fin c.size) (hi : i ∈ O) (x : U → Bool) : full x i = true := by
    exact lineSummary_eq_true_of_primaryInputs_eq_empty _ (Finset.mem_filter.mp hi).2
      (primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral i hi)
      (glue U x (fun _ => false))
  have outside : Disjoint S O := by
    apply Finset.disjoint_left.mpr
    intro i hi ho
    have two := (Finset.mem_filter.mp (eligible hi)).2.2
    rw [primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral i ho] at two
    simp at two
  have nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j := by
    intro i j
    simpa using nonliteral i j false
  have full_injective : Function.Injective full := by
    intro x y same
    have equal := key_injective_of_permutation c bijective nonprojection same
    funext i
    have coordinate := congrFun equal i.val
    simpa [glue] using coordinate
  have fibers (y : R → Bool) :
      ((majorityInputs edge).filter fun x => reduced x = y).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx z hz
    obtain ⟨xm, xy⟩ := Finset.mem_filter.mp hx
    obtain ⟨zm, zy⟩ := Finset.mem_filter.mp hz
    apply full_injective
    funext i
    by_cases hs : i ∈ S
    · rw [key_eq_false_of_majority full S edge full_forced xm ⟨i, hs⟩,
        key_eq_false_of_majority full S edge full_forced zm ⟨i, hs⟩]
    · by_cases ho : i ∈ O
      · rw [constant i ho x, constant i ho z]
      · exact congrFun (xy.trans zy.symm) ⟨i, by simp [hs, ho]⟩
  have countR : Fintype.card R + S.card + outputConjunctionCount c = c.size := by
    have partition := Fintype.card_subtype_compl (fun i : Fin c.size => i ∈ S ∪ O)
    have count : Fintype.card {i : Fin c.size // i ∈ S ∪ O} = S.card + O.card := by
      rw [Fintype.card_coe, Finset.card_union_of_disjoint outside]
    rw [count, Fintype.card_fin] at partition
    have bound : S.card + O.card ≤ c.size := by
      rw [← Finset.card_union_of_disjoint outside]
      exact le_trans (Finset.card_le_univ _) (by simp)
    change Fintype.card R + S.card + O.card = c.size
    change Fintype.card R = c.size - (S.card + O.card) at partition
    lia
  have information := log_card_le_of_boolean_fibers edge endpoints reduced (by decide) fibers
  have cards : (Fintype.card R : ℝ) + S.card + outputConjunctionCount c = c.size := by
    exact_mod_cast countR
  simp only [Fintype.card_coe, Nat.cast_one, Real.logb_one] at information
  have inputCard : U.card = n := by simp [U]
  rw [inputCard] at information
  rw [messageLoss_eq_logb_three_sub_one]
  nlinarith

/-- Unpaired exact-two gates give the majority-fiber inequality for a primary pairing. -/
theorem input_add_remaining_le_size_sub_outputConjunctionCount {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (P : Algebraic.Aggregate.Geometry.Shared.PrimaryPairing c.program)
    (disjoint : (P.remaining : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    (n : ℝ) + messageLoss * P.remaining.card ≤ c.size - outputConjunctionCount c := by
  exact input_add_majority_le_size_sub_outputConjunctionCount c bijective nonliteral
    P.remaining Finset.sdiff_subset disjoint

/-- Independent nonaffine outputs combine with unpaired majority summaries. -/
theorem three_mul_input_add_majority_le_two_mul_size {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation))
    (P : Algebraic.Aggregate.Geometry.Shared.PrimaryPairing c.program)
    (disjoint : (P.remaining : Set (Fin c.size)).Pairwise fun i j =>
      Disjoint (primaryInputs (c.program.lines i)) (primaryInputs (c.program.lines j))) :
    3 * (n : ℝ) + messageLoss *
      ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card - 2 * P.pairs.card) ≤
      2 * c.size := by
  have information := input_add_remaining_le_size_sub_outputConjunctionCount
    c bijective nonliteral P disjoint
  have rank : (n : ℝ) ≤ conjunctionCount c.program := by
    exact_mod_cast independent.output_le_conjunctionCount
  have outputs : (n : ℝ) + conjunctionCount c.program ≤
      c.size + outputConjunctionCount c := by
    exact_mod_cast input_add_conjunctionCount_le_size_add_outputConjunctionCount
      c bijective (by intro i j; simpa using nonliteral i j false)
  have pairing : ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card : ℝ) =
      2 * P.pairs.card + P.remaining.card := by
    exact_mod_cast P.card_exactTwo
  rw [pairing]
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
