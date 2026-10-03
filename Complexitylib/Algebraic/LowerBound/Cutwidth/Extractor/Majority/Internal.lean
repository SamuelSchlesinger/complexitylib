/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Defs
public import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Bridge

/-!
# Proofs for majority evaluation and robustness

The final majority stage in Chattopadhyay and Liao's constant-error sumset
extractor has a uniform polynomial-time evaluator in Complexitylib's machine
model. A strict good-coordinate margin larger than the number of bad coordinates
forces the verdict, regardless of how the bad bits depend on the good bits.

These are only properties of the final stage; no sumset-extraction guarantee is
claimed without the preceding source reduction and its probabilistic analysis.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem popCount_list (x : List Bool) :
    Complexity.popCount (fun i : Fin x.length => x[i]) =
      ((Finset.range x.length).filter fun i => x[i]?.getD false = true).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simpa using hi
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro i hi
    have hi' : i < x.length := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    exact ⟨⟨i, hi'⟩, by simpa [hi'] using (Finset.mem_filter.mp hi).2, rfl⟩

/-- Majority agrees exactly with the existing finite-vector majority, under
the standard list encoding. -/
theorem majorityEval_toList {n : Nat} (x : Complexity.BitString n) :
    majorityEval x.toList = [Complexity.majority x] := by
  simp only [majorityEval, Complexity.majority, popCount_list,
    Complexity.BitString.toList, List.length_ofFn]
  congr 3
  symm
  congr 1
  unfold Complexity.popCount
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simpa [Complexity.popCount] using hi
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro i hi
    have hi' : i < n := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    exact ⟨⟨i, hi'⟩, by simpa [hi'] using (Finset.mem_filter.mp hi).2, rfl⟩

/-- The majority evaluator is uniform polynomial time in the repository's
deterministic Turing-machine model. -/
theorem majorityEval_mem_FP : majorityEval ∈ Complexity.FP := by
  have hcount : Complexity.UnaryFn fun x : List Bool =>
      ((Finset.range x.length).filter fun i => x[i]?.getD false = true).card := by
    simpa only [Complexity.pairFst_pair, Complexity.pairSnd_pair,
      List.length_replicate, id_eq] using
      (Complexity.UnaryFn.length Complexity.id_mem_FP).count
        (Complexity.FPPred.getBit Complexity.Cobham.fstBlock_mem_FP
          Complexity.UnaryFn.index)
  have hpred := Complexity.FPPred.lt
    (Complexity.UnaryFn.length Complexity.id_mem_FP)
    ((Complexity.UnaryFn.const 2).mul hcount)
  exact Complexity.mem_FP_of_eq hpred.flag_mem_FP fun x => by
    simp only [majorityEval, Complexity.majority, popCount_list, id_eq, gt_iff_lt]

private theorem count_good_le {n : Nat} (good : Finset (Fin n)) (x : Fin n → Bool) :
    (good.filter fun i => x i = true).card ≤ Complexity.popCount x := by
  apply Finset.card_le_card
  intro i hi
  simpa using (Finset.mem_filter.mp hi).2

private theorem count_le_good_add_bad {n : Nat}
    (good : Finset (Fin n)) (x : Fin n → Bool) :
    Complexity.popCount x ≤ (good.filter fun i => x i = true).card + (n - good.card) := by
  have hsub : Finset.univ.filter (fun i => x i = true) ⊆
      (good.filter fun i => x i = true) ∪ (Finset.univ \ good) := by
    intro i hi
    by_cases hg : i ∈ good <;> simp_all
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa [Complexity.popCount, Finset.card_sdiff_of_subset (Finset.subset_univ good)] using h

/-- More positive good votes than all possible negative bad votes forces a
true majority, without any independence condition on the bad coordinates. -/
theorem majority_eq_true_of_margin {n : Nat} {good : Finset (Fin n)}
    {x : Fin n → Bool} (h : ((n - good.card : Nat) : Int) < voteMargin good x) :
    Complexity.majority x = true := by
  have hg : good.card ≤ n := by simpa using Finset.card_le_univ good
  have hc := count_good_le good x
  simp only [voteMargin] at h
  simp only [Complexity.majority, decide_eq_true_eq]
  lia

/-- A sufficiently negative good margin forces false even if every bad
coordinate votes true. Ties follow the evaluator's false convention. -/
theorem majority_eq_false_of_margin {n : Nat} {good : Finset (Fin n)}
    {x : Fin n → Bool} (h : voteMargin good x ≤ -((n - good.card : Nat) : Int)) :
    Complexity.majority x = false := by
  have hg : good.card ≤ n := by simpa using Finset.card_le_univ good
  have hc := count_le_good_add_bad good x
  simp only [voteMargin] at h
  simp only [Complexity.majority, decide_eq_false_iff_not]
  lia

end Algebraic.Cutwidth.Extractor.Internal
