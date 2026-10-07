/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.NormalForm
public import Complexitylib.Circuits.DepthThree.LowerBound.NormalForm

/-!
# Three-layer normalization of depth-three formulas

Flatten like-polarity gates and pad leaves. Every depth-three formula, or its complement,
is an OR of CNFs with total clause-and-conjunction count at most twice its tree size.
-/

@[expose] public section

namespace Complexity.AC0Formula

lemma leaf_cnf (f : AC0Formula n) (h : f.depth = 0) :
    ∃ F : CNF n, F.complexity ≤ f.size ∧ ∀ x, F.eval x = f.eval x := by
  cases f with
  | const b =>
    cases b
    · exact ⟨⟨[[]]⟩, le_rfl, fun _ => rfl⟩
    · exact ⟨⟨[]⟩, by simp [CNF.complexity, size], fun _ => rfl⟩
  | lit l => exact ⟨⟨[[l]]⟩, le_rfl, fun x => by simp [CNF.eval, eval]⟩
  | and fs => simp [depth] at h
  | or fs => simp [depth] at h

lemma or_leaves_cnf (fs : AC0Forest n) (hd : forestDepth fs = 0) :
    ∃ F : CNF n, F.complexity ≤ 1 ∧ ∀ x, F.eval x = evalAny x fs := by
  cases fs with
  | nil => exact ⟨⟨[[]]⟩, le_rfl, fun _ => rfl⟩
  | cons f fs =>
    have hf : f.depth = 0 := by simp only [forestDepth, max_eq_zero] at hd; exact hd.1
    have ht : forestDepth fs = 0 := by simp only [forestDepth, max_eq_zero] at hd; exact hd.2
    obtain ⟨F, hF, he⟩ := or_leaves_cnf fs ht
    cases f with
    | const b =>
      cases b
      · exact ⟨F, hF, fun x => by simpa [evalAny, eval] using he x⟩
      · exact ⟨⟨[]⟩, by simp [CNF.complexity], fun x => by simp [CNF.eval, evalAny, eval]⟩
    | lit l =>
      rcases F with ⟨clauses⟩
      cases clauses with
      | nil =>
        refine ⟨⟨[]⟩, by simp [CNF.complexity], fun x => ?_⟩
        rw [evalAny, ← he x]
        simp [CNF.eval]
      | cons C Cs =>
        have hCs : Cs = [] := by
          have : Cs.length = 0 := by simp only [CNF.complexity, List.length_cons] at hF; lia
          exact List.length_eq_zero_iff.mp this
        subst Cs
        refine ⟨⟨[l :: C]⟩, le_rfl, fun x => ?_⟩
        rw [evalAny, ← he x]
        simp [CNF.eval, eval]
    | and cs => simp [depth] at hf
    | or cs => simp [depth] at hf

lemma and_cnf (fs : AC0Forest n)
    (h : ∀ f ∈ fs.toList, ∃ F : CNF n, F.complexity ≤ f.size ∧
      ∀ x, F.eval x = f.eval x) :
    ∃ F : CNF n, F.complexity ≤ forestSize fs ∧ ∀ x, F.eval x = evalAll x fs := by
  cases fs with
  | nil => exact ⟨⟨[]⟩, le_rfl, fun _ => rfl⟩
  | cons f fs =>
    obtain ⟨F, hF, he⟩ := h f (by simp [AC0Forest.toList])
    obtain ⟨G, hG, hg⟩ := and_cnf fs (fun f hf => h f (by simp [AC0Forest.toList, hf]))
    refine ⟨⟨F.clauses ++ G.clauses⟩, ?_, fun x => ?_⟩
    · simpa [CNF.complexity, forestSize] using Nat.add_le_add hF hG
    · simpa only [CNF.eval, List.all_append, evalAll] using congrArg₂ Bool.and (he x) (hg x)

lemma depth_one_cnf (f : AC0Formula n) (hd : f.depth ≤ 1) :
    ∃ F : CNF n, F.complexity ≤ f.size ∧ ∀ x, F.eval x = f.eval x := by
  cases f with
  | const b => exact leaf_cnf (.const b) rfl
  | lit l => exact leaf_cnf (.lit l) rfl
  | and fs =>
    obtain ⟨F, hF, he⟩ := and_cnf fs (fun f hf => leaf_cnf f (by
      have := depth_le_forestDepth_of_mem f fs hf
      simp only [depth] at hd
      lia))
    exact ⟨F, hF.trans (by simp [size]), he⟩
  | or fs =>
    obtain ⟨F, hF, he⟩ := or_leaves_cnf fs (by simp only [depth] at hd; lia)
    exact ⟨F, hF.trans (one_le_size _), he⟩

lemma and_depth_two_cnf (fs : AC0Forest n) (hd : forestDepth fs ≤ 1) :
    ∃ F : CNF n, F.complexity ≤ forestSize fs ∧ ∀ x, F.eval x = evalAll x fs :=
  and_cnf fs fun f hf => depth_one_cnf f ((depth_le_forestDepth_of_mem f fs hf).trans hd)

/-- Total number of clause and conjunction gates in a list of CNFs. -/
def cnfCost (Fs : List (CNF n)) : ℕ := (Fs.map fun F => F.complexity + 1).sum

mutual
lemma depth_two_sigma (f : AC0Formula n) (hd : f.depth ≤ 2) :
    ∃ Fs : List (CNF n), cnfCost Fs ≤ 2 * f.size ∧
      ∀ x, Fs.any (fun F => F.eval x) = f.eval x := by
  cases f with
  | const b =>
    obtain ⟨F, hF, he⟩ := leaf_cnf (.const b : AC0Formula n) rfl
    exact ⟨[F], by simp [cnfCost, size] at hF ⊢; lia, fun x => by simpa [eval] using he x⟩
  | lit l =>
    obtain ⟨F, hF, he⟩ := leaf_cnf (.lit l) rfl
    exact ⟨[F], by simp [cnfCost, size] at hF ⊢; lia, fun x => by simpa [eval] using he x⟩
  | and fs =>
    obtain ⟨F, hF, he⟩ := and_depth_two_cnf fs (by simp only [depth] at hd; lia)
    exact ⟨[F], by simp [cnfCost, size]; lia, fun x => by simpa [eval] using he x⟩
  | or fs =>
    obtain ⟨Fs, hFs, he⟩ := forest_depth_two_sigma fs (by simp only [depth] at hd; lia)
    exact ⟨Fs, hFs.trans (by simp [size]), he⟩

lemma forest_depth_two_sigma (fs : AC0Forest n) (hd : forestDepth fs ≤ 2) :
    ∃ Fs : List (CNF n), cnfCost Fs ≤ 2 * forestSize fs ∧
      ∀ x, Fs.any (fun F => F.eval x) = evalAny x fs := by
  cases fs with
  | nil => exact ⟨[], le_rfl, fun _ => rfl⟩
  | cons f fs =>
    have hf : f.depth ≤ 2 := (le_max_left _ _).trans hd
    have ht : forestDepth fs ≤ 2 := (le_max_right _ _).trans hd
    obtain ⟨F, hF, he⟩ := depth_two_sigma f hf
    obtain ⟨G, hG, hg⟩ := forest_depth_two_sigma fs ht
    refine ⟨F ++ G, ?_, fun x => ?_⟩
    · simp only [cnfCost, List.map_append, List.sum_append] at hF hG ⊢
      simp only [forestSize]
      lia
    · simp only [List.any_append, he, hg, evalAny]
end

lemma or_depth_three_sigma (fs : AC0Forest n) (hd : forestDepth fs ≤ 2) :
    ∃ Fs : List (CNF n), cnfCost Fs ≤ 2 * (.or fs : AC0Formula n).size ∧
      ∀ x, Fs.any (fun F => F.eval x) = (.or fs : AC0Formula n).eval x := by
  obtain ⟨Fs, hFs, he⟩ := forest_depth_two_sigma fs hd
  exact ⟨Fs, hFs.trans (by simp [size]), he⟩

lemma depth_three_sigma_polarity (f : AC0Formula n) (hd : f.depth ≤ 3) :
    ∃ (b : Bool) (Fs : List (CNF n)), cnfCost Fs ≤ 2 * f.size ∧
      ∀ x, Fs.any (fun F => F.eval x) = Bool.xor (f.eval x) b := by
  cases f with
  | const b =>
    obtain ⟨Fs, hFs, he⟩ := depth_two_sigma (.const b : AC0Formula n) (by simp [depth])
    exact ⟨false, Fs, hFs, fun x => by simpa [eval] using he x⟩
  | lit l =>
    obtain ⟨Fs, hFs, he⟩ := depth_two_sigma (.lit l) (by simp [depth])
    exact ⟨false, Fs, hFs, fun x => by simpa [eval] using he x⟩
  | or fs =>
    obtain ⟨Fs, hFs, he⟩ := or_depth_three_sigma fs (by simp only [depth] at hd; lia)
    exact ⟨false, Fs, hFs, fun x => by simpa [eval] using he x⟩
  | and fs =>
    have hd' : forestDepth (negForest fs) ≤ 2 := by
      rw [forestDepth_negForest_internal]
      simp only [depth] at hd
      lia
    obtain ⟨Fs, hFs, he⟩ := or_depth_three_sigma (negForest fs) hd'
    refine ⟨true, Fs, ?_, fun x => ?_⟩
    · simpa only [size, forestSize_negForest_internal] using hFs
    · simpa only [eval, evalAny_negForest_internal, Bool.xor_true] using he x

lemma cnfCost_eq (Fs : List (CNF n)) :
    cnfCost Fs = (∑ j : Fin Fs.length, Fs[j].complexity) + Fs.length := by
  rw [cnfCost, ← List.ofFn_getElem_eq_map Fs (fun F => F.complexity + 1), List.sum_ofFn]
  simp [Finset.sum_add_distrib, Fin.getElem_fin]

lemma depth_three_source_proof (f : AC0Formula n) (hd : f.depth ≤ 3) :
    ∃ (b : Bool) (C : DepthThreeLowerBound.Circuit3 (Fin n)),
      C.gateCount ≤ 2 * f.size + 1 ∧
      C.Computes (fun x => Bool.xor (f.eval x) b) := by
  obtain ⟨b, Fs, hFs, he⟩ := depth_three_sigma_polarity f hd
  refine ⟨b, DepthThreeLowerBound.Circuit3.ofCNFs Fs, ?_, fun x => ?_⟩
  · rw [DepthThreeLowerBound.Circuit3.gateCount_ofCNFs, ← cnfCost_eq]
    lia
  · rw [DepthThreeLowerBound.Circuit3.eval_ofCNFs]
    exact he x

end Complexity.AC0Formula
