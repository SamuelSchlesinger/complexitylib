/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.NormalForm.Defs
public import Complexitylib.Circuits.DepthThree.LowerBound.ThresholdWeight
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageLowerBound
public import Complexitylib.Circuits.KCNF.Basic

/-!
# Transport of the depth-three and threshold-weight bounds to canonical CNFs

The indexed construction records every clause occurrence and one middle gate per CNF.
The weight bounds use the width-nonincreasing set conversion instead.
-/

public section

namespace Complexity.CNF

lemma eval_toDepthThree_proof (F : CNF n) (x : BitString n) :
    F.toDepthThree.eval x = F.eval x := by
  apply Bool.eq_iff_iff.mpr
  simp only [toDepthThree, DepthThreeLowerBound.CNF.eval_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    DepthThreeLowerBound.Clause.eval_eq_true, List.mem_toFinset, CNF.eval,
    List.all_eq_true, List.any_eq_true]
  apply forall_congr' fun C => ?_
  apply imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨l, ⟨k, hk, rfl⟩, he⟩
    exact ⟨k, hk, (Literal.eval_eq_true_iff k x).mpr he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨(l.var, l.polarity), ⟨l, hl, rfl⟩, (Literal.eval_eq_true_iff l x).mp he⟩

lemma width_toDepthThree_proof (F : CNF n) : F.toDepthThree.WidthAtMost F.width := by
  classical
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  calc
    _ ≤ (D.map fun l => (l.var, l.polarity)).toFinset.card := by
      unfold DepthThreeLowerBound.Clause.width DepthThreeLowerBound.Clause.scope
      exact @Finset.card_image_le _ _ _ _ (Classical.decEq _)
    _ ≤ (D.map fun l => (l.var, l.polarity)).length := List.toFinset_card_le _
    _ = D.length := List.length_map ..
    _ ≤ F.width := F.length_le_width D hD

end Complexity.CNF


namespace Complexity.DepthThreeLowerBound.Circuit3

lemma eval_clauseInputs_proof (C : List (Complexity.Literal n)) (x : BitString n) :
    (clauseInputs C).eval x = C.any (fun l => l.eval x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [RawClause.eval_eq_true, clauseInputs, List.mem_map, List.any_eq_true]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, he⟩
    exact ⟨l, hl, (Complexity.Literal.eval_eq_true_iff l x).mpr (by
      simpa [GateInput.eval, Literal.eval] using he)⟩
  · rintro ⟨l, hl, he⟩
    refine ⟨_, ⟨l, hl, rfl⟩, ?_⟩
    simpa [GateInput.eval, Literal.eval] using (Complexity.Literal.eval_eq_true_iff l x).mp he

lemma middleEval_ofCNFs_proof (Fs : List (Complexity.CNF n)) (j : Fin Fs.length)
    (x : BitString n) : (ofCNFs Fs).middleEval j x = Fs[j].eval x := by
  apply Bool.eq_iff_iff.mpr
  simp only [middleEval_eq_true, ofCNFs, Finset.mem_filter, Finset.mem_univ, true_and,
    eval_clauseInputs_proof, Complexity.CNF.eval, List.all_eq_true]
  constructor
  · intro h C hC
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hC
    have hh := h ((bottomEquiv Fs).symm ⟨j, ⟨k, hk⟩⟩) (by simp)
    change (fun t : BottomIndex Fs =>
      (Fs[t.1].clauses[t.2]).any (fun l => l.eval x) = true)
      ((bottomEquiv Fs) ((bottomEquiv Fs).symm ⟨j, ⟨k, hk⟩⟩)) at hh
    rw [Equiv.apply_symm_apply] at hh
    exact hh
  · intro h i hi
    subst j
    exact h _ (List.getElem_mem ((bottomEquiv Fs i).2).isLt)

lemma eval_ofCNFs_proof (Fs : List (Complexity.CNF n)) (x : BitString n) :
    (ofCNFs Fs).eval x = Fs.any (fun F => F.eval x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true, ofCNFs, Finset.mem_univ, true_and]
  change (∃ j : Fin Fs.length, (ofCNFs Fs).middleEval j x = true) ↔ _
  simp only [middleEval_ofCNFs_proof, List.any_eq_true]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨Fs[j], List.getElem_mem j.isLt, hj⟩
  · rintro ⟨F, hF, he⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hF
    exact ⟨⟨j, hj⟩, he⟩

lemma gateCount_ofCNFs_proof (Fs : List (Complexity.CNF n)) :
    (ofCNFs Fs).gateCount = (∑ j : Fin Fs.length, Fs[j].complexity) + Fs.length + 1 := by
  simp [gateCount, ofCNFs, BottomIndex, Fintype.card_sigma, Complexity.CNF.complexity]

end Complexity.DepthThreeLowerBound.Circuit3


namespace Complexity.DepthThreeLowerBound

lemma language_or_cnf_lower_bound_proof (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ Fs : List (Complexity.CNF n),
      (∀ x, Fs.any (fun F => F.eval x) = language (List.ofFn x)) →
      (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) <
        ((∑ j : Fin Fs.length, Fs[j].complexity) + Fs.length + 1 : ℕ) := by
  obtain ⟨N, hN⟩ := language_depth_three_gate_lower_bound A hA
  refine ⟨N, fun n hn Fs hFs => ?_⟩
  have h := hN n hn (Circuit3.ofCNFs Fs) (fun x => by rw [Circuit3.eval_ofCNFs_proof]; exact hFs x)
  simpa only [Circuit3.gateCount_ofCNFs_proof] using h

lemma language_cnf_threshold_weight_proof (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → Complexity.CNF n) (a : J → ℝ),
        (∀ j, (H j).width ≤ degreeCutoff s (dataDimension n)) →
        (∀ x, 1 ≤ sign (language (List.ofFn x)) * ∑ j, a j * indicator ((H j).eval x)) →
        (2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 ≤
          ∑ j, |a j| := by
  obtain ⟨N, hN, hb⟩ := language_threshold_weight s hs
  refine ⟨N, hN, fun n hn J _ H a hwidth hmargin => ?_⟩
  apply hb n hn J (fun j => (H j).toDepthThree) a
  · intro j C hC
    exact ((H j).width_toDepthThree_proof C hC).trans (hwidth j)
  · simpa only [Complexity.CNF.eval_toDepthThree_proof] using hmargin

lemma language_cnf_integer_threshold_weight_proof (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → Complexity.CNF n) (z : J → ℤ),
        (∀ j, (H j).width ≤ degreeCutoff s (dataDimension n)) →
        (∀ x, language (List.ofFn x) =
          decide (0 ≤ ∑ j, z j * if (H j).eval x then (1 : ℤ) else 0)) →
        ((2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 - 1) / 2 ≤
          ∑ j, |(z j : ℝ)| := by
  obtain ⟨N, hN, hb⟩ := language_integer_threshold_weight s hs
  refine ⟨N, hN, fun n hn J _ H z hwidth heval => ?_⟩
  apply hb n hn J (fun j => (H j).toDepthThree) z
  · intro j C hC
    exact ((H j).width_toDepthThree_proof C hC).trans (hwidth j)
  · simpa only [Complexity.CNF.eval_toDepthThree_proof] using heval

end Complexity.DepthThreeLowerBound
