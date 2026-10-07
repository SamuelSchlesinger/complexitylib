/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Balanced.Defs
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageLowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding

/-!
# Balanced hardness under both depth-three polarities

Fix the fresh input bit to recover the original hard function from either
output polarity. Input substitution preserves the number of gates.
The existing balanced-padding count gives exactly half of the input cube.
-/

public section

namespace Complexity.DepthThreeLowerBound

lemma balancedLanguage_ofFn_proof (n : ℕ) (x : Cube (Fin (n + 1))) :
    balancedLanguage (List.ofFn x) = balancedFamily n x := by
  change Bool.xor (language (List.ofFn x).tail) ((List.ofFn x).headD false) =
    Bool.xor (language (List.ofFn (Fin.tail x))) (x 0)
  rw [List.ofFn_succ]
  rfl

lemma balancedFamily_card_proof (n : ℕ) :
    (Algebraic.Cutwidth.accepting (balancedFamily n)).card = 2 ^ n :=
  Algebraic.Cutwidth.card_accepting_balancePad _

lemma balancedFamily_restrict (n : ℕ) (b : Bool) :
    ∃ α : Fin (n + 1) → Sum (Fin n) Bool,
      ∀ x, Bool.xor (balancedFamily n (GateInput.assignment α x)) b =
        language (List.ofFn x) := by
  let α : Fin (n + 1) → Sum (Fin n) Bool := Fin.cases (.inr b) (fun i => .inl i)
  refine ⟨α, ?_⟩
  intro x
  have he : GateInput.assignment α x = Fin.cons b x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [α, GateInput.assignment]
  rw [he]
  simp [balancedFamily, Algebraic.Cutwidth.balancePad]

lemma balancedFamily_lower_bound_proof (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ b : Bool, ∀ D : Circuit3 (Fin (n + 1)),
      D.Computes (fun x => Bool.xor (balancedFamily n x) b) →
        (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (D.gateCount : ℝ) := by
  obtain ⟨N, hN⟩ := language_depth_three_gate_lower_bound (2 * A) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro n hn b D hD
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨α, hα⟩ := balancedFamily_restrict n b
  have hc : (D.subst α).Computes (fun x => language (List.ofFn x)) := by
    intro x
    rw [Circuit3.eval_subst, hD]
    exact hα x
  have hl := hN n hnN (D.subst α) hc
  have hsqrt : Real.sqrt (n + 1 : ℕ) ≤ 2 * Real.sqrt (n : ℝ) := by
    calc
      _ ≤ Real.sqrt (4 * (n : ℝ)) := Real.sqrt_le_sqrt (by
        exact_mod_cast (show n + 1 ≤ 4 * n by lia))
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have he : A * Real.sqrt (n + 1 : ℕ) ≤ (2 * A) * Real.sqrt (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hA.le]
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he).trans_lt hl

lemma Circuit3.dualEval_eq_not_eval_proof {V : Type*} (C : Circuit3 V) (x : Cube V) :
    C.dualEval x = !C.eval x := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [dualEval, Circuit3.eval, Circuit3.middleEval, RawClause.eval]

lemma balancedFamily_both_polarities_proof (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D : Circuit3 (Fin (n + 1)),
      (D.Computes (balancedFamily n) ∨ D.ComputesDual (balancedFamily n)) →
        (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (D.gateCount : ℝ) := by
  obtain ⟨N, hN⟩ := balancedFamily_lower_bound_proof A hA
  refine ⟨N, ?_⟩
  intro n hn D hD
  rcases hD with hD | hD
  · apply hN n hn false D
    simpa only [Bool.xor_false] using hD
  · apply hN n hn true D
    intro x
    have he := congrArg Bool.not (hD x)
    simpa only [Circuit3.dualEval_eq_not_eval_proof, Bool.not_not, Bool.xor_true] using he

end Complexity.DepthThreeLowerBound
