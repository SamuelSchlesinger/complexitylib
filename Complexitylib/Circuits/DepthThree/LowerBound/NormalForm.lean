/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.NormalForm.Defs
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageLowerBound
import Complexitylib.Circuits.DepthThree.LowerBound.Internal.NormalForm

/-!
# Depth-three and threshold-weight bounds for canonical CNFs

These theorems use complexitylib's existing `CNF` rather than requiring source-specific
formulas. The unrestricted gate bound counts clauses plus CNFs plus one; the coefficient
bounds count absolute real or integer weights, including any constant feature.
-/

public section

namespace Complexity.CNF

/-- CNF conversion preserves evaluation, including empty clauses and conjunctions. -/
theorem eval_toDepthThree (F : CNF n) (x : BitString n) :
    F.toDepthThree.eval x = F.eval x :=
  eval_toDepthThree_proof F x

/-- The converted width is bounded by the canonical clause-length width. -/
theorem width_toDepthThree (F : CNF n) : F.toDepthThree.WidthAtMost F.width :=
  width_toDepthThree_proof F

end Complexity.CNF

namespace Complexity.DepthThreeLowerBound.Circuit3

/-- Conversion of a clause preserves its disjunction. -/
theorem eval_clauseInputs (C : List (Complexity.Literal n)) (x : BitString n) :
    (clauseInputs C).eval x = C.any (fun l => l.eval x) :=
  eval_clauseInputs_proof C x

/-- Each middle gate computes its corresponding canonical CNF. -/
theorem middleEval_ofCNFs (Fs : List (Complexity.CNF n)) (j : Fin Fs.length)
    (x : BitString n) : (ofCNFs Fs).middleEval j x = Fs[j].eval x :=
  middleEval_ofCNFs_proof Fs j x

/-- The converted three-layer circuit computes the OR of the input CNFs. -/
theorem eval_ofCNFs (Fs : List (Complexity.CNF n)) (x : BitString n) :
    (ofCNFs Fs).eval x = Fs.any (fun F => F.eval x) :=
  eval_ofCNFs_proof Fs x

/-- The exact cost is the number of clauses, plus the CNFs, plus the top gate. -/
theorem gateCount_ofCNFs (Fs : List (Complexity.CNF n)) :
    (ofCNFs Fs).gateCount = (∑ j : Fin Fs.length, Fs[j].complexity) + Fs.length + 1 :=
  gateCount_ofCNFs_proof Fs

end Complexity.DepthThreeLowerBound.Circuit3

namespace Complexity.DepthThreeLowerBound

/-- The full hard language needs the stated total number of OR-of-CNF gates.
This counts every clause, every CNF, and the top OR; it does not bound top fan-in alone. -/
theorem language_or_cnf_lower_bound (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ Fs : List (Complexity.CNF n),
      (∀ x, Fs.any (fun F => F.eval x) = language (List.ofFn x)) →
      (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) <
        ((∑ j : Fin Fs.length, Fs[j].complexity) + Fs.length + 1 : ℕ) :=
  language_or_cnf_lower_bound_proof A hA

/-- The margin-one weight lower bound for complexitylib's canonical CNFs. -/
theorem language_cnf_threshold_weight (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → Complexity.CNF n) (a : J → ℝ),
        (∀ j, (H j).width ≤ degreeCutoff s (dataDimension n)) →
        (∀ x, 1 ≤ sign (language (List.ofFn x)) * ∑ j, a j * indicator ((H j).eval x)) →
        (2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 ≤
          ∑ j, |a j| :=
  language_cnf_threshold_weight_proof s hs

/-- The integer threshold-weight lower bound for canonical CNFs; ties accept. -/
theorem language_cnf_integer_threshold_weight (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → Complexity.CNF n) (z : J → ℤ),
        (∀ j, (H j).width ≤ degreeCutoff s (dataDimension n)) →
        (∀ x, language (List.ofFn x) =
          decide (0 ≤ ∑ j, z j * if (H j).eval x then (1 : ℤ) else 0)) →
        ((2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 - 1) / 2 ≤
          ∑ j, |(z j : ℝ)| :=
  language_cnf_integer_threshold_weight_proof s hs

end Complexity.DepthThreeLowerBound
