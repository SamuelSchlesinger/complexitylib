/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Internal

/-!
# Uniform evaluation and robustness of majority

The final majority stage in Chattopadhyay and Liao's constant-error sumset
extractor has a uniform polynomial-time evaluator in Complexitylib's machine
model. A strict good-coordinate margin larger than the number of bad coordinates
forces the verdict, regardless of how the bad bits depend on the good bits.

These are only properties of the final stage; no sumset-extraction guarantee is
claimed without the preceding source reduction and its probabilistic analysis.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Majority agrees exactly with the existing finite-vector majority, under
the standard list encoding. -/
@[simp] theorem majorityEval_toList {n : Nat} (x : Complexity.BitString n) :
    majorityEval x.toList = [Complexity.majority x] :=
  Internal.majorityEval_toList x

/-- The majority evaluator is uniform polynomial time in the repository's
deterministic Turing-machine model. -/
theorem majorityEval_mem_FP : majorityEval ∈ Complexity.FP :=
  Internal.majorityEval_mem_FP

/-- More positive good votes than all possible negative bad votes forces a
true majority, without any independence condition on the bad coordinates. -/
theorem majority_eq_true_of_margin {n : Nat} {good : Finset (Fin n)}
    {x : Fin n → Bool} (h : ((n - good.card : Nat) : Int) < voteMargin good x) :
    Complexity.majority x = true :=
  Internal.majority_eq_true_of_margin h

/-- A sufficiently negative good margin forces false even if every bad
coordinate votes true. Ties follow the evaluator's false convention. -/
theorem majority_eq_false_of_margin {n : Nat} {good : Finset (Fin n)}
    {x : Fin n → Bool} (h : voteMargin good x ≤ -((n - good.card : Nat) : Int)) :
    Complexity.majority x = false :=
  Internal.majority_eq_false_of_margin h

end Algebraic.Cutwidth.Extractor
