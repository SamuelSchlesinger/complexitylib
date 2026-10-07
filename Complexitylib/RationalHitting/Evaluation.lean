/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.RationalHitting.Internal.Detection

/-!
# Exact matrix evaluation and consequences of hitting lists

These deductions use OpenAI's rational-formula semantics. Inverse is partial:
every evaluated inverse node must have a genuine two-sided inverse.

A hitting list detects nonzeroness by an invertible value. With two extra
syntax nodes in the size bound, it also detects admissibility, including for
identically zero formulas. The executable tests here have correctness proofs;
no polynomial bound for their rational arithmetic is asserted.
-/

public section

namespace Complexity.RationalHitting

/-- The executable evaluator returns exactly the values admitted by the evaluation relation. -/
theorem Formula.evalMatrix?_eq_some_iff {n d : ℕ} (f : Formula n) (X : Tuple n d)
    (v : Mat d) : f.evalMatrix? X = some v ↔ Evaluates f X v :=
  ⟨Internal.evalMatrix_sound f X, Internal.evalMatrix_complete⟩

/-- A nonzero evaluation already supplies a point in the formula's domain. -/
theorem Nonzero.admissible {n : ℕ} {f : Formula n} (hf : Nonzero f) : Admissible f :=
  Internal.nonzero_admissible hf

/-- Positive dimension makes an invertible hitting value a nonzero witness. -/
theorem Hits.nonzero_iff {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.size ≤ s) :
    Nonzero f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v :=
  Internal.hits_nonzero_iff hH f hf

/-- At any defined point, either the value of `f` or the value of `f + 1` is nonzero. -/
theorem admissible_nonzero_or_add_one {n : ℕ} (f : Formula n) (hf : Admissible f) :
    Nonzero f ∨ Nonzero (.add f (.const 1)) :=
  Internal.admissible_nonzero_or_add_one f hf

/-- A hitting list with a size allowance of two also detects the domain of every formula. -/
theorem Hits.admissible_iff {n s : ℕ} {H : Output n} (hH : Hits (s + 2) H)
    (f : Formula n) (hf : f.size ≤ s) :
    Admissible f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v :=
  Internal.hits_admissible_iff hH f hf

/-- An invertible hit turns a nonzero formula into one with an admissible inverse. -/
theorem Hits.admissible_inv_iff_nonzero {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.size ≤ s) : Admissible (.inv f) ↔ Nonzero f :=
  Internal.hits_admissible_inv_iff_nonzero hH f hf

/-- The executable domain test searches exactly the defined evaluations on the list. -/
theorem Output.admissibilityTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.admissibilityTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v :=
  Internal.admissibilityTest_iff H f

/-- The executable determinant test searches exactly the invertible evaluations on the list. -/
theorem Output.nonzeroTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.nonzeroTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v :=
  Internal.nonzeroTest_iff H f

/-- A hitting list for size `s + 2` decides admissibility of formulas of size at most `s`. -/
theorem Hits.admissibilityTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits (s + 2) H) (f : Formula n) (hf : f.size ≤ s) :
    H.admissibilityTest f = true ↔ Admissible f :=
  Internal.hits_admissibilityTest_eq_true_iff hH f hf

/-- A hitting list for size `s` decides nonzeroness of formulas of size at most `s`. -/
theorem Hits.nonzeroTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits s H) (f : Formula n) (hf : f.size ≤ s) :
    H.nonzeroTest f = true ↔ Nonzero f :=
  Internal.hits_nonzeroTest_eq_true_iff hH f hf

end Complexity.RationalHitting
