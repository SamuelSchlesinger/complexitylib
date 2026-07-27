/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonConverse.Internal

/-!
# The converse direction of Barrington's theorem

Polynomial-length width-`5` permutation branching programs are evaluated by
balanced Boolean formulas of logarithmic depth. Together with the existing
formula-to-program construction, this proves the full nonuniform Barrington
equivalence under the library's total-assignment family convention.

## Main results

- `BP.eval_reachesFormula` -- correctness of balanced state-to-state evaluation
- `BP.depth_reachesFormula_le` -- depth at most `(w + 1) * d + 1`
- `BP.eval_decisionFormula_eq_true` -- the decision formula detects movement
- `BP.depth_decisionFormula_le` -- logarithmic depth in program length
- `BP.vars_decisionFormula_lt` -- conversion preserves an arity bound
- `BPFamily.toFormulaFamily_logDepth` -- polynomial-length families give
  logarithmic-depth formula families
- `barrington_equivalence_onTotalAssignments` -- the explicitly named
  total-assignment equivalence
-/

@[expose] public section

namespace Complexity

/-- Taking a binary ceiling logarithm of a polynomial bound yields an affine
bound in `log₂ n`. This arithmetic bridge is shared by total-assignment and
fixed-arity Barrington converses. -/
theorem clog_le_of_polynomial_bound
    (C p n m : ℕ) (h : m ≤ C * (n + 1) ^ p) :
    Nat.clog 2 m ≤ Nat.clog 2 C + p * (Nat.log 2 n + 1) :=
  clog_le_of_polynomial_bound_internal C p n m h

namespace BP

/-- The balanced state-to-state formula correctly evaluates every program of
length at most `2 ^ d`. -/
theorem eval_reachesFormula {w : ℕ} (α : ℕ → Bool) (d : ℕ) (p : BP w)
    (x y : Fin w) (h : p.length ≤ 2 ^ d) :
    BoolFormula.eval α (reachesFormula d p x y) = true ↔ BP.eval α p x = y :=
  eval_reachesFormula_internal α d p x y h

/-- Balanced state-to-state evaluation has depth at most
`(w + 1) * d + 1`. -/
theorem depth_reachesFormula_le {w : ℕ} (d : ℕ) (p : BP w)
    (x y : Fin w) :
    (reachesFormula d p x y).depth ≤ (w + 1) * d + 1 :=
  depth_reachesFormula_le_internal d p x y

/-- The canonical decision formula is true exactly when the program moves its
designated query point. -/
theorem eval_decisionFormula_eq_true {w : ℕ} (α : ℕ → Bool)
    (p : BP w) (x : Fin w) :
    BoolFormula.eval α (decisionFormula p x) = true ↔ BP.eval α p x ≠ x :=
  eval_decisionFormula_eq_true_internal α p x

/-- The canonical decision formula has logarithmic depth in program length. -/
theorem depth_decisionFormula_le {w : ℕ} (p : BP w) (x : Fin w) :
    (decisionFormula p x).depth ≤ (w + 1) * Nat.clog 2 p.length + 2 :=
  depth_decisionFormula_le_internal p x

/-- The balanced decision formula introduces no new input variables. -/
theorem vars_decisionFormula_lt {w n : ℕ}
    (p : BP w) (x : Fin w)
    (hvars : ∀ instruction ∈ p, instruction.var < n) :
    ∀ index ∈ (decisionFormula p x).vars, index < n :=
  vars_decisionFormula_lt_internal p x hvars

end BP

namespace BPFamily

/-- The balanced formula family computes every function family decided by the
source branching-program family. -/
theorem toFormulaFamily_computes {w : ℕ} {R : BPFamily w}
    {x : ℕ → Fin w} {f : ℕ → (ℕ → Bool) → Bool}
    (h : R.DecidesOnTotalAssignments x f) :
    (R.toFormulaFamily x).ComputesOnTotalAssignments f :=
  toFormulaFamily_computes_internal h

/-- A polynomial-length width-`5` branching-program family becomes a
logarithmic-depth Boolean-formula family. -/
theorem toFormulaFamily_logDepth {R : BPFamily 5} {x : ℕ → Fin 5}
    (h : R.PolynomialLength) :
    (R.toFormulaFamily x).LogDepth :=
  toFormulaFamily_logDepth_internal h

end BPFamily

/-- Every logarithmic-depth total-assignment formula family has a
polynomial-length width-`5` permutation branching-program family. -/
theorem formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments :
    FormulaNC1OnTotalAssignments ⊆ Width5BPOnTotalAssignments :=
  formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments_internal

/-- Every polynomial-length width-`5` total-assignment branching-program
family has an equivalent logarithmic-depth formula family. -/
theorem width5BPOnTotalAssignments_subset_formulaNC1OnTotalAssignments :
    Width5BPOnTotalAssignments ⊆ FormulaNC1OnTotalAssignments :=
  width5BPOnTotalAssignments_subset_formulaNC1OnTotalAssignments_internal

/-- **Barrington's theorem on total assignments.** Logarithmic-depth Boolean
formula families are exactly polynomial-length width-`5` permutation
branching-program families over assignments `ℕ → Bool`.

This theorem does not claim that the length-`n` objects only read the first
`n` variables; the typed fixed-arity theorem is a separate statement. -/
theorem barrington_equivalence_onTotalAssignments :
    FormulaNC1OnTotalAssignments = Width5BPOnTotalAssignments :=
  Set.Subset.antisymm
    formulaNC1OnTotalAssignments_subset_width5BPOnTotalAssignments
    width5BPOnTotalAssignments_subset_formulaNC1OnTotalAssignments

end Complexity
