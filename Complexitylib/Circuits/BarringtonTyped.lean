/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonTyped.Defs
public import Complexitylib.Circuits.BarringtonTyped.Internal

/-!
# Fixed-arity nonuniform Barrington theorem

This is the typed version of Barrington's theorem. At every input length, a
formula or branching program carries a proof that it reads only variables in
that fixed arity. Both sides denote `BoolFunFamily`; the branching-program
model stores the unique zero-input answer separately.

## Main results

* `fixedArityFormulaFamily_exists_bp` -- logarithmic-depth formulas compile to
  polynomial-length, variable-bounded width-`5` programs.
* `fixedArityBPFamily_exists_formula` -- balanced formulas give the converse.
* `barrington_equivalence` -- the typed nonuniform class equivalence.
-/

@[expose] public section

namespace Complexity

/-- Every fixed-arity logarithmic-depth formula family has an equivalent
fixed-arity polynomial-length width-`5` branching-program family. -/
theorem fixedArityFormulaFamily_exists_bp
    (F : FixedArityFormulaFamily) (hF : F.LogDepth) :
    ∃ R : FixedArityBPFamily 5,
      R.PolynomialLength ∧ R.function = F.function :=
  fixedArityFormulaFamily_exists_bp_internal F hF

/-- Every fixed-arity polynomial-length width-`5` branching-program family has
an equivalent fixed-arity logarithmic-depth formula family. -/
theorem fixedArityBPFamily_exists_formula
    (R : FixedArityBPFamily 5) (hR : R.PolynomialLength) :
    ∃ F : FixedArityFormulaFamily,
      F.LogDepth ∧ F.function = R.function :=
  fixedArityBPFamily_exists_formula_internal R hR

/-- Typed logarithmic-depth formula families are contained in typed
polynomial-length width-`5` branching-program families. -/
theorem formulaNC1_subset_width5BP : FormulaNC1 ⊆ Width5BP :=
  formulaNC1_subset_width5BP_internal

/-- Typed polynomial-length width-`5` branching-program families are
contained in typed logarithmic-depth formula families. -/
theorem width5BP_subset_formulaNC1 : Width5BP ⊆ FormulaNC1 :=
  width5BP_subset_formulaNC1_internal

/-- **Typed nonuniform Barrington theorem.** Variable-bounded,
logarithmic-depth formula families compute exactly the same typed Boolean
function families as variable-bounded, polynomial-length width-`5`
permutation branching programs. -/
theorem barrington_equivalence : FormulaNC1 = Width5BP :=
  Set.Subset.antisymm
    formulaNC1_subset_width5BP
    width5BP_subset_formulaNC1

end Complexity
