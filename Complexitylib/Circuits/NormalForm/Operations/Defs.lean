/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.NormalForm.Defs

/-!
# Operations on CNF and DNF -- definitions

Disjoining DNFs concatenates their term lists. Dually, conjoining CNFs
concatenates their clause lists. These are the width-preserving operations
used when one alternating formula layer is assembled from normal forms for
its children.
-/

@[expose] public section

namespace Complexity

namespace DNF

/-- Disjoin a finite list of DNFs by concatenating all of their terms. -/
def disjoin (formulas : List (DNF N)) : DNF N :=
  ⟨formulas.flatMap DNF.terms⟩

end DNF

namespace CNF

/-- Conjoin a finite list of CNFs by concatenating all of their clauses. -/
def conjoin (formulas : List (CNF N)) : CNF N :=
  ⟨formulas.flatMap CNF.clauses⟩

end CNF

end Complexity
