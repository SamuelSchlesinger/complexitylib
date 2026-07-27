/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.NormalForm.Operations.Defs
public import Complexitylib.Circuits.NormalForm.Operations.Internal

/-!
# Operations on CNF and DNF

Disjunction of DNFs and conjunction of CNFs preserve the largest component
width and add component counts. These operations let a layer of bounded-depth
decision trees be assembled into the matching normal form without a
distributive expansion.
-/

@[expose] public section

namespace Complexity

namespace DNF

/-- Disjoining DNFs agrees with disjoining their Boolean values. -/
theorem eval_disjoin (formulas : List (DNF N))
    (input : BitString N) :
    (disjoin formulas).eval input =
      formulas.any fun formula => formula.eval input :=
  eval_disjoin_internal formulas input

/-- Disjoining DNFs cannot exceed a common width bound. -/
theorem width_disjoin_le
    (formulas : List (DNF N)) (bound : ℕ)
    (hbound :
      ∀ formula ∈ formulas, formula.width ≤ bound) :
    (disjoin formulas).width ≤ bound :=
  width_disjoin_le_internal formulas bound hbound

/-- DNF disjunction adds the numbers of terms exactly. -/
theorem complexity_disjoin
    (formulas : List (DNF N)) :
    (disjoin formulas).complexity =
      (formulas.map DNF.complexity).sum :=
  complexity_disjoin_internal formulas

end DNF

namespace CNF

/-- Conjoining CNFs agrees with conjoining their Boolean values. -/
theorem eval_conjoin (formulas : List (CNF N))
    (input : BitString N) :
    (conjoin formulas).eval input =
      formulas.all fun formula => formula.eval input :=
  eval_conjoin_internal formulas input

/-- Conjoining CNFs cannot exceed a common width bound. -/
theorem width_conjoin_le
    (formulas : List (CNF N)) (bound : ℕ)
    (hbound :
      ∀ formula ∈ formulas, formula.width ≤ bound) :
    (conjoin formulas).width ≤ bound :=
  width_conjoin_le_internal formulas bound hbound

/-- CNF conjunction adds the numbers of clauses exactly. -/
theorem complexity_conjoin
    (formulas : List (CNF N)) :
    (conjoin formulas).complexity =
      (formulas.map CNF.complexity).sum :=
  complexity_conjoin_internal formulas

end CNF

end Complexity
