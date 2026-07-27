/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.NormalForm.Operations.Defs

/-!
# Operations on CNF and DNF -- proof internals
-/

@[expose] public section

namespace Complexity

namespace DNF

theorem eval_disjoin_internal (formulas : List (DNF N))
    (input : BitString N) :
    (disjoin formulas).eval input =
      formulas.any fun formula => formula.eval input := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [disjoin, List.flatMap_cons, eval,
        List.any_append, List.any_cons]
      have htail :
          (List.flatMap terms formulas).any
              (fun term =>
                term.all fun literal => literal.eval input) =
            formulas.any fun found => found.eval input := by
        simpa only [disjoin, eval] using ih
      rw [htail]
      rfl

theorem width_disjoin_le_internal
    (formulas : List (DNF N)) (bound : ℕ)
    (hbound :
      ∀ formula ∈ formulas, formula.width ≤ bound) :
    (disjoin formulas).width ≤ bound := by
  rw [DNF.width_le_iff]
  intro term hterm
  simp only [disjoin] at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨formula, hformula, hterm⟩ := hterm
  exact (formula.length_le_width term hterm).trans
    (hbound formula hformula)

theorem complexity_disjoin_internal
    (formulas : List (DNF N)) :
    (disjoin formulas).complexity =
      (formulas.map DNF.complexity).sum := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [disjoin, complexity, List.flatMap_cons,
        List.length_append, List.map_cons, List.sum_cons]
      exact congrArg (formula.terms.length + ·) ih

end DNF

namespace CNF

theorem eval_conjoin_internal (formulas : List (CNF N))
    (input : BitString N) :
    (conjoin formulas).eval input =
      formulas.all fun formula => formula.eval input := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [conjoin, List.flatMap_cons, eval,
        List.all_append, List.all_cons]
      have htail :
          (List.flatMap clauses formulas).all
              (fun clause =>
                clause.any fun literal => literal.eval input) =
            formulas.all fun found => found.eval input := by
        simpa only [conjoin, eval] using ih
      rw [htail]
      rfl

theorem width_conjoin_le_internal
    (formulas : List (CNF N)) (bound : ℕ)
    (hbound :
      ∀ formula ∈ formulas, formula.width ≤ bound) :
    (conjoin formulas).width ≤ bound := by
  rw [CNF.width_le_iff]
  intro clause hclause
  simp only [conjoin] at hclause
  rw [List.mem_flatMap] at hclause
  obtain ⟨formula, hformula, hclause⟩ := hclause
  exact (formula.length_le_width clause hclause).trans
    (hbound formula hformula)

theorem complexity_conjoin_internal
    (formulas : List (CNF N)) :
    (conjoin formulas).complexity =
      (formulas.map CNF.complexity).sum := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [conjoin, complexity, List.flatMap_cons,
        List.length_append, List.map_cons, List.sum_cons]
      exact congrArg (formula.clauses.length + ·) ih

end CNF

end Complexity
