/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Numerical.Defs

/-!
# Correctness of canonical numerical expansion

The two blocks of the extended vocabulary respectively recover the input
relations and the designated numerical predicates. Forgetting the second block
recovers the original structure, so the existing interpretation transport theorem
also proves correctness of embedding input formulas.
-/

public section

namespace Complexity.DescriptiveComplexity

private theorem forgetNumerical_rel {V : Vocabulary} (A : FinStruct V)
    (predicates : List NumericalPredicate) :
    ((FOInterpretation.forgetNumerical V predicates).apply (A.withNumerical predicates)).rel =
      A.rel := by
  funext r args
  simp [FOInterpretation.apply, FOInterpretation.forgetNumerical, Formula.Sat, Term.eval,
    FinStruct.withNumerical, Vocabulary.withNumerical]
  rfl

theorem forgetNumerical_apply_internal {V : Vocabulary} (A : FinStruct V)
    (predicates : List NumericalPredicate) :
    (FOInterpretation.forgetNumerical V predicates).apply (A.withNumerical predicates) = A := by
  rw [show (FOInterpretation.forgetNumerical V predicates).apply (A.withNumerical predicates) =
    { A with rel :=
      ((FOInterpretation.forgetNumerical V predicates).apply (A.withNumerical predicates)).rel }
    from rfl, forgetNumerical_rel A predicates]

theorem withNumerical_sat_internal {V : Vocabulary} {n : Nat} (A : FinStruct V)
    (φ : Formula V n) (predicates : List NumericalPredicate) (σ : Env A.card n) :
    (φ.withNumerical predicates).Sat (A.withNumerical predicates) σ ↔ φ.Sat A σ := by
  have h := (FOInterpretation.forgetNumerical V predicates).translate_sat
    (A.withNumerical predicates) σ φ
  change Formula.Sat { A with rel :=
    ((FOInterpretation.forgetNumerical V predicates).apply (A.withNumerical predicates)).rel }
      σ φ ↔ _ at h
  rw [forgetNumerical_rel] at h
  exact h.symm

theorem numerical_sat_internal {V : Vocabulary} {n : Nat} (A : FinStruct V)
    (predicates : List NumericalPredicate) (r : Fin predicates.length)
    (args : Fin (predicates.get r).arity → Term (V.withNumerical predicates) n)
    (σ : Env A.card n) :
    (Formula.numerical predicates r args).Sat (A.withNumerical predicates) σ ↔
      (predicates.get r).Holds
        (fun i => (Term.eval (A.withNumerical predicates) σ (args i)).val) := by
  simp [Formula.numerical, Formula.Sat, FinStruct.withNumerical, Vocabulary.withNumerical]
  rfl

theorem withNumerical_toFinStruct_internal {V : Vocabulary} (A : DecFinStruct V)
    (predicates : List NumericalPredicate) :
    (A.withNumerical predicates).toFinStruct = A.toFinStruct.withNumerical predicates := by
  have hrel : (A.withNumerical predicates).toFinStruct.rel =
      (A.toFinStruct.withNumerical predicates).rel := by
    funext r
    refine Fin.addCases (fun i => ?_) (fun j => ?_) r
    · simp [DecFinStruct.toFinStruct, DecFinStruct.withNumerical,
        FinStruct.withNumerical, Vocabulary.withNumerical]
    · simp [DecFinStruct.toFinStruct, DecFinStruct.withNumerical,
        FinStruct.withNumerical, Vocabulary.withNumerical]
      funext args
      exact decide_eq_true_eq
  rw [show (A.withNumerical predicates).toFinStruct =
    { A.toFinStruct.withNumerical predicates with
      rel := (A.withNumerical predicates).toFinStruct.rel }
    from rfl, hrel]

end Complexity.DescriptiveComplexity
