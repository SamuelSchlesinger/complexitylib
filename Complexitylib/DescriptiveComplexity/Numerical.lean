/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Numerical.Defs
import Complexitylib.DescriptiveComplexity.Numerical.Internal

/-!
# First-order logic with canonical numerical predicates

Canonical expansions make order, BIT, addition, and multiplication available to
the existing FO syntax. Numerical atoms have their specified natural-number
semantics; input formulas embed without changing truth. The computable expansion
agrees with its propositional counterpart, so the existing Boolean evaluator can
check formulas on these expansions.

This supplies the semantic interfaces for FO[BIT] and FO[ADD, MUL]. Their equality
of expressive power, formula definitions of one arithmetic basis from the other,
and the uniform circuit capture theorem remain separate results.
-/

public section

namespace Complexity.DescriptiveComplexity

variable {V : Vocabulary} {n : Nat}

/-- Canonical numerical expansion preserves the universe exactly. -/
@[simp] theorem FinStruct.withNumerical_card (A : FinStruct V)
    (predicates : List NumericalPredicate) : (A.withNumerical predicates).card = A.card := rfl

/-- Forgetting the added symbols recovers the original structure. -/
@[simp] theorem FOInterpretation.forgetNumerical_apply (A : FinStruct V)
    (predicates : List NumericalPredicate) :
    (forgetNumerical V predicates).apply (A.withNumerical predicates) = A :=
  forgetNumerical_apply_internal A predicates

/-- Embedding an input formula into the numerical vocabulary preserves satisfaction. -/
@[simp] theorem Formula.withNumerical_sat (A : FinStruct V) (φ : Formula V n)
    (predicates : List NumericalPredicate) (σ : Env A.card n) :
    (φ.withNumerical predicates).Sat (A.withNumerical predicates) σ ↔ φ.Sat A σ :=
  withNumerical_sat_internal A φ predicates σ

/-- A designated numerical atom has its canonical meaning on the evaluated arguments. -/
@[simp] theorem Formula.numerical_sat (A : FinStruct V)
    (predicates : List NumericalPredicate) (r : Fin predicates.length)
    (args : Fin (predicates.get r).arity → Term (V.withNumerical predicates) n)
    (σ : Env A.card n) :
    (numerical predicates r args).Sat (A.withNumerical predicates) σ ↔
      (predicates.get r).Holds (fun i => (Term.eval (A.withNumerical predicates) σ (args i)).val) :=
  numerical_sat_internal A predicates r args σ

/-- The order atom compares the natural indices of its two elements. -/
@[simp] theorem Formula.orderLt_sat (A : FinStruct V) (x y : Term V.withOrder n)
    (σ : Env A.card n) :
    (orderLt x y).Sat (A.withNumerical [.lt]) σ ↔
      (x.eval (A.withNumerical [.lt]) σ).val < (y.eval (A.withNumerical [.lt]) σ).val := by
  simp [orderLt, NumericalPredicate.Holds]

/-- BIT reads the indicated zero-based bit of the element's natural index. -/
@[simp] theorem Formula.bit_sat (A : FinStruct V) (x i : Term V.withBit n)
    (σ : Env A.card n) :
    (bit x i).Sat (A.withNumerical [.bit]) σ ↔
      (x.eval (A.withNumerical [.bit]) σ).val.testBit
        (i.eval (A.withNumerical [.bit]) σ).val = true := by
  simp [bit, NumericalPredicate.Holds]

/-- ADD is the graph of natural addition, with all three elements in the finite universe. -/
@[simp] theorem Formula.add_sat (A : FinStruct V) (x y z : Term V.withArithmetic n)
    (σ : Env A.card n) :
    (add x y z).Sat (A.withNumerical [.add, .mul]) σ ↔
      (x.eval (A.withNumerical [.add, .mul]) σ).val +
        (y.eval (A.withNumerical [.add, .mul]) σ).val =
          (z.eval (A.withNumerical [.add, .mul]) σ).val := by
  simp [add, NumericalPredicate.Holds]

/-- MUL is the graph of natural multiplication, without modular wraparound. -/
@[simp] theorem Formula.mul_sat (A : FinStruct V) (x y z : Term V.withArithmetic n)
    (σ : Env A.card n) :
    (mul x y z).Sat (A.withNumerical [.add, .mul]) σ ↔
      (x.eval (A.withNumerical [.add, .mul]) σ).val *
        (y.eval (A.withNumerical [.add, .mul]) σ).val =
          (z.eval (A.withNumerical [.add, .mul]) σ).val := by
  simp [mul, NumericalPredicate.Holds]

/-- The computable expansion has exactly the specified propositional semantics. -/
@[simp] theorem DecFinStruct.withNumerical_toFinStruct (A : DecFinStruct V)
    (predicates : List NumericalPredicate) :
    (A.withNumerical predicates).toFinStruct = A.toFinStruct.withNumerical predicates :=
  withNumerical_toFinStruct_internal A predicates

/-- Every input FO definition remains a definition after adding numerical predicates. -/
theorem FODefinable.withNumerical {Q : BooleanQuery V} (hQ : FODefinable Q)
    (predicates : List NumericalPredicate) : FODefinableWithNumerical predicates Q := by
  obtain ⟨φ, hφ⟩ := hQ
  refine ⟨φ.withNumerical predicates, fun A => ?_⟩
  exact (hφ A).trans (Formula.withNumerical_sat A φ predicates (emptyEnv A.card)).symm

end Complexity.DescriptiveComplexity
