/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.BoundedFailure
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Atoms
public import Mathlib.Data.Fintype.Card

/-!
# Dyadic fusion for arithmetic circuits

Many arithmetic complexity measures obey a maximum rule for addition and a
sum rule for multiplication.  Degree is the basic example.  If all generators
and constants have measure at most one, a value of measure at least `2 ^ n`
requires `n` successive dyadic threshold crossings.

This file realizes that argument as a genuine fusion model.  Its witnesses are
the thresholds `2 ^ k`, for `k < n`.  Addition and constants preserve every
witness.  A multiplication can violate at most one witness, since two inputs
below `2 ^ k` produce a result below `2 ^ (k + 1)`.  Therefore a fusion cover
contains at least `n` multiplication atoms, and the generic circuit-to-cover
theorem gives an exact multiplicative-complexity lower bound.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Dyadic

open Algebraic.Fusion.Arithmetic

/-- A natural-valued arithmetic measure with degree-like local bounds. -/
structure Measure
    (K : Type u)
    (R : Type v)
    [Add R]
    [Mul R]
    (constant : K → R) where
  /-- Complexity assigned to a semantic arithmetic value. -/
  value : R → Nat
  /-- Addition is maximum-bounded. -/
  add_le : ∀ left right,
    value (left + right) ≤ max (value left) (value right)
  /-- Multiplication is sum-bounded. -/
  mul_le : ∀ left right,
    value (left * right) ≤ value left + value right
  /-- Every named constant starts below the first dyadic threshold. -/
  constant_le_one : ∀ scalar, value (constant scalar) ≤ 1

variable {K : Type u} {R : Type v}
variable [Add R] [Mul R]
variable {constant : K → R}

/-- Fusion model whose observations are dyadic upper bounds on an arithmetic
measure. -/
def model
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target) :
    Model (Arithmetic.multiplicationCost (K := K))
      (Arithmetic.interpretation constant) problem where
  Witness := Fin levels
  reference _ _ := True
  observed level value := measure.value value ≤ 2 ^ level.1
  input_sound := by
    intro level input _
    exact (input_le_one input).trans
      (Nat.one_le_pow level.1 2 (by decide))
  target_reference := by
    intro _
    trivial
  target_not_observed := by
    intro level observed
    have power_lt : 2 ^ level.1 < 2 ^ levels :=
      Nat.pow_lt_pow_right (by decide) level.2
    exact (Nat.not_le_of_lt power_lt) (target_ge.trans observed)

/-- The dyadic model has the canonical finite witness enumeration. -/
noncomputable instance witnessFintype
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target) :
    Fintype (model measure problem levels input_le_one target_ge).Witness := by
  unfold model
  infer_instance

@[simp] theorem witness_card
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target) :
    Fintype.card (model measure problem levels input_le_one target_ge).Witness =
      levels := by
  change Fintype.card (Fin levels) = levels
  simp

/-- Addition preserves every dyadic witness. -/
theorem add_preserved
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (arguments : Fin 2 → R)
    (level : Fin levels) :
    (⟨.add, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
      (model measure problem levels input_le_one target_ge) level := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result, model,
    Arithmetic.interpretation, true_implies]
  intro argumentsBound
  exact (measure.add_le _ _).trans
    (max_le (argumentsBound (0 : Fin 2))
      (argumentsBound (1 : Fin 2)))

/-- Named constants preserve every dyadic witness. -/
theorem constant_preserved
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (scalar : K)
    (arguments : Fin (Arithmetic.arity (.constant scalar)) → R)
    (level : Fin levels) :
    (⟨.constant scalar, arguments⟩ :
      Atom (Arithmetic.signature K) R).PreservedBy
        (model measure problem levels input_le_one target_ge) level := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result, model,
    Arithmetic.interpretation, true_implies]
  intro _
  exact (measure.constant_le_one scalar).trans
    (Nat.one_le_pow level.1 2 (by decide))

/-- Failure of a multiplication atom supplies bounds on both arguments and a
strictly larger result. -/
theorem bounds_of_mul_not_preserved
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (arguments : Fin 2 → R)
    (level : Fin levels)
    (failure : ¬
      (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
        (model measure problem levels input_le_one target_ge) level) :
    (∀ input, measure.value (arguments input) ≤ 2 ^ level.1) ∧
      2 ^ level.1 < measure.value
        (arguments (0 : Fin 2) * arguments (1 : Fin 2)) := by
  classical
  simp only [Atom.PreservedBy, Model.Sound, Atom.result, model,
    Arithmetic.interpretation, true_implies] at failure
  exact (Classical.not_imp.mp failure).imp_right (Nat.lt_of_not_ge ·)

/-- One multiplication cannot cross two distinct dyadic thresholds. -/
theorem mul_failure_unique
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (arguments : Fin 2 → R)
    (first second : Fin levels)
    (firstFailure : ¬
      (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
        (model measure problem levels input_le_one target_ge) first)
    (secondFailure : ¬
      (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
        (model measure problem levels input_le_one target_ge) second) :
    first = second := by
  have impossible_of_lt : ∀ {lower upper : Fin levels},
      lower.1 < upper.1 →
      ¬ (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
          (model measure problem levels input_le_one target_ge) lower →
      ¬ (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
          (model measure problem levels input_le_one target_ge) upper →
      False := by
    intro lower upper lower_lt lowerFailure upperFailure
    have lowerBounds := bounds_of_mul_not_preserved measure problem levels
      input_le_one target_ge arguments lower lowerFailure
    have upperBounds := bounds_of_mul_not_preserved measure problem levels
      input_le_one target_ge arguments upper upperFailure
    have result_le_double : measure.value
        (arguments (0 : Fin 2) * arguments (1 : Fin 2)) ≤
        2 ^ lower.1 + 2 ^ lower.1 :=
      (measure.mul_le _ _).trans (Nat.add_le_add
        (lowerBounds.1 (0 : Fin 2))
        (lowerBounds.1 (1 : Fin 2)))
    have result_le_next : measure.value
        (arguments (0 : Fin 2) * arguments (1 : Fin 2)) ≤
        2 ^ (lower.1 + 1) := by
      simpa [pow_succ, Nat.mul_two] using result_le_double
    have next_le_upper : 2 ^ (lower.1 + 1) ≤ 2 ^ upper.1 := by
      apply Nat.pow_le_pow_right
      · decide
      · omega
    exact (Nat.not_lt_of_ge (result_le_next.trans next_le_upper))
      upperBounds.2
  have not_first_lt_second : ¬ first.1 < second.1 := by
    intro less
    exact impossible_of_lt less firstFailure secondFailure
  have not_second_lt_first : ¬ second.1 < first.1 := by
    intro less
    exact impossible_of_lt less secondFailure firstFailure
  apply Fin.ext
  exact Nat.le_antisymm (Nat.le_of_not_gt not_second_lt_first)
    (Nat.le_of_not_gt not_first_lt_second)

/-- The dyadic local lemmas packaged for the generic bounded-failure arithmetic
interface.  Its capacity is exactly one threshold per multiplication. -/
noncomputable def failureRules
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target) :
    @Fusion.Arithmetic.FailureRules K R _ _ constant problem
      (model measure problem levels input_le_one target_ge)
      (witnessFintype measure problem levels input_le_one target_ge) := by
  letI : Fintype
      (model measure problem levels input_le_one target_ge).Witness :=
    witnessFintype measure problem levels input_le_one target_ge
  refine {
    capacity := 1
    add_preserved :=
      add_preserved measure problem levels input_le_one target_ge
    constant_preserved :=
      constant_preserved measure problem levels input_le_one target_ge
    mul_failure_card_le := ?_
  }
  classical
  intro arguments
  rw [Finset.card_le_one]
  intro first firstPresent second secondPresent
  have firstFailure : ¬
      (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
        (model measure problem levels input_le_one target_ge) first := by
    simpa using firstPresent
  have secondFailure : ¬
      (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
        (model measure problem levels input_le_one target_ge) second := by
    simpa using secondPresent
  exact mul_failure_unique measure problem levels input_le_one target_ge
    arguments first second
    firstFailure secondFailure

@[simp] theorem failureRules_capacity
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target) :
    (failureRules measure problem levels input_le_one target_ge).capacity = 1 := by
  simp [failureRules]

/-- Every dyadic witness has an unpreserved multiplication in a fusion
cover. -/
theorem exists_unpreserved_multiplication
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge))
    (level : Fin levels) :
    ∃ arguments ∈ multiplicationArguments cover.atoms,
      ¬ (⟨.mul, arguments⟩ : Atom (Arithmetic.signature K) R).PreservedBy
        (model measure problem levels input_le_one target_ge) level := by
  classical
  by_contra none
  apply cover.isCover level
  intro atom atomPresent
  cases atom with
  | mk op arguments =>
      cases op with
      | add =>
          exact add_preserved measure problem levels input_le_one target_ge
            arguments level
      | mul =>
          change Fin 2 → R at arguments
          by_contra failure
          apply none
          refine ⟨arguments, ?_, failure⟩
          change arguments ∈ cover.atoms.filterMap Atom.mulArguments?
          rw [List.mem_filterMap]
          exact ⟨⟨.mul, arguments⟩, atomPresent, rfl⟩
      | constant scalar =>
          exact constant_preserved measure problem levels input_le_one
            target_ge scalar arguments level

/-- Arguments of a multiplication selected by one dyadic witness. -/
noncomputable def failingArguments
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge))
    (level : Fin levels) : Fin 2 → R :=
  Classical.choose
    (exists_unpreserved_multiplication measure problem levels input_le_one
      target_ge cover level)

theorem failingArguments_mem
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge))
    (level : Fin levels) :
    failingArguments measure problem levels input_le_one target_ge cover level ∈
      multiplicationArguments cover.atoms :=
  (Classical.choose_spec
    (exists_unpreserved_multiplication measure problem levels input_le_one
      target_ge cover level)).1

theorem failingArguments_spec
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge))
    (level : Fin levels) :
    ¬ (⟨.mul, failingArguments measure problem levels input_le_one target_ge
        cover level⟩ : Atom (Arithmetic.signature K) R).PreservedBy
      (model measure problem levels input_le_one target_ge) level :=
  (Classical.choose_spec
    (exists_unpreserved_multiplication measure problem levels input_le_one
      target_ge cover level)).2

/-- Index of the multiplication selected by one dyadic witness. -/
noncomputable def failingMultiplication
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge))
    (level : Fin levels) :
    Fin (multiplicationArguments cover.atoms).length :=
  Classical.choose (List.mem_iff_get.mp
    (failingArguments_mem measure problem levels input_le_one target_ge
      cover level))

theorem get_failingMultiplication
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge))
    (level : Fin levels) :
    (multiplicationArguments cover.atoms).get
        (failingMultiplication measure problem levels input_le_one target_ge
          cover level) =
      failingArguments measure problem levels input_le_one target_ge
        cover level :=
  Classical.choose_spec (List.mem_iff_get.mp
    (failingArguments_mem measure problem levels input_le_one target_ge
      cover level))

/-- The selected multiplication really fails its witness. -/
theorem failingMultiplication_spec
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge))
    (level : Fin levels) :
    ¬ (⟨.mul, (multiplicationArguments cover.atoms).get
        (failingMultiplication measure problem levels input_le_one target_ge
          cover level)⟩ : Atom (Arithmetic.signature K) R).PreservedBy
      (model measure problem levels input_le_one target_ge) level := by
  rw [get_failingMultiplication]
  exact failingArguments_spec measure problem levels input_le_one target_ge
    cover level

/-- Distinct thresholds select distinct multiplication atoms. -/
theorem failingMultiplication_injective
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge)) :
    Function.Injective
      (failingMultiplication measure problem levels input_le_one target_ge
        cover) := by
  intro first second equal
  apply mul_failure_unique measure problem levels input_le_one target_ge
    ((multiplicationArguments cover.atoms).get
      (failingMultiplication measure problem levels input_le_one target_ge
        cover first)) first second
  · exact failingMultiplication_spec measure problem levels input_le_one
      target_ge cover first
  · have argumentsEqual := congrArg
      (multiplicationArguments cover.atoms).get equal
    rw [argumentsEqual]
    exact failingMultiplication_spec measure problem levels input_le_one
      target_ge cover second

/-- Every fusion cover pays one multiplication for every dyadic threshold. -/
theorem cover_cost_lowerBound
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (cover : Cover (model measure problem levels input_le_one target_ge)) :
    levels ≤ cover.cost := by
  simpa using
    (failureRules measure problem levels input_le_one target_ge).cover_lowerBound
      (by simp) cover

/-- A dyadic measure lower bound transfers to every arithmetic circuit
constructing the target. -/
theorem circuit_multiplication_lowerBound
    (measure : Measure K R constant)
    (problem : Problem R)
    (levels : Nat)
    (input_le_one : ∀ input,
      measure.value (problem.inputs input) ≤ 1)
    (target_ge : 2 ^ levels ≤ measure.value problem.target)
    (circuit : Circuit (Arithmetic.signature K) problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Arithmetic.interpretation constant)) :
    levels ≤ circuit.cost (Arithmetic.multiplicationCost (K := K)) :=
  (model measure problem levels input_le_one target_ge).lowerBound
    (cover_cost_lowerBound measure problem levels input_le_one target_ge)
    circuit constructs

end Dyadic
end Fusion
end Algebraic
