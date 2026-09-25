/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Finset.Card

/-!
# Counting bounded fusion failures

A fusion cover excludes every witness, but a single atom need not exclude only
one witness.  This file packages the general counting argument in which an
atom of cost `c` can fail on at most `capacity * c` witnesses.  Taking the
union of all failure sets then gives a weighted cover lower bound.

This layer is useful when observations are indexed by derivative directions,
rank increments, monomials, cuts, or thresholds.  The semantic fusion model
and the combinatorial estimate on one atom remain independent.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

/-- The finite set of witnesses on which an atom fails to preserve soundness. -/
noncomputable def Atom.failures
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (atom : Atom σ U)
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness] : Finset model.Witness := by
  classical
  exact Finset.univ.filter fun witness => ¬ atom.PreservedBy model witness

@[simp] theorem Atom.mem_failures
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (atom : Atom σ U)
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness]
    (witness : model.Witness) :
    witness ∈ atom.failures model ↔ ¬ atom.PreservedBy model witness := by
  classical
  simp [Atom.failures]

/-- All witnesses excluded by at least one atom in a list. -/
noncomputable def Model.failureUnion
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness]
    (atoms : List (Atom σ U)) : Finset model.Witness := by
  classical
  exact atoms.foldr (fun atom failures => atom.failures model ∪ failures) ∅

@[simp] theorem Model.failureUnion_nil
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness] :
    model.failureUnion ([] : List (Atom σ U)) = ∅ := by
  simp [Model.failureUnion]

@[simp] theorem Model.failureUnion_cons
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness]
    [DecidableEq model.Witness]
    (atom : Atom σ U)
    (atoms : List (Atom σ U)) :
    model.failureUnion (atom :: atoms) =
      atom.failures model ∪ model.failureUnion atoms := by
  classical
  ext witness
  simp [Model.failureUnion]

/-- Membership in the failure union is the expected existential statement. -/
theorem Model.mem_failureUnion_iff
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness]
    (atoms : List (Atom σ U))
    (witness : model.Witness) :
    witness ∈ model.failureUnion atoms ↔
      ∃ atom ∈ atoms, ¬ atom.PreservedBy model witness := by
  classical
  induction atoms with
  | nil => simp
  | cons atom atoms inductionHypothesis =>
      simp [inductionHypothesis]

/-- The failure union has cardinality at most the sum of failure cardinalities. -/
theorem Model.failureUnion_card_le_sum
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness]
    (atoms : List (Atom σ U)) :
    (model.failureUnion atoms).card ≤
      (atoms.map fun atom => (atom.failures model).card).sum := by
  classical
  induction atoms with
  | nil => simp
  | cons atom atoms inductionHypothesis =>
      calc
        (model.failureUnion (atom :: atoms)).card =
            (atom.failures model ∪ model.failureUnion atoms).card := by
          rw [model.failureUnion_cons]
        _ ≤ (atom.failures model).card + (model.failureUnion atoms).card :=
          Finset.card_union_le _ _
        _ ≤ (atom.failures model).card +
            (atoms.map fun other => (other.failures model).card).sum :=
          Nat.add_le_add_left inductionHypothesis _
        _ = ((atom :: atoms).map fun other =>
            (other.failures model).card).sum := by simp

/-- Every cover has enough total failure capacity to account for all witnesses. -/
theorem Cover.witnessCard_le_sum_failures
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    [Fintype model.Witness]
    (cover : Cover model) :
    Fintype.card model.Witness ≤
      (cover.atoms.map fun atom => (atom.failures model).card).sum := by
  classical
  calc
    Fintype.card model.Witness = (Finset.univ : Finset model.Witness).card := by
      simp
    _ ≤ (model.failureUnion cover.atoms).card := by
      apply Finset.card_le_card
      intro witness _
      rw [model.mem_failureUnion_iff]
      by_contra noFailure
      apply cover.isCover witness
      intro atom present
      by_contra failure
      exact noFailure ⟨atom, present, failure⟩
    _ ≤ (cover.atoms.map fun atom => (atom.failures model).card).sum :=
      model.failureUnion_card_le_sum cover.atoms

/-- A failure estimate only for the atoms in one cover suffices for the
counting argument.  This circuit-local form is useful for restricted models
whose width, degree, homogeneity, or liveness promise need not hold for every
semantic atom of the ambient interpretation. -/
theorem Cover.witnessCard_le_mul_cost_of_local
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    [Fintype model.Witness]
    (cover : Cover model)
    (capacity : Nat)
    (localBound : ∀ atom ∈ cover.atoms,
      (atom.failures model).card ≤
        capacity * atom.cost operationCost) :
    Fintype.card model.Witness ≤ capacity * cover.cost := by
  have failureSumLe : ∀ atoms : List (Atom σ U),
      (∀ atom ∈ atoms,
        (atom.failures model).card ≤
          capacity * atom.cost operationCost) →
      (atoms.map fun atom => (atom.failures model).card).sum ≤
        (atoms.map fun atom =>
          capacity * atom.cost operationCost).sum := by
    intro atoms
    induction atoms with
    | nil => simp
    | cons atom atoms inductionHypothesis =>
        intro atomsLocal
        simp only [List.map_cons, List.sum_cons]
        apply Nat.add_le_add
        · exact atomsLocal atom (by simp)
        · apply inductionHypothesis
          intro other present
          exact atomsLocal other (by simp [present])
  have capacitySum (atoms : List (Atom σ U)) :
      (atoms.map fun atom =>
        capacity * atom.cost operationCost).sum =
          capacity * Atom.listCost atoms operationCost := by
    induction atoms with
    | nil => simp
    | cons atom atoms inductionHypothesis =>
        simp only [List.map_cons, List.sum_cons, Atom.listCost]
        rw [Nat.mul_add, inductionHypothesis]
        simp [Atom.listCost]
  calc
    Fintype.card model.Witness ≤
        (cover.atoms.map fun atom => (atom.failures model).card).sum :=
      cover.witnessCard_le_sum_failures
    _ ≤ (cover.atoms.map fun atom =>
        capacity * atom.cost operationCost).sum :=
      failureSumLe cover.atoms localBound
    _ = capacity * cover.cost := capacitySum cover.atoms

/-- Divide a circuit-local failure estimate by a positive capacity. -/
theorem Cover.ceilDiv_witnessCard_le_cost_of_local
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    [Fintype model.Witness]
    (cover : Cover model)
    (capacity : Nat)
    (positive : 0 < capacity)
    (localBound : ∀ atom ∈ cover.atoms,
      (atom.failures model).card ≤
        capacity * atom.cost operationCost) :
    Fintype.card model.Witness ⌈/⌉ capacity ≤ cover.cost :=
  (ceilDiv_le_iff_le_mul positive).2
    (cover.witnessCard_le_mul_cost_of_local capacity localBound)

/-- A bounded-failure estimate on the semantic atoms extracted from one
constructing circuit transfers directly to its operation cost. -/
theorem Model.ceilDiv_witnessCard_le_circuitCost_of_local
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness]
    (capacity : Nat)
    (positive : 0 < capacity)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit interpretation)
    (localBound : ∀ atom ∈
      circuitAtoms circuit interpretation problem.inputs,
      (atom.failures model).card ≤
        capacity * atom.cost operationCost) :
    Fintype.card model.Witness ⌈/⌉ capacity ≤
      circuit.cost operationCost := by
  let cover := coverOfCircuit model circuit constructs
  calc
    Fintype.card model.Witness ⌈/⌉ capacity ≤ cover.cost :=
      cover.ceilDiv_witnessCard_le_cost_of_local capacity positive localBound
    _ = circuit.cost operationCost :=
      coverOfCircuit_cost model circuit constructs

/--
A reusable certificate that each atom destroys only boundedly many witnesses
per unit of operation cost.
-/
structure FailureBound
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    [Fintype model.Witness] where
  /-- Maximum number of failed witnesses per unit of gate cost. -/
  capacity : Nat
  /-- The local failure estimate for every possible semantic gate atom. -/
  failure_card_le : ∀ atom : Atom σ U,
    (atom.failures model).card ≤ capacity * atom.cost operationCost

/-- A bounded-failure certificate gives a weighted lower bound for every cover. -/
theorem FailureBound.witnessCard_le_mul_coverCost
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    [Fintype model.Witness]
    (bound : FailureBound model)
    (cover : Cover model) :
    Fintype.card model.Witness ≤ bound.capacity * cover.cost := by
  have failureSumLe (atoms : List (Atom σ U)) :
      (atoms.map fun atom => (atom.failures model).card).sum ≤
        (atoms.map fun atom =>
          bound.capacity * atom.cost operationCost).sum := by
    induction atoms with
    | nil => rfl
    | cons atom atoms inductionHypothesis =>
        exact Nat.add_le_add (bound.failure_card_le atom) inductionHypothesis
  have capacitySum (atoms : List (Atom σ U)) :
      (atoms.map fun atom =>
        bound.capacity * atom.cost operationCost).sum =
          bound.capacity * Atom.listCost atoms operationCost := by
    induction atoms with
    | nil => simp
    | cons atom atoms inductionHypothesis =>
        simp only [List.map_cons, List.sum_cons, Atom.listCost]
        rw [Nat.mul_add, inductionHypothesis]
        simp [Atom.listCost]
  calc
    Fintype.card model.Witness ≤
        (cover.atoms.map fun atom => (atom.failures model).card).sum :=
      cover.witnessCard_le_sum_failures
    _ ≤ (cover.atoms.map fun atom =>
        bound.capacity * atom.cost operationCost).sum :=
      failureSumLe cover.atoms
    _ = bound.capacity * cover.cost :=
      capacitySum cover.atoms

/-- Dividing the witness count by a positive capacity lower-bounds cover cost. -/
theorem FailureBound.ceilDiv_witnessCard_le_coverCost
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    [Fintype model.Witness]
    (bound : FailureBound model)
    (positive : 0 < bound.capacity)
    (cover : Cover model) :
    Fintype.card model.Witness ⌈/⌉ bound.capacity ≤ cover.cost :=
  (ceilDiv_le_iff_le_mul positive).2
    (bound.witnessCard_le_mul_coverCost cover)

/-- A positive bounded-failure certificate packages into the core framework. -/
noncomputable def FailureBound.framework
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    [Fintype model.Witness]
    (bound : FailureBound model)
    (positive : 0 < bound.capacity) : Framework model where
  bound := Fintype.card model.Witness ⌈/⌉ bound.capacity
  coverLowerBound := bound.ceilDiv_witnessCard_le_coverCost positive

/-- The counting bound transferred directly to constructing circuits. -/
theorem FailureBound.ceilDiv_witnessCard_le_circuitCost
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    [Fintype model.Witness]
    (bound : FailureBound model)
    (positive : 0 < bound.capacity)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit interpretation) :
    Fintype.card model.Witness ⌈/⌉ bound.capacity ≤
      circuit.cost operationCost :=
  (bound.framework positive).lowerBound circuit constructs

end Fusion
end Algebraic
