/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Data.ENat.Lattice

/-!
# Algebra-generic fusion lower bounds

Fusion arguments turn the gates of a concrete computation into a static cover
of a family of observations.  This file contains the part of that argument
which is independent of Boolean sets, semi-filters, or any particular circuit
basis.

An observation compares two predicates on every semantic value: a reference
predicate and an observed predicate.  Inputs satisfy the implication from the
reference predicate to the observed predicate, while the target violates it.
Consequently, every circuit constructing the target contains a gate at which
that implication is not preserved.  The resulting local gate configurations
cover all observations, and their total weight is exactly the circuit cost.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

/-- A fixed algebraic construction problem: construct `target` from `inputs`. -/
structure Problem (U : Type u) where
  /-- Number of available generators. -/
  inputCount : Nat
  /-- The generators available as circuit inputs. -/
  inputs : Fin inputCount → U
  /-- The value to be constructed. -/
  target : U

/-- One operation together with the semantic values supplied to its arguments. -/
structure Atom (σ : Signature) (U : Type u) where
  /-- Operation performed at the gate. -/
  op : σ.Op
  /-- Semantic value supplied to each argument. -/
  arguments : Fin (σ.Arity op) → U

/-- The semantic result of a fusion atom. -/
def Atom.result
    (atom : Atom σ U)
    (interpretation : Interpretation σ U) : U :=
  interpretation atom.op atom.arguments

/-- The weight of one fusion atom. -/
def Atom.cost
    (atom : Atom σ U)
    (operationCost : OperationCost σ) : Nat :=
  operationCost atom.op

/-- Total weight of a list of fusion atoms. -/
def Atom.listCost
    (atoms : List (Atom σ U))
    (operationCost : OperationCost σ) : Nat :=
  (atoms.map fun atom => atom.cost operationCost).sum

@[simp] theorem Atom.listCost_nil
    (operationCost : OperationCost σ) :
    Atom.listCost ([] : List (Atom σ U)) operationCost = 0 := rfl

@[simp] theorem Atom.listCost_append
    (left right : List (Atom σ U))
    (operationCost : OperationCost σ) :
    Atom.listCost (left ++ right) operationCost =
      Atom.listCost left operationCost + Atom.listCost right operationCost := by
  simp [Atom.listCost]

@[simp] theorem Atom.listCost_singleton
    (atom : Atom σ U)
    (operationCost : OperationCost σ) :
    Atom.listCost [atom] operationCost = atom.cost operationCost := by
  simp [Atom.listCost]

/--
An observation model for one construction problem.  A witness supplies a
reference predicate and an observed predicate on semantic values.  Every input
is sound for every witness, whereas the target is reference-true and
observed-false.

The model deliberately imposes no Boolean or order structure on `U`.  For
set-theoretic fusion, witnesses will be points equipped with semi-filters.  For
arithmetic circuits they can instead be linear, rank, derivative, or other
algebraic observations.
-/
structure Model
    (operationCost : OperationCost σ)
    (interpretation : Interpretation σ U)
    (problem : Problem U) where
  /-- Observations which every proposed cover must exclude. -/
  Witness : Type w
  /-- The reference view of a semantic value. -/
  reference : Witness → U → Prop
  /-- The fused or approximating view of a semantic value. -/
  observed : Witness → U → Prop
  /-- Every generator is sound under every observation. -/
  input_sound : ∀ witness input,
    reference witness (problem.inputs input) →
      observed witness (problem.inputs input)
  /-- The target is true in every reference view. -/
  target_reference : ∀ witness, reference witness problem.target
  /-- The target is false in every observed view. -/
  target_not_observed : ∀ witness, ¬ observed witness problem.target

/-- The reference-to-observed implication at one semantic value. -/
def Model.Sound
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (witness : model.Witness)
    (value : U) : Prop :=
  model.reference witness value → model.observed witness value

/-- A witness preserves an atom when sound arguments imply a sound result. -/
def Atom.PreservedBy
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (atom : Atom σ U)
    (model : Model operationCost interpretation problem)
    (witness : model.Witness) : Prop :=
  (∀ argument, model.Sound witness (atom.arguments argument)) →
    model.Sound witness (atom.result interpretation)

/-- A list of atoms covers a model when no witness preserves every atom. -/
def Model.IsCover
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (atoms : List (Atom σ U)) : Prop :=
  ∀ witness, ¬ ∀ atom ∈ atoms, atom.PreservedBy model witness

/-- A proof-carrying finite fusion cover. -/
structure Cover
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem) where
  /-- Local gate configurations in the cover. -/
  atoms : List (Atom σ U)
  /-- Every observation is violated by some atom in the list. -/
  isCover : model.IsCover atoms

/-- Total operation weight of a fusion cover. -/
def Cover.cost
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    (cover : Cover model) : Nat :=
  Atom.listCost cover.atoms operationCost

/-- Minimum weighted cover cost, or `⊤` if no finite cover exists. -/
noncomputable def Model.coverComplexity
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem) : ℕ∞ :=
  ⨅ cover : Cover model, (cover.cost : ℕ∞)

/-- Every concrete cover upper-bounds minimum cover complexity. -/
theorem Model.coverComplexity_le
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (cover : Cover model) :
    model.coverComplexity ≤ cover.cost := by
  unfold Model.coverComplexity
  exact iInf_le _ cover

/-- A line evaluated after a prefix program, viewed as a fusion atom. -/
def lineAtom
    (line : Line σ n g)
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) : Atom σ U where
  op := line.op
  arguments := program.trace interpretation input ∘ line.wires

@[simp] theorem lineAtom_op
    (line : Line σ n g)
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (lineAtom line program interpretation input).op = line.op := rfl

/-- The result of a line's fusion atom is exactly the line evaluation. -/
theorem lineAtom_result
    (line : Line σ n g)
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (lineAtom line program interpretation input).result interpretation =
      line.eval interpretation input (program.eval interpretation input) := rfl

/-- Semantic gate configurations of a program, in topological order. -/
def programAtoms
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (program : Program σ n g) → List (Atom σ U)
  | .empty => []
  | .gate program line =>
      programAtoms interpretation input program ++
        [lineAtom line program interpretation input]

@[simp] theorem programAtoms_empty
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    programAtoms interpretation input (Program.empty : Program σ n 0) = [] := rfl

@[simp] theorem programAtoms_gate
    (program : Program σ n g)
    (line : Line σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    programAtoms interpretation input (program.gate line) =
      programAtoms interpretation input program ++
        [lineAtom line program interpretation input] := rfl

/-- Extracted atoms have exactly the weighted cost of the source program. -/
theorem programAtoms_cost
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (operationCost : OperationCost σ) :
    Atom.listCost (programAtoms interpretation input program) operationCost =
      program.cost operationCost := by
  induction program with
  | empty => rfl
  | gate program line inductionHypothesis =>
      rw [programAtoms_gate, Atom.listCost_append,
        Atom.listCost_singleton, inductionHypothesis]
      rfl

/--
If a witness preserves every extracted atom, then every wire in the program is
sound for that witness.
-/
theorem sound_trace_of_preserves
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (program : Program σ problem.inputCount g)
    (witness : model.Witness)
    (preserves : ∀ atom ∈
      programAtoms interpretation problem.inputs program,
        atom.PreservedBy model witness) :
    ∀ wire, model.Sound witness
      (program.trace interpretation problem.inputs wire) := by
  induction program with
  | empty =>
      intro wire
      cases wire with
      | input input => exact model.input_sound witness input
      | gate gate => exact Fin.elim0 gate
  | @gate g program line inductionHypothesis =>
      have preservesPrior : ∀ atom ∈
          programAtoms interpretation problem.inputs program,
          atom.PreservedBy model witness := by
        intro atom present
        exact preserves atom (List.mem_append_left _ present)
      have priorSound := inductionHypothesis preservesPrior
      intro wire
      induction wire using Wire.lastCases with
      | last =>
          let lastAtom := lineAtom line program interpretation problem.inputs
          have lastPresent : lastAtom ∈
              programAtoms interpretation problem.inputs (program.gate line) := by
            simp [lastAtom]
          have lastPreserved := preserves lastAtom lastPresent
          have argumentsSound : ∀ argument,
              model.Sound witness (lastAtom.arguments argument) := by
            intro argument
            exact priorSound (line.wires argument)
          have resultSound := lastPreserved argumentsSound
          rw [Program.trace_gateWire, Program.gateFunction_gate_last]
          exact resultSound
      | castSucc priorWire =>
          rw [Program.trace_gate_castSucc]
          exact priorSound priorWire

/-- A circuit constructs a problem when its sole output is the target value. -/
def Problem.Constructs
    (problem : Problem U)
    (circuit : Circuit σ problem.inputCount 1)
    (interpretation : Interpretation σ U) : Prop :=
  circuit.eval interpretation problem.inputs 0 = problem.target

/-- Semantic gate configurations extracted from a circuit. -/
def circuitAtoms
    (circuit : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) : List (Atom σ U) :=
  programAtoms interpretation input circuit.program

/-- Extracted circuit atoms have exactly the circuit's weighted cost. -/
theorem circuitAtoms_cost
    (circuit : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (operationCost : OperationCost σ) :
    Atom.listCost (circuitAtoms circuit interpretation input) operationCost =
      circuit.cost operationCost := by
  exact programAtoms_cost circuit.program interpretation input operationCost

/-- Every circuit constructing the target supplies a fusion cover. -/
def coverOfCircuit
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit interpretation) : Cover model where
  atoms := circuitAtoms circuit interpretation problem.inputs
  isCover := by
    intro witness preserves
    have outputSound := sound_trace_of_preserves model circuit.program witness preserves
      (circuit.outputs 0)
    have targetSound : model.Sound witness problem.target := by
      rw [← constructs]
      exact outputSound
    exact model.target_not_observed witness
      (targetSound (model.target_reference witness))

/-- The cover extracted from a circuit has exactly the circuit's cost. -/
theorem coverOfCircuit_cost
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit interpretation) :
    (coverOfCircuit model circuit constructs).cost =
      circuit.cost operationCost := by
  exact circuitAtoms_cost circuit interpretation problem.inputs operationCost

/-- A lower bound for every fusion cover is a circuit-cost lower bound. -/
theorem Model.lowerBound
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (coverLowerBound : ∀ cover : Cover model, L ≤ cover.cost)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit interpretation) :
    L ≤ circuit.cost operationCost := by
  let cover := coverOfCircuit model circuit constructs
  rw [← coverOfCircuit_cost model circuit constructs]
  exact coverLowerBound cover

/-- Cover complexity lower-bounds every circuit constructing the target. -/
theorem Model.coverComplexity_le_cost
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit interpretation) :
    model.coverComplexity ≤ circuit.cost operationCost := by
  calc
    model.coverComplexity ≤
        (coverOfCircuit model circuit constructs).cost :=
      model.coverComplexity_le (coverOfCircuit model circuit constructs)
    _ = circuit.cost operationCost :=
      by exact_mod_cast coverOfCircuit_cost model circuit constructs

/-- A packaged combinatorial lower bound for one fusion model. -/
structure Framework
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    (model : Model operationCost interpretation problem) where
  /-- Claimed weighted lower bound. -/
  bound : Nat
  /-- Every finite fusion cover pays the claimed bound. -/
  coverLowerBound : ∀ cover : Cover model, bound ≤ cover.cost

/-- A fusion framework proves its bound for every constructing circuit. -/
theorem Framework.lowerBound
    {σ : Signature}
    {U : Type u}
    {operationCost : OperationCost σ}
    {interpretation : Interpretation σ U}
    {problem : Problem U}
    {model : Model operationCost interpretation problem}
    (framework : Framework model)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit interpretation) :
    framework.bound ≤ circuit.cost operationCost :=
  model.lowerBound framework.coverLowerBound circuit constructs

end Fusion
end Algebraic
