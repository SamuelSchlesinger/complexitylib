/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework
public import Complexitylib.Algebraic.Basis.Arithmetic
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Atoms
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Interaction-span Fusion for arithmetic circuits

Many cancellation-tolerant arithmetic lower bounds use a linear feature with
the following product rule: the feature of a product is a linear combination
of the two old feature values plus one new interaction term.  Hessian matrices
are the motivating example; their new term is the symmetrized outer product
of the two gradients.

This module isolates the circuit-combinatorial part.  It proves that the
target feature lies in the span of one interaction term for each
multiplication gate.  Concrete feature maps and rank estimates are supplied
in separate modules.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction

variable {K : Type u} {C : Type v} {U : Type w} {Q : Type x}
variable [Semiring K] [Add U] [Mul U]
variable [AddCommMonoid Q] [Module K Q]

/-- Algebraic data whose product rule creates one new interaction term. -/
structure Certificate
    (constant : C → U)
    (problem : Problem U) where
  /-- Linearized feature used to obstruct the target. -/
  feature : U → Q
  /-- New feature contribution created by multiplying two values. -/
  interaction : U → U → Q
  /-- Free inputs have zero feature. -/
  input_zero : ∀ input, feature (problem.inputs input) = 0
  /-- Addition is linear at feature level. -/
  feature_add : ∀ left right,
    feature (left + right) = feature left + feature right
  /-- Named scalar constants have zero feature. -/
  constant_zero : ∀ scalar, feature (constant scalar) = 0
  /-- A product propagates its input features linearly and creates exactly one
  additional interaction. -/
  feature_mul : ∀ left right, ∃ leftScalar rightScalar : K,
    feature (left * right) =
      leftScalar • feature left + rightScalar • feature right +
        interaction left right

/-- A submodule obstruction for an interaction certificate. -/
structure SpanWitness
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem) where
  /-- Candidate span of the interactions already made available. -/
  submodule : Submodule K Q
  /-- The target feature is not yet in the candidate span. -/
  target_not_mem : certificate.feature problem.target ∉ submodule

/-- Fusion model induced by an interaction certificate. -/
def model
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem) :
    Model (Algebraic.Arithmetic.multiplicationCost (K := C))
      (Algebraic.Arithmetic.interpretation constant) problem where
  Witness := SpanWitness (Q := Q) certificate
  reference _ _ := True
  observed witness value := certificate.feature value ∈ witness.submodule
  input_sound := by
    intro witness input _
    rw [certificate.input_zero input]
    exact witness.submodule.zero_mem
  target_reference := by
    intro _
    trivial
  target_not_observed := by
    intro witness
    exact witness.target_not_mem

/-- Addition preserves every interaction-span witness. -/
theorem add_preserved
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (arguments : Fin 2 → U)
    (witness : (model certificate).Witness) :
    (⟨.add, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature C) U).PreservedBy
        (model certificate) witness := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result, model,
    Algebraic.Arithmetic.interpretation, true_implies]
  intro argumentsMem
  rw [certificate.feature_add]
  exact witness.submodule.add_mem
    (argumentsMem (0 : Fin 2)) (argumentsMem (1 : Fin 2))

/-- Named constants preserve every interaction-span witness. -/
theorem constant_preserved
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (scalar : C)
    (arguments : Fin (Algebraic.Arithmetic.arity (.constant scalar)) → U)
    (witness : (model certificate).Witness) :
    (⟨.constant scalar, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature C) U).PreservedBy
        (model certificate) witness := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result, model,
    Algebraic.Arithmetic.interpretation, true_implies]
  intro _
  rw [certificate.constant_zero scalar]
  exact witness.submodule.zero_mem

/-- A multiplication preserves a witness whenever its new interaction is
already in the witness submodule. -/
theorem mul_preserved_of_interaction_mem
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (arguments : Fin 2 → U)
    (witness : (model certificate).Witness)
    (interactionMem : certificate.interaction
      (arguments (0 : Fin 2)) (arguments (1 : Fin 2)) ∈
        witness.submodule) :
    (⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature C) U).PreservedBy
        (model certificate) witness := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result, model,
    Algebraic.Arithmetic.interpretation, true_implies]
  intro argumentsMem
  change certificate.feature
    (arguments (0 : Fin 2) * arguments (1 : Fin 2)) ∈ witness.submodule
  obtain ⟨leftScalar, rightScalar, decomposition⟩ :=
    certificate.feature_mul
      (arguments (0 : Fin 2)) (arguments (1 : Fin 2))
  rw [decomposition]
  exact witness.submodule.add_mem
    (witness.submodule.add_mem
      (witness.submodule.smul_mem leftScalar
        (argumentsMem (0 : Fin 2)))
      (witness.submodule.smul_mem rightScalar
        (argumentsMem (1 : Fin 2))))
    interactionMem

/-- Retain the new interaction created by a multiplication atom and discard
addition and constant atoms. -/
def Atom.interaction?
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atom : Atom (Algebraic.Arithmetic.signature C) U) : Option Q :=
  match atom with
  | ⟨.add, _⟩ => none
  | ⟨.mul, arguments⟩ =>
      some (certificate.interaction
        (arguments (0 : Fin 2)) (arguments (1 : Fin 2)))
  | ⟨.constant _, _⟩ => none

/-- Interaction terms extracted from a list of arithmetic atoms. -/
def interactions
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) : List Q :=
  atoms.filterMap (Atom.interaction? certificate)

@[simp] theorem interactions_cons_add
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (arguments : Fin 2 → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    interactions certificate (⟨.add, arguments⟩ :: atoms) =
      interactions certificate atoms := rfl

@[simp] theorem interactions_cons_mul
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (arguments : Fin 2 → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    interactions certificate (⟨.mul, arguments⟩ :: atoms) =
      certificate.interaction
        (arguments (0 : Fin 2)) (arguments (1 : Fin 2)) ::
          interactions certificate atoms := rfl

@[simp] theorem interactions_cons_constant
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (scalar : C)
    (arguments : Fin (Algebraic.Arithmetic.arity (.constant scalar)) → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    interactions certificate (⟨.constant scalar, arguments⟩ :: atoms) =
      interactions certificate atoms := rfl

/-- Extracting interactions is the same ordered projection as first
extracting multiplication occurrences and then mapping the certificate's
interaction function.  In particular, this preserves repeated semantic
multiplications as distinct occurrences. -/
theorem interactions_eq_map_multiplicationArguments
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    interactions certificate atoms =
      (multiplicationArguments atoms).map fun arguments =>
        certificate.interaction
          (arguments (0 : Fin 2)) (arguments (1 : Fin 2)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      cases atom with
      | mk op arguments =>
          cases op with
          | add =>
              change Fin 2 → U at arguments
              simpa using inductionHypothesis
          | mul =>
              change Fin 2 → U at arguments
              simp [inductionHypothesis]
          | constant scalar =>
              simpa using inductionHypothesis

/-- The number of extracted interactions is exactly multiplication cost. -/
theorem interactions_length
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    (interactions certificate atoms).length =
      Atom.listCost atoms
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      cases atom with
      | mk op arguments =>
          cases op with
          | add =>
              change Fin 2 → U at arguments
              rw [interactions_cons_add]
              simpa [Atom.listCost, Atom.cost] using inductionHypothesis
          | mul =>
              change Fin 2 → U at arguments
              rw [interactions_cons_mul]
              simp [Atom.listCost, Atom.cost, inductionHypothesis,
                Nat.add_comm]
          | constant scalar =>
              rw [interactions_cons_constant]
              simpa [Atom.listCost, Atom.cost] using inductionHypothesis

/-- Submodule generated by all multiplication interactions in an atom list. -/
noncomputable def generatedSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    Submodule K Q :=
  Submodule.span K
    (Set.range fun index : Fin (interactions certificate atoms).length =>
      (interactions certificate atoms).get index)

/-- The interaction of a multiplication atom in the list belongs to the
generated interaction submodule. -/
theorem interaction_mem_generatedSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U))
    (arguments : Fin 2 → U)
    (present : (⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature C) U) ∈ atoms) :
    certificate.interaction
        (arguments (0 : Fin 2)) (arguments (1 : Fin 2)) ∈
      generatedSubmodule certificate atoms := by
  have interactionPresent : certificate.interaction
        (arguments (0 : Fin 2)) (arguments (1 : Fin 2)) ∈
      interactions certificate atoms := by
    change _ ∈ atoms.filterMap (Atom.interaction? certificate)
    rw [List.mem_filterMap]
    exact ⟨⟨.mul, arguments⟩, present, rfl⟩
  obtain ⟨index, indexSpec⟩ := List.mem_iff_get.mp interactionPresent
  apply Submodule.subset_span
  exact ⟨index, indexSpec⟩

/-- Every interaction-span Fusion cover spans the target feature. -/
theorem targetFeature_mem_generatedSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (cover : Cover (model certificate)) :
    certificate.feature problem.target ∈
      generatedSubmodule certificate cover.atoms := by
  classical
  by_contra targetNotMem
  let witness : SpanWitness certificate := {
    submodule := generatedSubmodule certificate cover.atoms
    target_not_mem := targetNotMem
  }
  apply cover.isCover witness
  intro atom present
  cases atom with
  | mk op arguments =>
      cases op with
      | add =>
          change Fin 2 → U at arguments
          exact add_preserved certificate arguments witness
      | mul =>
          change Fin 2 → U at arguments
          apply mul_preserved_of_interaction_mem certificate arguments witness
          exact interaction_mem_generatedSubmodule certificate cover.atoms
            arguments present
      | constant scalar =>
          exact constant_preserved certificate scalar arguments witness

/-- A constructing arithmetic circuit spans its target feature using exactly
one extracted interaction per multiplication gate. -/
theorem targetFeature_mem_circuitSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant)) :
    certificate.feature problem.target ∈
      generatedSubmodule certificate
        (circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation constant) problem.inputs) := by
  exact targetFeature_mem_generatedSubmodule certificate
    (coverOfCircuit (model certificate) circuit constructs)

/-- Every wire feature belongs to the interaction span of any atom list that
contains all atoms of the program.  Unlike the cover argument, this invariant
does not single out one output and is therefore the bridge to multi-output
lower bounds. -/
theorem feature_trace_mem_of_programAtoms_subset
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (program : Program (Algebraic.Arithmetic.signature C)
      problem.inputCount g)
    (allAtoms : List (Atom (Algebraic.Arithmetic.signature C) U))
    (atomsSubset : ∀ atom,
      atom ∈ programAtoms
        (Algebraic.Arithmetic.interpretation constant)
        problem.inputs program → atom ∈ allAtoms) :
    ∀ wire, certificate.feature
        (program.trace (Algebraic.Arithmetic.interpretation constant)
          problem.inputs wire) ∈
      generatedSubmodule certificate allAtoms := by
  induction program with
  | empty =>
      intro wire
      refine Fin.addCases (fun input => ?_)
        (fun impossible => Fin.elim0 impossible) wire
      rw [Program.trace_input, certificate.input_zero input]
      exact (generatedSubmodule certificate allAtoms).zero_mem
  | @gate g program line inductionHypothesis =>
      have priorSubset : ∀ atom,
          atom ∈ programAtoms
            (Algebraic.Arithmetic.interpretation constant)
            problem.inputs program → atom ∈ allAtoms := by
        intro atom present
        exact atomsSubset atom (List.mem_append_left _ present)
      have priorMem := inductionHypothesis priorSubset
      intro wire
      refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
      · rw [Program.trace_input, certificate.input_zero input]
        exact (generatedSubmodule certificate allAtoms).zero_mem
      · refine Fin.lastCases ?_ (fun priorGate => ?_) gate
        · let lastAtom := lineAtom line program
            (Algebraic.Arithmetic.interpretation constant) problem.inputs
          have lastPresent : lastAtom ∈ allAtoms := by
            apply atomsSubset lastAtom
            simp [lastAtom]
          rw [Program.trace_gateWire, Program.gateFunction_gate_last]
          cases line with
          | mk op wires =>
              cases op with
              | add =>
                  change Fin 2 → Wire problem.inputCount g at wires
                  change certificate.feature
                    (program.trace
                        (Algebraic.Arithmetic.interpretation constant)
                        problem.inputs (wires (0 : Fin 2)) +
                      program.trace
                        (Algebraic.Arithmetic.interpretation constant)
                        problem.inputs (wires (1 : Fin 2))) ∈
                    generatedSubmodule certificate allAtoms
                  rw [certificate.feature_add]
                  exact (generatedSubmodule certificate allAtoms).add_mem
                    (priorMem (wires (0 : Fin 2)))
                    (priorMem (wires (1 : Fin 2)))
              | mul =>
                  change Fin 2 → Wire problem.inputCount g at wires
                  change certificate.feature
                    (program.trace
                        (Algebraic.Arithmetic.interpretation constant)
                        problem.inputs (wires (0 : Fin 2)) *
                      program.trace
                        (Algebraic.Arithmetic.interpretation constant)
                        problem.inputs (wires (1 : Fin 2))) ∈
                    generatedSubmodule certificate allAtoms
                  obtain ⟨leftScalar, rightScalar, decomposition⟩ :=
                    certificate.feature_mul
                      (program.trace
                        (Algebraic.Arithmetic.interpretation constant)
                        problem.inputs (wires (0 : Fin 2)))
                      (program.trace
                        (Algebraic.Arithmetic.interpretation constant)
                        problem.inputs (wires (1 : Fin 2)))
                  rw [decomposition]
                  apply (generatedSubmodule certificate allAtoms).add_mem
                  · exact (generatedSubmodule certificate allAtoms).add_mem
                      ((generatedSubmodule certificate allAtoms).smul_mem
                        leftScalar (priorMem (wires (0 : Fin 2))))
                      ((generatedSubmodule certificate allAtoms).smul_mem
                        rightScalar (priorMem (wires (1 : Fin 2))))
                  · exact interaction_mem_generatedSubmodule certificate
                      allAtoms
                      (fun argument : Fin 2 =>
                        program.trace
                          (Algebraic.Arithmetic.interpretation constant)
                          problem.inputs (wires argument)) (by
                        simpa [lastAtom, lineAtom, Function.comp_def] using
                          lastPresent)
              | constant scalar =>
                  change certificate.feature (constant scalar) ∈
                    generatedSubmodule certificate allAtoms
                  rw [certificate.constant_zero scalar]
                  exact (generatedSubmodule certificate allAtoms).zero_mem
        · simpa [Program.trace] using priorMem (Wire.gate priorGate)

/-- Every output feature of a circuit lies in the common span of all its
multiplication interactions. -/
theorem feature_circuit_output_mem
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m)
    (output : Fin m) :
    certificate.feature
        (circuit.eval (Algebraic.Arithmetic.interpretation constant)
          problem.inputs output) ∈
      generatedSubmodule certificate
        (circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation constant) problem.inputs) := by
  exact feature_trace_mem_of_programAtoms_subset certificate circuit.program
    (circuitAtoms circuit
      (Algebraic.Arithmetic.interpretation constant) problem.inputs)
    (fun _ present => present) (circuit.outputs output)

end Interaction
end Arithmetic
end Fusion
end Algebraic
