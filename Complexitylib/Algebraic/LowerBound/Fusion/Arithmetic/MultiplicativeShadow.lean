/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Multiple
public import Complexitylib.Algebraic.LowerBound.Fusion.Comap
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Multiplicative-shadow lower bounds for arithmetic circuits

An additive interaction certificate linearizes addition and charges the new
directions created by multiplication.  This module records the operation-dual
principle.  Suppose a feature of a product always belongs to the span of the
two operand features.  Free inputs and named constants start with zero
feature.  A multiplication gate then creates no new feature direction, while
one addition gate can create at most the direction of its result.

Consequently, the common span of the requested output features has dimension
at most the number of addition gates.  The argument permits arbitrary
constants, cancellation, zero intermediate values, and sharing between all
outputs.  It deliberately asks for no rule governing the feature of a sum.

The motivating specialization sends a nonzero rational function to its
factor-exponent, divisor, or valuation vector modulo the free inputs and
constants.  Multiplication is addition in that vector space, whereas an
addition can introduce at most one new divisor direction.

This is a machine-checked feature-span presentation of the classical
addition-rank viewpoint, not a claim that addition rank is new.  See:

* D. G. Kirkpatrick and Z. M. Kedem, *Addition Requirements for Rational
  Functions* (1977), https://doi.org/10.1137/0206015.
* C. P. Schnorr and J. P. Van de Wiele, *On the Additive Complexity of
  Polynomials* (1980), https://doi.org/10.1016/0304-3975(80)90068-7.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace MultiplicativeShadow

variable {K : Type u} {C : Type v} {U : Type w} {Q : Type x}

section Semiring

variable [Semiring K] [Add U] [Mul U]
variable [AddCommMonoid Q] [Module K Q]

/-- A feature for which multiplication creates no direction outside the span
of the operand features. -/
structure Certificate
    (constant : C → U)
    (problem : Problem U) where
  /-- Feature used to obstruct the requested outputs. -/
  feature : U → Q
  /-- Free inputs have zero feature. -/
  input_zero : ∀ input, feature (problem.inputs input) = 0
  /-- Named constants have zero feature. -/
  constant_zero : ∀ scalar, feature (constant scalar) = 0
  /-- A product feature belongs to the span of its two operand features. -/
  feature_mul : ∀ left right, ∃ leftScalar rightScalar : K,
    feature (left * right) =
      leftScalar • feature left + rightScalar • feature right

/-- Pull a multiplicative-shadow certificate back along a
multiplication-preserving semantic map.  The map need not preserve addition:
addition results are retained as fresh shadow generators anyway. -/
def Certificate.comap
    {U₁ : Type y} {U₂ : Type z}
    [Mul U₁] [Mul U₂]
    (sourceConstant : C → U₁)
    (targetConstant : C → U₂)
    (problem : Problem U₁)
    (map : U₁ → U₂)
    (map_mul : ∀ left right, map (left * right) = map left * map right)
    (map_constant : ∀ scalar,
      map (sourceConstant scalar) = targetConstant scalar)
    (certificate : Certificate (K := K) (Q := Q) targetConstant
      (problem.map map)) :
    Certificate (K := K) (Q := Q) sourceConstant problem where
  feature := certificate.feature ∘ map
  input_zero := certificate.input_zero
  constant_zero := by
    intro scalar
    change certificate.feature (map (sourceConstant scalar)) = 0
    rw [map_constant scalar]
    exact certificate.constant_zero scalar
  feature_mul := by
    intro left right
    obtain ⟨leftScalar, rightScalar, decomposition⟩ :=
      certificate.feature_mul (map left) (map right)
    exact ⟨leftScalar, rightScalar, by
      change certificate.feature (map (left * right)) = _
      rw [map_mul]
      exact decomposition⟩

@[simp] theorem Certificate.comap_feature
    {U₁ : Type y} {U₂ : Type z}
    [Mul U₁] [Mul U₂]
    (sourceConstant : C → U₁)
    (targetConstant : C → U₂)
    (problem : Problem U₁)
    (map : U₁ → U₂)
    (map_mul : ∀ left right, map (left * right) = map left * map right)
    (map_constant : ∀ scalar,
      map (sourceConstant scalar) = targetConstant scalar)
    (certificate : Certificate (K := K) (Q := Q) targetConstant
      (problem.map map))
    (value : U₁) :
    (certificate.comap sourceConstant targetConstant problem map map_mul
      map_constant).feature value = certificate.feature (map value) :=
  rfl

/-- Retain the feature of an addition result and discard multiplication and
constant atoms. -/
def Atom.additionShadow?
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atom : Atom (Algebraic.Arithmetic.signature C) U) : Option Q :=
  match atom with
  | ⟨.add, arguments⟩ =>
      some (certificate.feature
        (arguments (0 : Fin 2) + arguments (1 : Fin 2)))
  | ⟨.mul, _⟩ => none
  | ⟨.constant _, _⟩ => none

/-- Addition-result shadows extracted from a list of arithmetic atoms. -/
def additionShadows
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) : List Q :=
  atoms.filterMap (Atom.additionShadow? certificate)

@[simp] theorem additionShadows_cons_add
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (arguments : Fin 2 → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    additionShadows certificate (⟨.add, arguments⟩ :: atoms) =
      certificate.feature
        (arguments (0 : Fin 2) + arguments (1 : Fin 2)) ::
          additionShadows certificate atoms := rfl

@[simp] theorem additionShadows_cons_mul
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (arguments : Fin 2 → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    additionShadows certificate (⟨.mul, arguments⟩ :: atoms) =
      additionShadows certificate atoms := rfl

@[simp] theorem additionShadows_cons_constant
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (scalar : C)
    (arguments : Fin (Algebraic.Arithmetic.arity (.constant scalar)) → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    additionShadows certificate (⟨.constant scalar, arguments⟩ :: atoms) =
      additionShadows certificate atoms := rfl

/-- The number of retained shadows is exactly the addition cost. -/
theorem additionShadows_length
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    (additionShadows certificate atoms).length =
      Atom.listCost atoms
        (Algebraic.Arithmetic.additionCost (K := C)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      cases atom with
      | mk op arguments =>
          cases op with
          | add =>
              change Fin 2 → U at arguments
              rw [additionShadows_cons_add]
              simp [Atom.listCost, Atom.cost, inductionHypothesis,
                Nat.add_comm]
          | mul =>
              change Fin 2 → U at arguments
              rw [additionShadows_cons_mul]
              simpa [Atom.listCost, Atom.cost] using inductionHypothesis
          | constant scalar =>
              rw [additionShadows_cons_constant]
              simpa [Atom.listCost, Atom.cost] using inductionHypothesis

/-- Submodule generated by the shadows of all addition results in an atom
list. -/
noncomputable def generatedSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    Submodule K Q :=
  Submodule.span K
    (Set.range fun index : Fin (additionShadows certificate atoms).length =>
      (additionShadows certificate atoms).get index)

/-- The shadow of an addition atom in the list belongs to the generated
submodule. -/
theorem additionShadow_mem_generatedSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U))
    (arguments : Fin 2 → U)
    (present : (⟨.add, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature C) U) ∈ atoms) :
    certificate.feature
        (arguments (0 : Fin 2) + arguments (1 : Fin 2)) ∈
      generatedSubmodule certificate atoms := by
  have shadowPresent : certificate.feature
        (arguments (0 : Fin 2) + arguments (1 : Fin 2)) ∈
      additionShadows certificate atoms := by
    change _ ∈ atoms.filterMap (Atom.additionShadow? certificate)
    rw [List.mem_filterMap]
    exact ⟨⟨.add, arguments⟩, present, rfl⟩
  obtain ⟨index, indexSpec⟩ := List.mem_iff_get.mp shadowPresent
  apply Submodule.subset_span
  exact ⟨index, indexSpec⟩

/-- Every wire feature lies in the span of addition-result shadows from any
atom list containing the whole program. -/
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
      cases wire with
      | input input =>
          rw [Program.trace_input, certificate.input_zero input]
          exact (generatedSubmodule certificate allAtoms).zero_mem
      | gate impossible => exact Fin.elim0 impossible
  | @gate g program line inductionHypothesis =>
      have priorSubset : ∀ atom,
          atom ∈ programAtoms
            (Algebraic.Arithmetic.interpretation constant)
            problem.inputs program → atom ∈ allAtoms := by
        intro atom present
        exact atomsSubset atom (List.mem_append_left _ present)
      have priorMem := inductionHypothesis priorSubset
      intro wire
      induction wire using Wire.lastCases with
      | last =>
          let lastAtom := lineAtom line program
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
                  exact additionShadow_mem_generatedSubmodule certificate
                    allAtoms
                    (fun argument : Fin 2 =>
                      program.trace
                        (Algebraic.Arithmetic.interpretation constant)
                        problem.inputs (wires argument)) (by
                      simpa [lastAtom, lineAtom, Function.comp_def] using
                        lastPresent)
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
                  exact (generatedSubmodule certificate allAtoms).add_mem
                    ((generatedSubmodule certificate allAtoms).smul_mem
                      leftScalar (priorMem (wires (0 : Fin 2))))
                    ((generatedSubmodule certificate allAtoms).smul_mem
                      rightScalar (priorMem (wires (1 : Fin 2))))
              | constant scalar =>
                  change certificate.feature (constant scalar) ∈
                    generatedSubmodule certificate allAtoms
                  rw [certificate.constant_zero scalar]
                  exact (generatedSubmodule certificate allAtoms).zero_mem
      | castSucc priorWire =>
          rw [Program.trace_gate_castSucc]
          exact priorMem priorWire

/-- Every output feature lies in the common span of the circuit's addition
result shadows. -/
theorem feature_circuit_output_mem
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
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

end Semiring

section Field

variable [Field K] [Add U] [Mul U]
variable [AddCommMonoid Q] [Module K Q]

/-- Every requested output feature belongs to the common addition-shadow span
of a constructing circuit. -/
theorem targetFeature_mem_circuitSubmodule
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Interaction.Multiple.Constructs (constant := constant)
      problem targets circuit)
    (output : Fin m) :
    certificate.feature (targets output) ∈
      generatedSubmodule certificate
        (circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation constant) problem.inputs) := by
  rw [← congrFun constructs output]
  exact feature_circuit_output_mem certificate circuit output

/-- The dimension of the requested output-shadow span is at most the number
of addition gates. -/
theorem featureSpan_finrank_le_additionCost
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Interaction.Multiple.Constructs (constant := constant)
      problem targets circuit) :
    Module.finrank K
        (Submodule.span K (Set.range (certificate.feature ∘ targets))) ≤
      circuit.cost (Algebraic.Arithmetic.additionCost (K := C)) := by
  classical
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation constant) problem.inputs
  let additionFeature :
      Fin (additionShadows certificate atoms).length → Q :=
    fun index => (additionShadows certificate atoms).get index
  have targetSpan_le :
      Submodule.span K (Set.range (certificate.feature ∘ targets)) ≤
        generatedSubmodule certificate atoms := by
    apply Submodule.span_le.mpr
    intro featureValue present
    obtain ⟨output, rfl⟩ := present
    exact targetFeature_mem_circuitSubmodule certificate targets circuit
      constructs output
  let _ : Module.Finite K (generatedSubmodule certificate atoms) := by
    change Module.Finite K
      (Submodule.span K (Set.range additionFeature))
    exact Module.Finite.span_of_finite K (Set.finite_range additionFeature)
  calc
    Module.finrank K
        (Submodule.span K (Set.range (certificate.feature ∘ targets))) ≤
        Module.finrank K (generatedSubmodule certificate atoms) :=
      Submodule.finrank_mono targetSpan_le
    _ ≤ (additionShadows certificate atoms).length := by
      have additionFinrank :=
        finrank_range_le_card (R := K) additionFeature
      unfold Set.finrank at additionFinrank
      simp only [Fintype.card_fin] at additionFinrank
      change Module.finrank K
          (Submodule.span K (Set.range additionFeature)) ≤
        (additionShadows certificate atoms).length
      exact additionFinrank
    _ = Atom.listCost atoms
        (Algebraic.Arithmetic.additionCost (K := C)) :=
      additionShadows_length certificate atoms
    _ = circuit.cost
        (Algebraic.Arithmetic.additionCost (K := C)) := by
      simpa [atoms] using circuitAtoms_cost circuit
        (Algebraic.Arithmetic.interpretation constant) problem.inputs
        (Algebraic.Arithmetic.additionCost (K := C))

/-- Linearly independent output shadows force one addition gate per output. -/
theorem circuit_addition_lowerBound_of_linearIndependent
    {constant : C → U}
    {problem : Problem U}
    (certificate : Certificate (K := K) (Q := Q) constant problem)
    (targets : Fin m → U)
    (independent : LinearIndependent K (certificate.feature ∘ targets))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Interaction.Multiple.Constructs (constant := constant)
      problem targets circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.additionCost (K := C)) := by
  have spanBound := featureSpan_finrank_le_additionCost certificate targets
    circuit constructs
  have dimensionEq : Module.finrank K
      (Submodule.span K (Set.range (certificate.feature ∘ targets))) = m := by
    simpa using finrank_span_eq_card independent
  rwa [dimensionEq] at spanBound

end Field

end MultiplicativeShadow
end Arithmetic
end Fusion
end Algebraic
