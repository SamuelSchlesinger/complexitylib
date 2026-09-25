/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework
public import Complexitylib.Algebraic.Basis.Arithmetic

/-!
# Arithmetic atom projections

Common list-level views of semantic arithmetic-circuit atoms.  Keeping these
projections independent of any particular Fusion witness lets dyadic,
interaction-span, and future arithmetic specializations share the same notion
of a multiplication occurrence and the same exact cost accounting.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic

variable {C : Type u} {U : Type v}

/-- Retain the arguments of a multiplication atom and discard addition and
constant atoms. -/
def Atom.mulArguments?
    (atom : Atom (Algebraic.Arithmetic.signature C) U) :
    Option (Fin 2 → U) :=
  match atom with
  | ⟨.add, _⟩ => none
  | ⟨.mul, arguments⟩ => some arguments
  | ⟨.constant _, _⟩ => none

/-- Multiplication occurrences, in program order, contained in a list of
evaluated arithmetic atoms.  Equal semantic argument pairs remain distinct
list entries. -/
def multiplicationArguments
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    List (Fin 2 → U) :=
  atoms.filterMap Atom.mulArguments?

@[simp] theorem multiplicationArguments_cons_add
    (arguments : Fin 2 → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    multiplicationArguments
      ((⟨.add, arguments⟩ :
        Atom (Algebraic.Arithmetic.signature C) U) :: atoms) =
      multiplicationArguments atoms := rfl

@[simp] theorem multiplicationArguments_cons_mul
    (arguments : Fin 2 → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    multiplicationArguments
      ((⟨.mul, arguments⟩ :
        Atom (Algebraic.Arithmetic.signature C) U) :: atoms) =
      arguments :: multiplicationArguments atoms := rfl

@[simp] theorem multiplicationArguments_cons_constant
    (scalar : C)
    (arguments : Fin (Algebraic.Arithmetic.arity (.constant scalar)) → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    multiplicationArguments
      ((⟨.constant scalar, arguments⟩ :
        Atom (Algebraic.Arithmetic.signature C) U) :: atoms) =
      multiplicationArguments atoms := rfl

/-- Membership in the multiplication-occurrence projection is exactly
membership of the corresponding multiplication atom in the source list. -/
theorem mem_multiplicationArguments
    (arguments : Fin 2 → U)
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    arguments ∈ multiplicationArguments atoms ↔
      (⟨.mul, arguments⟩ :
        Atom (Algebraic.Arithmetic.signature C) U) ∈ atoms := by
  change arguments ∈ atoms.filterMap Atom.mulArguments? ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨atom, present, equal⟩
    cases atom with
    | mk op atomArguments =>
        cases op with
        | add => simp [Atom.mulArguments?] at equal
        | mul =>
            change Fin 2 → U at atomArguments
            simp only [Atom.mulArguments?] at equal
            rw [← Option.some.inj equal]
            exact present
        | constant scalar => simp [Atom.mulArguments?] at equal
  · intro present
    exact ⟨⟨.mul, arguments⟩, present, rfl⟩

/-- The number of retained multiplication occurrences is exactly their
weighted atom cost. -/
theorem multiplicationArguments_length
    (atoms : List (Atom (Algebraic.Arithmetic.signature C) U)) :
    (multiplicationArguments atoms).length =
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
              rw [multiplicationArguments_cons_add]
              simpa [Atom.listCost, Atom.cost] using inductionHypothesis
          | mul =>
              change Fin 2 → U at arguments
              rw [multiplicationArguments_cons_mul]
              simp [Atom.listCost, Atom.cost, inductionHypothesis,
                Nat.add_comm]
          | constant scalar =>
              simpa [Atom.listCost, Atom.cost] using inductionHypothesis

/-- Multiplication occurrences of an arithmetic circuit evaluated on a
particular semantic input. -/
def circuitMultiplicationArguments
    [Add U]
    [Mul U]
    (constant : C → U)
    (input : Fin n → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n m) :
    List (Fin 2 → U) :=
  multiplicationArguments
    (circuitAtoms circuit
      (Algebraic.Arithmetic.interpretation constant) input)

/-- The evaluated multiplication-occurrence list has exactly the circuit's
multiplication cost, independently of semantic coincidences between gates. -/
theorem circuitMultiplicationArguments_length
    [Add U]
    [Mul U]
    (constant : C → U)
    (input : Fin n → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n m) :
    (circuitMultiplicationArguments constant input circuit).length =
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  calc
    (circuitMultiplicationArguments constant input circuit).length =
        Atom.listCost
          (circuitAtoms circuit
            (Algebraic.Arithmetic.interpretation constant) input)
          (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
      multiplicationArguments_length _
    _ = circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
      circuitAtoms_cost circuit
        (Algebraic.Arithmetic.interpretation constant) input
        (Algebraic.Arithmetic.multiplicationCost (K := C))

end Arithmetic
end Fusion
end Algebraic
