/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic.Expression
public import Complexitylib.Algebraic.LowerBound.Fusion.Substitution

/-!
# Local Fusion properties of compiled arithmetic expressions

An expression can carry a semantic predicate that must hold at the output of
every multiplication node.  Tree compilation preserves this predicate at
every extracted multiplication atom.  This packages local gate-shape proofs
independently of any particular rank measure or polynomial family.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Expression

variable {C : Type} {R : Type}

/-- A semantic predicate holds at the result of every multiplication node in
an arithmetic expression. -/
def MultiplicationProperty
    [Add R]
    [Mul R]
    (constant : C → R)
    (input : Fin n → R)
    (property : R → Prop) : Algebraic.Arithmetic.Expression C n → Prop
  | .input _ | .constant _ => True
  | .add left right =>
      MultiplicationProperty constant input property left ∧
        MultiplicationProperty constant input property right
  | .mul left right =>
      MultiplicationProperty constant input property left ∧
        MultiplicationProperty constant input property right ∧
        property
          (Algebraic.Arithmetic.Expression.eval constant input left *
            Algebraic.Arithmetic.Expression.eval constant input right)

/-- Every multiplication atom emitted by expression compilation satisfies
the expression's multiplication-result predicate. -/
theorem multiplicationProperty_of_atom
    [Add R]
    [Mul R]
    (constant : C → R)
    (input : Fin n → R)
    (property : R → Prop)
    (expression : Algebraic.Arithmetic.Expression C n)
    (holds : MultiplicationProperty constant input property expression)
    (arguments : Fin 2 → R)
    (present : (⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature C) R) ∈
        circuitAtoms
          (Algebraic.Arithmetic.Expression.circuit expression)
          (Algebraic.Arithmetic.interpretation constant) input) :
    property (arguments (0 : Fin 2) * arguments (1 : Fin 2)) := by
  induction expression with
  | input index =>
      simp [circuitAtoms, Algebraic.Arithmetic.Expression.circuit,
        Algebraic.Arithmetic.Expression.compile] at present
  | constant value =>
      simp [circuitAtoms, Algebraic.Arithmetic.Expression.circuit,
        Algebraic.Arithmetic.Expression.compile, lineAtom] at present
      have operationEqual := congrArg Atom.op present
      contradiction
  | add left right leftIH rightIH =>
      rcases holds with ⟨leftHolds, rightHolds⟩
      change (⟨.mul, arguments⟩ :
        Atom (Algebraic.Arithmetic.signature C) R) ∈
          programAtoms (Algebraic.Arithmetic.interpretation constant) input
            (Algebraic.Arithmetic.Expression.compile (.add left right)).program
        at present
      simp only [Algebraic.Arithmetic.Expression.compile,
        programAtoms_gate] at present
      rw [programAtoms_instantiate] at present
      have inputWires_eval :
          (Algebraic.Arithmetic.Expression.compile left).program.trace
                (Algebraic.Arithmetic.interpretation constant) input ∘
              (Wire.input : Fin n → Wire n left.gateCount) = input := by
        funext index
        exact Program.trace_input
          (Algebraic.Arithmetic.Expression.compile left).program
          (Algebraic.Arithmetic.interpretation constant) input index
      rw [inputWires_eval] at present
      rcases List.mem_append.mp present with prior | last
      · rcases List.mem_append.mp prior with inLeft | inRight
        · exact leftIH leftHolds inLeft
        · exact rightIH rightHolds inRight
      · have operationEqual := congrArg Atom.op
          (List.mem_singleton.mp last)
        contradiction
  | mul left right leftIH rightIH =>
      rcases holds with ⟨leftHolds, rightHolds, rootHolds⟩
      change (⟨.mul, arguments⟩ :
        Atom (Algebraic.Arithmetic.signature C) R) ∈
          programAtoms (Algebraic.Arithmetic.interpretation constant) input
            (Algebraic.Arithmetic.Expression.compile (.mul left right)).program
        at present
      simp only [Algebraic.Arithmetic.Expression.compile,
        programAtoms_gate] at present
      rw [programAtoms_instantiate] at present
      have inputWires_eval :
          (Algebraic.Arithmetic.Expression.compile left).program.trace
                (Algebraic.Arithmetic.interpretation constant) input ∘
              (Wire.input : Fin n → Wire n left.gateCount) = input := by
        funext index
        exact Program.trace_input
          (Algebraic.Arithmetic.Expression.compile left).program
          (Algebraic.Arithmetic.interpretation constant) input index
      rw [inputWires_eval] at present
      rcases List.mem_append.mp present with prior | last
      · rcases List.mem_append.mp prior with inLeft | inRight
        · exact leftIH leftHolds inLeft
        · exact rightIH rightHolds inRight
      · have atomEqual := List.mem_singleton.mp last
        have resultEqual := congrArg
          (fun atom : Atom (Algebraic.Arithmetic.signature C) R =>
            atom.result (Algebraic.Arithmetic.interpretation constant))
          atomEqual
        have rootValue :
            (lineAtom
                { op := Algebraic.Arithmetic.Op.mul
                  wires := fun argument =>
                    Fin.cases
                      (Wire.Renaming.castAdd right.gateCount
                        (Algebraic.Arithmetic.Expression.compile left).output)
                      (fun _ => Wire.Substitution.append
                        (Wire.input : Fin n → Wire n left.gateCount)
                        right.gateCount
                        (Algebraic.Arithmetic.Expression.compile right).output)
                      (Fin.cast (Algebraic.Arithmetic.arity_mul (K := C))
                        argument) }
                ((Algebraic.Arithmetic.Expression.compile right).program.instantiate
                    (Algebraic.Arithmetic.Expression.compile left).program
                    Wire.input)
                (Algebraic.Arithmetic.interpretation constant) input).result
                (Algebraic.Arithmetic.interpretation constant) =
              Algebraic.Arithmetic.Expression.eval constant input
                (.mul left right) := by
          simpa [Algebraic.Arithmetic.Expression.compile,
            Algebraic.Arithmetic.Expression.eval, lineAtom_result] using
              Algebraic.Arithmetic.Expression.compile_trace constant input
                (.mul left right)
        rw [rootValue] at resultEqual
        change property
          ((⟨.mul, arguments⟩ :
            Atom (Algebraic.Arithmetic.signature C) R).result
              (Algebraic.Arithmetic.interpretation constant))
        rw [resultEqual]
        exact rootHolds

end Expression
end Arithmetic
end Fusion
end Algebraic
