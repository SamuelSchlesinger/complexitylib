/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Restriction

/-!
# Restricting one-output De Morgan circuits

The source program is restricted directly, and its designated output wire is
then materialized in the residual program when necessary. Deleted charged
gates are indexed by `Fin source.size`, the original source-gate type. The exact cost
identity is exposed as a standard `Circuit.Reduction` certificate.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/--
Restriction of a one-output De Morgan circuit, with the exact set of deleted
charged source gates.
-/
structure CircuitRestriction
    (source : Circuit signature (n + 1) 1)
    (selected : Fin (n + 1))
    (fixedValue : Bool) where
  /-- Residual circuit on the remaining inputs. -/
  result : Circuit signature n 1
  /-- Deleted charged gates in the original source program. -/
  deleted : Finset (Fin source.size)
  /-- Pointwise semantics under the chosen input restriction. -/
  eval_eq : ∀ input,
    result.eval interpretation input =
      source.eval interpretation
        ((InputSubstitution.fix selected fixedValue).apply input)
  /-- The deletion set accounts exactly for the charged-cost decrease. -/
  cost_eq : deleted.card + result.cost binaryCost = source.cost binaryCost

namespace CircuitRestriction

/-- Number of internal gates in the residual circuit. -/
abbrev gateCount
    {source : Circuit signature (n + 1) 1}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : CircuitRestriction source selected fixedValue) : Nat :=
  restriction.result.size

/-- Materialize the residual value of the designated source output, using
at most one free gate for a constant or a negation. -/
def ofProgram
    {source : Circuit signature (n + 1) 1}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (program : ProgramRestriction source.program selected fixedValue) :
    CircuitRestriction source selected fixedValue := by
  let outputValue := program.values (source.outputs 0)
  let materialized := materialize program.result outputValue
  exact
    { result := { program := materialized.result, outputs := fun _ => materialized.output }
      deleted := program.deleted
      eval_eq := by
        intro input
        funext output
        have output_eq : output = 0 := Fin.eq_zero output
        subst output
        change materialized.result.trace interpretation input materialized.output = _
        rw [materialized.output_eq]
        exact program.trace_eq input (source.outputs 0)
      cost_eq := by
        change program.deleted.card + materialized.result.cost binaryCost = source.cost binaryCost
        rw [materialized.cost_eq]
        exact program.cost_eq }

/-- View an exact circuit restriction as a generic certified reduction. -/
def toReduction
    {source : Circuit signature (n + 1) 1}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : CircuitRestriction source selected fixedValue) :
    Circuit.Reduction binaryCost source interpretation
      (InputSubstitution.fix selected fixedValue) where
  result := restriction.result
  eval_eq := restriction.eval_eq
  saving := restriction.deleted.card
  saving_le := restriction.cost_eq.le

end CircuitRestriction

/-- Partial-evaluate a one-output circuit after fixing one input. -/
noncomputable def restrictCircuit
    (source : Circuit signature (n + 1) 1)
    (selected : Fin (n + 1))
    (fixedValue : Bool) :
    CircuitRestriction source selected fixedValue := by
  exact CircuitRestriction.ofProgram
    (restrictProgram selected fixedValue
      source.program)

/-- Circuit restriction exposes exactly the source program's deletion set. -/
@[simp] theorem restrictCircuit_deleted
    (source : Circuit signature (n + 1) 1)
    (selected : Fin (n + 1))
    (fixedValue : Bool) :
    (restrictCircuit source selected fixedValue).deleted =
      (restrictProgram selected fixedValue source.program).deleted := rfl

end DeMorgan
end Algebraic
