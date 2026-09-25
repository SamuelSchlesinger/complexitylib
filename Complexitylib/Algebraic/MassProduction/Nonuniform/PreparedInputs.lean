/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Wiring

/-!
# Shared generated values with preserved original inputs

A preprocessing circuit runs once and retains all original input wires.
Downstream wiring can select generated values or original values without
duplicating the preprocessing computation or adding charged gates.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.PreparedInputs

/-- Preserve the original inputs after the generated output block. -/
def circuit (generated : Circuit DeMorgan.signature inputs gates outputs) :=
  generated.parallel (Circuit.id DeMorgan.signature inputs)

/-- Lift an original wire or constant past the generated output block. -/
def original (outputs : Nat) (wire : DeMorgan.Wiring inputs) : DeMorgan.Wiring (outputs + inputs) :=
  match wire with
  | .input index => .input (Fin.natAdd outputs index)
  | .constant value => .constant value

/-- Select one generated output wire. -/
def output (inputs : Nat) (index : Fin outputs) : DeMorgan.Wiring (outputs + inputs) :=
  .input (Fin.castAdd inputs index)

/-- The preprocessing output is its generated values followed by the original input. -/
theorem circuit_eval (generated : Circuit DeMorgan.signature inputs gates outputs)
    (input : Fin inputs → Bool) :
    (circuit generated).eval DeMorgan.interpretation input =
      Fin.append (generated.eval DeMorgan.interpretation input) input := by
  rw [circuit, Circuit.eval_parallel, Circuit.eval_id]

/-- Original values survive preprocessing exactly. -/
theorem original_eval (generated : Circuit DeMorgan.signature inputs gates outputs)
    (wire : DeMorgan.Wiring inputs) (input : Fin inputs → Bool) :
    (original outputs wire).eval ((circuit generated).eval DeMorgan.interpretation input) = wire.eval input := by
  rw [circuit_eval]
  cases wire <;> simp [original]

/-- Generated values are available as fixed wires. -/
theorem output_eval (generated : Circuit DeMorgan.signature inputs gates outputs)
    (index : Fin outputs) (input : Fin inputs → Bool) :
    (output inputs index).eval ((circuit generated).eval DeMorgan.interpretation input) =
      generated.eval DeMorgan.interpretation input index := by
  rw [circuit_eval]
  simp only [output, DeMorgan.Wiring.eval_input, Fin.append_left]

/-- Keeping the original inputs adds no charged gates. -/
theorem circuit_cost (generated : Circuit DeMorgan.signature inputs gates outputs) :
    (circuit generated).cost DeMorgan.standardCost = generated.cost DeMorgan.standardCost := by
  rw [circuit, Circuit.cost_parallel, Circuit.cost_id, Nat.add_zero]

end Algebraic.MassProduction.Nonuniform.PreparedInputs
