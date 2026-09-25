/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.ConditionalComplexity.Boolean
public import Mathlib.Tactic.FinCases

/-!
# Strictness of the conditional chain bound

In CSLib's Boolean basis (AND, OR, NOT, and constants, each of cost one),
let `f(x,y) = x ∧ y` and `g(x,y) = ¬(x ∧ y)`. Then
`C(f,g) = C(g) = 2`, whereas `C(f | g) = 1`.
The two-gate NAND circuit already contains the AND output. Supplying only
NAND as a free input loses access to that intermediate wire.

All equalities are kernel-checked. The tiny one-gate lower bound enumerates
the finite operation, wiring, output, and input choices using `decide`.
-/

@[expose] public section

namespace Algebraic.ConditionalComplexity

open Cslib.Circuits.Boolean

/-- The two-input conjunction as a single-output target. -/
def andTarget : Target Bool 2 1 := fun input _ => input 0 && input 1

/-- The negation of two-input conjunction as a single-output target. -/
def nandTarget : Target Bool 2 1 := fun input _ => !(input 0 && input 1)

/-- Two gates with both the intermediate AND and final NAND exposed. -/
def andNandCircuit : Circuit signature 2 2 (1 + 1) where
  program := ((Program.empty : Program signature 2 0).gate
    ⟨.and, Wire.input⟩).gate ⟨.not, fun _ => Wire.gate 0⟩
  outputs := Fin.append (fun _ => Wire.gate 0) (fun _ => Wire.gate 1)

/-- The shared circuit computes the pair of functions. -/
theorem andNandCircuit_computes :
    andNandCircuit.ComputesWith interpretation
      (fun input => Fin.append (andTarget input) (nandTarget input)) := by
  intro input
  funext output
  fin_cases output <;> rfl

private theorem no_one_gate_nand :
    ∀ (op : Op) (wires : Fin (signature.Arity op) → Wire 2 0) (output : Wire 2 1),
      ¬ ∀ input : Fin 2 → Bool,
        (Program.gate .empty ⟨op, wires⟩).trace interpretation input output =
          !(input 0 && input 1) := by
  decide

private theorem no_zero_gate_nand :
    ∀ output : Wire 2 0, ¬ ∀ input : Fin 2 → Bool,
      (Program.empty : Program signature 2 0).trace interpretation input output =
        !(input 0 && input 1) := by
  decide

private theorem no_projection_and_given_nand :
    ∀ selected : Fin (2 + 1), ¬ ∀ input : Fin 2 → Bool,
      Fin.append input (nandTarget input) selected = andTarget input 0 := by
  decide

private theorem nand_size_lower (circuit : Circuit signature 2 gates 1)
    (computes : circuit.ComputesWith interpretation nandTarget) : 2 ≤ gates := by
  by_contra small
  have cases' : gates = 0 ∨ gates = 1 := by omega
  obtain rfl | rfl := cases'
  · rcases circuit with ⟨program, outputs⟩
    cases program
    exact no_zero_gate_nand (outputs 0) (fun input => congrFun (computes input) 0)
  · rcases circuit with ⟨program, outputs⟩
    cases program with
    | gate priorProgram line =>
      cases priorProgram
      exact no_one_gate_nand line.op line.wires (outputs 0)
        (fun input => congrFun (computes input) 0)

/-- NAND requires exactly two gates in the AND/OR/NOT basis. -/
theorem gateComplexity_nand : Circuit.gateComplexity interpretation nandTarget = 2 := by
  apply le_antisymm
  · have computes : (andNandCircuit.mapOutputs (Fin.natAdd 1)).ComputesWith
        interpretation nandTarget := by
      intro input
      funext output
      simpa only [Circuit.eval_mapOutputs, Function.comp_apply, Fin.append_right] using
        congrFun (andNandCircuit_computes input) (Fin.natAdd 1 output)
    exact Circuit.gateComplexity_le computes
  · apply Circuit.le_costComplexity
    intro gates circuit computes
    simpa [Circuit.size] using
      (show (2 : ℕ∞) ≤ gates by exact_mod_cast nand_size_lower circuit computes)

/-- Exposing the intermediate conjunction in the NAND circuit is free. -/
theorem gateComplexity_and_nand :
    Circuit.gateComplexity interpretation
      (fun input => Fin.append (andTarget input) (nandTarget input)) = 2 := by
  apply le_antisymm (Circuit.gateComplexity_le andNandCircuit_computes)
  apply Circuit.le_costComplexity
  intro gates circuit computes
  have nandComputes : (circuit.mapOutputs (Fin.natAdd 1)).ComputesWith
      interpretation nandTarget := by
    intro input
    funext output
    simpa only [Circuit.eval_mapOutputs, Function.comp_apply, Fin.append_right] using
      congrFun (computes input) (Fin.natAdd 1 output)
  simpa [Circuit.size] using
    (show (2 : ℕ∞) ≤ gates by exact_mod_cast nand_size_lower _ nandComputes)

/-- Given NAND as a supplied value, one NOT gate recovers AND. -/
theorem conditionalGateComplexity_and_given_nand :
    Circuit.conditionalGateComplexity interpretation andTarget nandTarget = 1 := by
  apply le_antisymm
  · let recover : Circuit signature (2 + 1) 1 1 :=
      ⟨.gate .empty ⟨.not, fun _ => Wire.input (Fin.natAdd 2 0)⟩,
        fun _ => Wire.gate 0⟩
    have computes : recover.ComputesGiven interpretation andTarget nandTarget := by
      intro input
      funext output
      change (!(!(input 0 && input 1))) = (input 0 && input 1)
      exact Bool.not_not _
    exact Circuit.conditionalGateComplexity_le computes
  · apply Order.one_le_iff_ne_zero.mpr
    intro zero
    obtain ⟨select, agrees⟩ :=
      (Circuit.conditionalGateComplexity_eq_zero_iff interpretation andTarget nandTarget).mp zero
    exact no_projection_and_given_nand (select 0) (fun input => congrFun (agrees input) 0)

/-- The chain upper bound can be strict: its two sides here are `2` and `3`. -/
theorem gateComplexity_pair_lt_conditional_add :
    Circuit.gateComplexity interpretation
      (fun input => Fin.append (andTarget input) (nandTarget input)) <
      Circuit.conditionalGateComplexity interpretation andTarget nandTarget +
        Circuit.gateComplexity interpretation nandTarget := by
  rw [gateComplexity_and_nand, conditionalGateComplexity_and_given_nand, gateComplexity_nand]
  decide

end Algebraic.ConditionalComplexity
