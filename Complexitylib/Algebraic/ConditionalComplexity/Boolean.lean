/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.ConditionalComplexity
public import Cslib.Computability.Circuit.Boolean.Synthesis

/-!
# Conditional circuits give Boolean synthesis bounds

A circuit with formal supplied inputs can be appended to any program already
computing those values. All existing wires are preserved, so its gate budget
gives CSLib's `Synthesis` predicate. No converse is asserted: `Synthesis`
quantifies over starting programs and can use all their intermediate wires.
-/

@[expose] public section

open Algebraic

namespace Cslib.Circuits.Boolean

/-- A conditional circuit can be instantiated after any program that already
computes its supplied family, preserving all existing wire functions. -/
theorem synthesis_of_conditionalGateComplexity_le
    (target : Target Bool n m) (supplied : Target Bool n k) (budget : Nat)
    (bounded : Circuit.conditionalGateComplexity interpretation target supplied ≤ budget) :
    Synthesis interpretation (Set.range fun i input => supplied input i)
      (Set.range fun i input => target input i) budget := by
  classical
  obtain ⟨gates, sizeBound, circuit, computes⟩ :=
    (Circuit.conditionalGateComplexity_le_iff interpretation target supplied budget).mp bounded
  intro priorGates prior availableGiven
  choose wires wiresEval using fun i =>
    mem_available.mp (availableGiven (Set.mem_range_self i))
  let inputWires : Fin (n + k) → Wire n priorGates := Fin.append Wire.input wires
  let combined := circuit.instantiate prior inputWires
  refine ⟨priorGates + gates, combined.program, Nat.add_le_add_left sizeBound _, ?_, ?_⟩
  · intro f present
    obtain ⟨wire, wireEval⟩ := mem_available.mp present
    apply mem_available.mpr
    refine ⟨Wire.Renaming.castAdd gates wire, fun input => ?_⟩
    exact (circuit.program.instantiate_trace_ambient prior inputWires interpretation input wire).trans
      (wireEval input)
  · rintro _ ⟨output, rfl⟩
    apply mem_available.mpr
    refine ⟨combined.outputs output, fun input => ?_⟩
    change combined.eval interpretation input output = _
    rw [Circuit.eval_instantiate]
    have inputsEq : prior.trace interpretation input ∘ inputWires =
        Fin.append input (supplied input) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [inputWires]
      · simpa [inputWires, Function.comp_def] using wiresEval j input
    rw [inputsEq]
    exact congrFun (computes input) output

end Cslib.Circuits.Boolean
