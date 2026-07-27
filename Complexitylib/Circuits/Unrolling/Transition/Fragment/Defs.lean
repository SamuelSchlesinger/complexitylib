/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Defs

/-!
# Packed circuit fragments for one Turing-machine transition

This definitions layer compiles the canonical list of next-configuration
formulas into one appendable raw-circuit fragment. The formula outputs are
copied into a contiguous block in configuration-atom order, so that block can
serve directly as the input configuration of a later unrolled step.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Next-configuration formulas in the canonical configuration-atom order. -/
noncomputable def stepFormulas (tm : NTM k) (T configBase choiceWire : ℕ) :
    List BoolFormula :=
  (configAtoms tm T).map (nextFormula tm T configBase choiceWire)

/-- Exact number of gates emitted by the packed one-step fragment. -/
noncomputable def stepFragmentSize (tm : NTM k) (T configBase choiceWire : ℕ) : ℕ :=
  ((stepFormulas tm T configBase choiceWire).map BoolFormula.size).sum +
    (stepFormulas tm T configBase choiceWire).length

/-- Machine-dependent coefficient in the quadratic one-step size bound. -/
noncomputable def stepSizeCoeff (tm : NTM k) : ℕ :=
  let tapeCount := k + 2
  let stateCount := Fintype.card tm.Q
  let caseCount := (transitionCases tm).length
  (stateCount + 5 * tapeCount) *
    (24 + 3 * caseCount * (4 * tapeCount + 7))

/-- First wire of the packed successor-configuration block. -/
noncomputable def stepOutputBase (tm : NTM k) (T configBase choiceWire available : ℕ) : ℕ :=
  BoolFormula.rawBatchOutputBase available
    (stepFormulas tm T configBase choiceWire)

/-- Compile one bounded transition after an existing raw-circuit prefix.

The packed outputs follow `configAtoms`, independently of the variable sizes
of the formulas that compute them. -/
noncomputable def stepFragment (tm : NTM k) (T configBase choiceWire available : ℕ) :
    CircuitCode.RawCircuit :=
  BoolFormula.compileRawBatch available
    (stepFormulas tm T configBase choiceWire)

end CircuitUnrolling

end Complexity
