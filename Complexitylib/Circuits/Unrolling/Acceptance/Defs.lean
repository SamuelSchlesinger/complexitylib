/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Unrolling.Trace.Defs

/-!
# Acceptance gates for bounded Turing-machine traces

This definitions layer appends one final AND gate to a complete bounded-trace
fragment. Its inputs are the final configuration atoms asserting that the
machine is halted and that output cell one contains `1`. The appended gate is
therefore both the raw circuit's designated output and the acceptance bit used
when the raw circuit is reconstructed as a typed single-output circuit.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Final AND gate testing the halted state and output-cell-one acceptance
conditions in a packed configuration block. -/
noncomputable def acceptanceGate (tm : NTM k) (T configBase : ℕ) :
    CircuitCode.RawGate :=
  { op := .and
    input₀ := configWire tm T configBase (.state tm.qhalt)
    input₁ := configWire tm T configBase
      (.cell .output ⟨1, by omega⟩ Γ.one)
    negated₀ := false
    negated₁ := false }

/-- Complete bounded trace followed by its single acceptance-output gate. -/
noncomputable def acceptanceRawCircuit (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : CircuitCode.RawCircuit :=
  traceFragment tm T n available layout ++
    [acceptanceGate tm T (traceOutputBase tm T n available layout)]

/-- Machine-dependent coefficient absorbing the final acceptance gate into the
cubic bounded-trace size bound. -/
noncomputable def acceptanceSizeCoeff (tm : NTM k) : ℕ :=
  traceSizeCoeff tm + 1

/-- Exact bounded-trace acceptance bit computed from one data input and one
choice string. -/
def boundedAcceptanceBit (tm : NTM k) (T : ℕ) (x : BitString n)
    (choices : BitString T) : Bool :=
  decide ((tm.trace T choices (tm.initCfg x.toList)).state = tm.qhalt ∧
    (tm.trace T choices (tm.initCfg x.toList)).output.cells 1 = Γ.one)

end CircuitUnrolling

end Complexity
