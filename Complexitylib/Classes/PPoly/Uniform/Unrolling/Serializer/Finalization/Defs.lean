/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Stream.Defs

/-!
# Numeric finalization schedule for direct tableau serialization

This definitions layer describes the acceptance, padding, and terminal-copy
tail of a positive padded direct-unrolling circuit using natural-number
addresses and counts. The machine and its distinguished halt state remain
fixed compile-time parameters in the bridge theorems; no run-time schedule
value contains a configuration atom or formula tree.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Acceptance gate addressed by state count, halt-state index, tape count,
horizon, and the base of the final packed configuration. -/
def numericAcceptanceGate (stateCount haltStateIndex tapeCount T
    finalConfigBase : ℕ) : CircuitCode.RawGate :=
  { op := .and
    input₀ := finalConfigBase + haltStateIndex
    input₁ := finalConfigBase + stateCount + tapeCount * (T + 1) +
      (((tapeCount - 1) * (T + 2) + 1) * 4 + 1)
    negated₀ := false
    negated₁ := false }

/-- Exact gate count of an unpadded direct tableau with horizon `T`. -/
noncomputable def directOriginalRawGateCount (tm : TM k) (T : ℕ) : ℕ :=
  configWidth tm.toNTM T + T * directStepSize tm.toNTM T + 1

/-- Dead constant-false padding determined only by the original and closed
gate counts. -/
def directPaddingSchedule (originalRawGateCount closedBound : ℕ) :
    CircuitCode.RawCircuit :=
  List.replicate (closedBound - originalRawGateCount)
    (CircuitCode.RawGate.constant 0 false)

/-- Final output gate copying the original raw circuit's last wire. -/
def directTerminalCopyGate (n originalRawGateCount : ℕ) :
    CircuitCode.RawGate :=
  CircuitCode.RawGate.copy (n + originalRawGateCount - 1)

/-- Numeric tail following the original raw circuit: dead padding, then its
terminal output copy. -/
def directFinalizationSuffix (n originalRawGateCount closedBound : ℕ) :
    CircuitCode.RawCircuit :=
  directPaddingSchedule originalRawGateCount closedBound ++
    [directTerminalCopyGate n originalRawGateCount]

end Serializer

end CircuitUnrolling

end Complexity
