/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbe
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken.Defs

/-!
# Barrington leaf emission after output-probe token decoding -- definitions

The variable branch runs the bounded terminated-unary decoder and then emits
the resulting canonical branching-program instruction.  The complete leaf
dispatcher also wires true directly to constant-instruction emission and false
to a no-op, leaving only the recursive connective continuations abstract.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Decode a variable payload and emit its Barrington instruction. -/
def outputProbeDecodeVarInstrTM (tm : TM n) (controllerTapes : ℕ)
    (layout : TM.OutputProbeDecodeTokenLayout controllerTapes)
    (target : Equiv.Perm (Fin 5)) :
    TM (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  TM.seqTM
    (TM.outputProbeDecodeNatTM tm controllerTapes
      layout.natLayout.cursorIdx layout.natLayout.scratchIdx
      layout.natLayout.valueIdx layout.natLayout.activeIdx
      layout.natLayout.loopIdx layout.natLayout.fuelIdx)
    (emitVarInstrTM
      (TM.outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
      (TM.outputProbeIndexedControllerIdx n layout.natLayout.valueIdx)
      target)

/-- Concrete runtime of variable-payload decoding followed by instruction
emission. -/
def outputProbeDecodeVarInstrTime (bodyTime : ℕ → ℕ)
    (fuelValue varValue : ℕ) : ℕ :=
  TM.binaryForLoopTime bodyTime fuelValue 0 fuelValue + 1 +
    emitInstrTime varValue

/-- Decode one formula token, emit the three leaf cases, and dispatch recursive
connectives to caller-supplied continuations. -/
def outputProbeDecodeLeafInstrTM (tm : TM n) (controllerTapes : ℕ)
    (layout : TM.OutputProbeDecodeTokenLayout controllerTapes)
    (target : Equiv.Perm (Fin 5))
    (onNeg onConj onDisj onInvalid :
      TM (0 + TM.outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  TM.outputProbeDecodeTokenTM tm controllerTapes layout
    (outputProbeDecodeVarInstrTM tm controllerTapes layout target)
    (emitConstInstrTM
      (TM.outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
      (TM.outputProbeIndexedControllerIdx n layout.natLayout.valueIdx)
      target)
    TM.skipTM onNeg onConj onDisj onInvalid

end Machine

end BPCode

end Complexity
