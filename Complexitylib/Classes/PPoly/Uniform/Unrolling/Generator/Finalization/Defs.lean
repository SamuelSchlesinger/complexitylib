/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Finalization.Defs

/-!
# Direct-unrolling finalization generator -- definitions

This phase emits the original acceptance gate, pads with dead constant gates
until the precomputed closed frontier, and finally copies the saved acceptance
wire. The binary padding driver uses `available` itself as its counter, so no
gate-counting pass or unary work fuel is needed.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Numeric acceptance gate reconstructed from the current final-configuration
base and horizon. -/
noncomputable def currentAcceptanceGate (tm : TM k)
    (values : BinaryValues WorkCount) : CircuitCode.RawGate :=
  numericAcceptanceGate (Fintype.card tm.Q)
    (stateIndex tm.toNTM tm.qhalt) (k + 2) (values Work.horizon)
    (values Work.configBase)

/-- Pure endpoint of acceptance-reference preparation. -/
noncomputable def acceptanceReferenceValues (tm : TM k)
    (values : BinaryValues WorkCount) : BinaryValues WorkCount :=
  let gate := currentAcceptanceGate tm values
  let values := Function.update values Work.reference₀
    gate.input₀
  let values := Function.update values Work.reference₁
    gate.input₁
  let values := Function.update values Work.temporary₀ 0
  let values := Function.update values Work.temporary₁ 0
  Function.update values Work.temporary₂ 0

/-- Pure endpoint after saving and emitting the original acceptance gate. -/
noncomputable def afterAcceptanceValues (tm : TM k)
    (values : BinaryValues WorkCount) : BinaryValues WorkCount :=
  let values := acceptanceReferenceValues tm values
  let values := Function.update values Work.savedOutput
    (values Work.available)
  let values := Function.update values Work.available
    (values Work.available + 1)
  let values := Function.update values Work.reference₀ 0
  Function.update values Work.reference₁ 0

/-- Prepare the final-state reference of the numeric acceptance gate. -/
noncomputable def prepareAcceptanceStateReference (tm : TM k) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.set Work.reference₀ (stateIndex tm.toNTM tm.qhalt))
    (BinaryRoutine.add Work.configBase Work.reference₀ Work.addCounter)

/-- Add the final output tape's cell-block base to the second reference. -/
noncomputable def prepareAcceptanceCellPrefix (tm : TM k) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.reference₁ (Fintype.card tm.Q),
      BinaryRoutine.add Work.configBase Work.reference₁ Work.addCounter,
      BinaryRoutine.set Work.temporary₀ 1,
      BinaryRoutine.add Work.horizon Work.temporary₀ Work.addCounter,
      BinaryRoutine.set Work.temporary₁ (k + 2),
      BinaryRoutine.mulAdd Work.temporary₀ Work.temporary₁ Work.reference₁
        Work.multiplyCounter Work.addCounter,
      BinaryRoutine.clear Work.temporary₀,
      BinaryRoutine.clear Work.temporary₁]

/-- Add output-cell position one and symbol-one's fixed offset. -/
def prepareAcceptanceCellOffset (k : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.temporary₀ 2,
      BinaryRoutine.add Work.horizon Work.temporary₀ Work.addCounter,
      BinaryRoutine.set Work.temporary₁ (k + 1),
      BinaryRoutine.clear Work.temporary₂,
      BinaryRoutine.mulAdd Work.temporary₁ Work.temporary₀ Work.temporary₂
        Work.multiplyCounter Work.addCounter,
      BinaryRoutine.addConst Work.temporary₂ 1,
      BinaryRoutine.set Work.temporary₁ 4,
      BinaryRoutine.mulAdd Work.temporary₂ Work.temporary₁ Work.reference₁
        Work.multiplyCounter Work.addCounter,
      BinaryRoutine.addConst Work.reference₁ 1,
      BinaryRoutine.clear Work.temporary₀,
      BinaryRoutine.clear Work.temporary₁,
      BinaryRoutine.clear Work.temporary₂]

/-- Prepare the two absolute references of the numeric acceptance gate. -/
noncomputable def prepareAcceptanceReferences (tm : TM k) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareAcceptanceStateReference tm,
      prepareAcceptanceCellPrefix tm,
      prepareAcceptanceCellOffset k]

/-- Emit the original acceptance gate and save its absolute output wire. -/
noncomputable def emitAcceptance (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareAcceptanceReferences tm,
      BinaryRoutine.binaryCopy Work.available Work.savedOutput Work.copyCounter,
      BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.reference₀ Work.reference₁,
      BinaryRoutine.clear Work.reference₀,
      BinaryRoutine.clear Work.reference₁]

/-- One dead constant-false padding gate. The surrounding loop, rather than
this body, advances `available`. -/
def emitPaddingGate : BinaryRoutine WorkCount :=
  BinaryRoutine.emitRawGate .and false true Work.emitCounter Work.reference₀
    Work.reference₀

/-- Emit dead gates until `available = frontier`. -/
def emitPadding : BinaryRoutine WorkCount :=
  BinaryRoutine.binaryFor emitPaddingGate Work.available Work.frontier

/-- Emit the terminal gate that restores the original acceptance output. -/
def emitTerminalCopy : BinaryRoutine WorkCount :=
  BinaryRoutine.emitRawGateStep .and false false Work.emitCounter Work.available
    Work.savedOutput Work.savedOutput

/-- Complete acceptance, padding, and terminal-copy phase. -/
noncomputable def finalization (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitAcceptance tm, emitPadding, emitTerminalCopy,
      BinaryRoutine.clear Work.savedOutput]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
