/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Core.Defs

/-!
# Projection lemmas for streaming evaluator actions

These narrowly oriented rewrites expose the named code, wire, and counter
actions behind the finite-index projections used by `TM.δ`. They keep later
one-step proofs independent of the implementation's nested index tests.
-/


public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Projecting the code-tape write exposes the named code action. -/
@[simp] theorem workWrite_codeIdx {wHeads : Fin workTapeCount → Γ}
    {oHead : Γ} (action : CoreAction wHeads oHead) :
    action.workWrite codeIdx = action.code.write := by
  simp [CoreAction.workWrite, codeIdx]

/-- Projecting the wire-tape write exposes the named wire action. -/
@[simp] theorem workWrite_wiresIdx {wHeads : Fin workTapeCount → Γ}
    {oHead : Γ} (action : CoreAction wHeads oHead) :
    action.workWrite wiresIdx = action.wires.write := by
  simp [CoreAction.workWrite, codeIdx, wiresIdx]

/-- Projecting the counter-tape write exposes the named counter action. -/
@[simp] theorem workWrite_counterIdx {wHeads : Fin workTapeCount → Γ}
    {oHead : Γ} (action : CoreAction wHeads oHead) :
    action.workWrite counterIdx = action.counter.write := by
  simp [CoreAction.workWrite, codeIdx, wiresIdx, counterIdx]

/-- Projecting the code-tape direction exposes the named code action. -/
@[simp] theorem workDir_codeIdx {wHeads : Fin workTapeCount → Γ}
    {oHead : Γ} (action : CoreAction wHeads oHead) :
    action.workDir codeIdx = action.code.dir := by
  simp [CoreAction.workDir, codeIdx]

/-- Projecting the wire-tape direction exposes the named wire action. -/
@[simp] theorem workDir_wiresIdx {wHeads : Fin workTapeCount → Γ}
    {oHead : Γ} (action : CoreAction wHeads oHead) :
    action.workDir wiresIdx = action.wires.dir := by
  simp [CoreAction.workDir, codeIdx, wiresIdx]

/-- Projecting the counter-tape direction exposes the named counter action. -/
@[simp] theorem workDir_counterIdx {wHeads : Fin workTapeCount → Γ}
    {oHead : Γ} (action : CoreAction wHeads oHead) :
    action.workDir counterIdx = action.counter.dir := by
  simp [CoreAction.workDir, codeIdx, wiresIdx, counterIdx]

/-- Unfold one nonhalting evaluator step through its named `CoreAction`. -/
theorem evalFamilyCoreTM_step (c : Cfg workTapeCount evalFamilyCoreTM.Q)
    (hstate : c.state ≠ CorePhase.done) :
    evalFamilyCoreTM.step c =
      let action := coreAction c.state (fun i => (c.work i).read) c.output.read
      some
        { state := action.next
          input := c.input.move (TM.idleDir c.input.read)
          work := fun i => (c.work i).writeAndMove
            (action.workWrite i) (action.workDir i)
          output := c.output.writeAndMove action.output.write action.output.dir } := by
  rw [TM.step]
  simp only [evalFamilyCoreTM]
  erw [ite_eq_right hstate]

end Internal

end Machine

end CircuitCode

end Complexity
