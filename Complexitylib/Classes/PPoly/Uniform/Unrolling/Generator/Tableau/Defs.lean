/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Finalization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Defs

/-!
# Complete direct-unrolling generator -- definitions

The positive tableau body emits the initial packed configuration, exactly one
packed transition layer per horizon step, and the padded terminal acceptance
fragment. The outer step counter is restored after the loop. Prefixing this
body with `program` also handles the separately tagged length-zero family
member.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Emit all packed transition layers and restore the outer step counter. -/
noncomputable def emitTransitionSteps (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryFor (emitStep tm) Work.loop₂ Work.horizon)
    (BinaryRoutine.clear Work.loop₂)

/-- Compact semantic entry contract for the complete transition-layer loop. -/
structure TransitionEntry (tm : TM k)
    (values : BinaryValues WorkCount) : Prop where
  /-- All reusable transition scratch starts clean. -/
  clean : StepClean values
  /-- Layer enumeration starts at zero. -/
  loop₂ : values Work.loop₂ = 0
  /-- At least one represented configuration layer exists. -/
  horizon : 0 < values Work.horizon

/-- Transition-layer loop with its compact semantic precondition exposed
without changing the concrete machine or any behavioral/resource field. -/
noncomputable def tableauTransitionSteps (tm : TM k) :
    BinaryRoutine WorkCount :=
  (emitTransitionSteps tm).restrict (TransitionEntry tm)

/-- Compact semantic entry contract for final acceptance, padding, and copy. -/
structure FinalizationEntry (values : BinaryValues WorkCount) : Prop where
  /-- Raw-gate emission scratch is clear. -/
  emitCounter : values Work.emitCounter = 0
  /-- Binary-copy scratch is clear. -/
  copyCounter : values Work.copyCounter = 0
  /-- Addition scratch is clear. -/
  addCounter : values Work.addCounter = 0
  /-- Multiplication scratch is clear. -/
  multiplyCounter : values Work.multiplyCounter = 0
  /-- The acceptance gate fits before the closed padding frontier. -/
  available : values Work.available + 1 ≤ values Work.frontier

/-- Finalization phase with its compact semantic precondition exposed without
changing the concrete machine or any behavioral/resource field. -/
noncomputable def tableauFinalization (tm : TM k) : BinaryRoutine WorkCount :=
  (finalization tm).restrict FinalizationEntry

/-- Complete positive-length tableau body, excluding the tagged header. -/
noncomputable def positiveTableauBody (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq (initialization tm)
    (BinaryRoutine.seq (tableauTransitionSteps tm) (tableauFinalization tm))

/-- Complete zero/positive generator for the padded direct-unrolling code. -/
noncomputable def paddedDirectUnrollingProgram
    (tm : TM k) (q : Polynomial ℕ) : BinaryRoutine WorkCount :=
  program tm q (positiveTableauBody tm)

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
