/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Defs

/-!
# Streamable deterministic unrolling arithmetic — definitions

This definitions layer isolates the numeric data needed by a future streaming
serializer. Formula tree sizes do not depend on the absolute wire numbers stored
at their leaves, so one canonical choice of incoming bases determines the size
of every transition formula and of every packed transition layer.

The direct deterministic prefix build fixes the primary-wire layout used by
`TM.directUnrollingRawCircuit`. It remains a proof-level circuit construction;
no Turing-machine generator is defined here.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Canonical tree size of the next-configuration formula for one atom.

The zero wire bases are only representatives: the surface theorem
`size_nextFormula_eq_directStepFormulaSize` proves that every choice of absolute
configuration and choice wires has this size. -/
noncomputable def directStepFormulaSize (tm : NTM k) (T : ℕ)
    (atom : ConfigAtom tm T) : ℕ :=
  (nextFormula tm T 0 0 atom).size

/-- Exact gate count of one packed transition layer, expressed without incoming
wire bases. The first summand compiles every next-configuration formula; the
configuration-width summand copies their outputs into the packed successor block. -/
noncomputable def directStepSize (tm : NTM k) (T : ℕ) : ℕ :=
  ((configAtoms tm T).map (directStepFormulaSize tm T)).sum + configWidth tm T

end CircuitUnrolling

namespace TM

/-- Canonical deterministic trace prefix used by the direct-unrolling family.
All semantically irrelevant nondeterministic-choice wires reuse primary wire zero. -/
noncomputable def directPrefixTraceBuild (tm : TM k) (T n i : ℕ) [NeZero n] :
    CircuitUnrolling.TraceBuild :=
  CircuitUnrolling.prefixTraceBuild tm.toNTM T n n i
    (CircuitUnrolling.deterministicInputWires T n)

/-- The deterministic transition fragment at canonical layer `i`, with all
absolute bases replaced by their closed forms. -/
noncomputable def directStepFragment (tm : TM k) (T n : ℕ) (i : Fin T) :
    CircuitCode.RawCircuit :=
  CircuitUnrolling.stepFragment tm.toNTM T
    (n + i.val * CircuitUnrolling.directStepSize tm.toNTM T) 0
    (n + CircuitUnrolling.configWidth tm.toNTM T +
      i.val * CircuitUnrolling.directStepSize tm.toNTM T)

end TM

end Complexity
