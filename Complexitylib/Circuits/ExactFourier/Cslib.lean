/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.ExactFourier.Cslib.Defs
import Complexitylib.Circuits.ExactFourier.Cslib.Internal

/-!
# Exact scalar circuits transfer to CSLib

The translation preserves every output and all sharing. It adds exactly one
gate, for the source's free zero wire. Every addition, subtraction, and scalar
multiplication remains a separate gate of fan-in at most two.
-/

public section

namespace Complexity.ExactFourier

/-- The only additional gate produces the source's free zero wire. -/
theorem Circuit.size_toCslib {n : ℕ} (C : Circuit n) : C.toCslib.size = C.size + 1 := rfl

/-- The translation preserves the complete vector of outputs. -/
theorem Circuit.eval_toCslib {n : ℕ} (C : Circuit n) (x : Fin n → ℂ) :
    C.toCslib.eval scalarInterpretation x = C.eval x := by
  funext i
  exact C.program.trace_toCslib x (C.outputs i)

/-- Source matrix computation becomes literal CSLib function computation. -/
theorem Circuit.Computes.toCslib {n : ℕ} {C : Circuit n}
    {A : Matrix (Fin n) (Fin n) ℂ} (hC : C.Computes A) :
    C.toCslib.Computes scalarInterpretation A.mulVec := by
  intro x
  rw [C.eval_toCslib]
  exact hC x

/-- Source scalar circuits translate to CSLib circuits of fan-in at most two. -/
theorem Circuit.toCslib_fanInAtMost {n : ℕ} (C : Circuit n) :
    C.toCslib.FanInAtMost 2 := C.program.toCslib_fanInAtMost

end Complexity.ExactFourier
