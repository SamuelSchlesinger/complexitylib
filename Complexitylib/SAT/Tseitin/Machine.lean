/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.NormalForm
public import Complexitylib.SAT.Tseitin.Machine.Controller
public import Complexitylib.SAT.Tseitin.Machine.Internal.PolynomialTime

/-!
# Polynomial-time Tseitin reduction machine

This surface module exposes the concrete deterministic machine implementing
the total encoded CNF-SAT-to-3SAT reduction. Its explicit quartic time bound
includes validation, register initialization, valid-input transformation, and
the fixed malformed-input fallback.

## Main results

- `ThreeSAT.Machine.reductionTM_computesInTime`
- `ThreeSAT.reduction_mem_FP`
-/


public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- The concrete Tseitin reduction machine computes the total encoded
reduction within an explicit quartic time bound. -/
theorem reductionTM_computesInTime :
    reductionTM.ComputesInTime reduction
      (fun n => 6 * n + 16384 * (n + 2) ^ 4 + 49) := by
  exact reductionTM_computesInTime_internal

end Machine

/-- The total encoded CNF-SAT-to-3SAT reduction is polynomial-time
computable. -/
theorem reduction_mem_FP : reduction ∈ FP := by
  rw [mem_FP_iff_computesInTime_polynomial]
  let p : Polynomial ℕ :=
    Polynomial.C 6 * Polynomial.X +
      Polynomial.C 16384 * (Polynomial.X + Polynomial.C 2) ^ 4 +
      Polynomial.C 49
  refine ⟨Machine.workTapeCount, Machine.reductionTM, p, ?_⟩
  simpa [p] using Machine.reductionTM_computesInTime

end ThreeSAT

end SAT

end Complexity
