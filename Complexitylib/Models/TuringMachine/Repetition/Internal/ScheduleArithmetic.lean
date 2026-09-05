/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Defs

/-!
# Schedule arithmetic internals for fixed-time repetition

This module proves the arithmetic and compact-seed alignment facts shared by
the public repetition surface and the proof-internal schedule. Keeping these
proofs below the public surface prevents internal correctness modules from
depending on `Complexitylib.Models.TuringMachine.Repetition`.
-/


public section

namespace Complexity

namespace NTM

/-! ### Exact schedule arithmetic -/

/-- Internal form of the zero-time stride calculation. -/
theorem repeatAtTimeStride_zero_internal : repeatAtTimeStride 0 = 2 := rfl

/-- Internal form of the successor-time stride calculation. -/
theorem repeatAtTimeStride_succ_internal (T : ℕ) :
    repeatAtTimeStride (T + 1) = repeatAtTimeStride T + 2 := by
  simp only [repeatAtTimeStride]
  omega

/-- Internal form of the zero-repetition schedule calculation. -/
theorem repeatAtTimeSteps_zero_internal (T : ℕ) :
    repeatAtTimeSteps 0 T = 2 := by
  simp [repeatAtTimeSteps]

/-- Internal form of the zero-time schedule calculation. -/
theorem repeatAtTimeSteps_zero_time_internal (k : ℕ) :
    repeatAtTimeSteps k 0 = 2 + k * 2 := by
  simp [repeatAtTimeSteps, repeatAtTimeStride_zero_internal]

/-- Internal form of the successor-repetition schedule calculation. -/
theorem repeatAtTimeSteps_succ_internal (k T : ℕ) :
    repeatAtTimeSteps (k + 1) T = repeatAtTimeSteps k T + repeatAtTimeStride T := by
  simp [repeatAtTimeSteps, Nat.add_mul, Nat.add_assoc]

/-! ### Compact-seed alignment -/

/-- Internal form of the compact-seed and machine-schedule alignment. -/
theorem repeatRandomSeed_apply_repeatChoiceIdx_internal (k T : ℕ)
    (choices : Fin (repeatAtTimeSteps k T) → Bool) (j : Fin k) (t : Fin T) :
    repeatRandomSeed k T choices (finProdFinEquiv (j, t)) =
      choices (repeatChoiceIdx T j t) := by
  erw [repeatRandomSeed_apply]
  congr 1
  apply Fin.ext
  change 2 + (t.val + (2 * T + 2) * j.val) =
    2 + j.val * (2 * T + 2) + t.val
  rw [Nat.mul_comm (2 * T + 2) j.val]
  omega

end NTM

end Complexity
