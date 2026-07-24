/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.RewindInputSpace.Internal

/-!
# Space-exact input rewind

The input rewind only moves its input head toward cell one. This focused
contract records that its peak auxiliary space is the initial budget rather
than the machine's linear rewind time.
-/

namespace Complexity

namespace TM

/-- Rewind a parked invariant input while preserving the work/output frame and
without increasing auxiliary space. -/
theorem rewindInputTM_hoareTimeSpace_frame {n : ℕ}
    (inputHeadBound inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinputInvariant : inp₀.StartInvariant) (hinput : Parked inp₀)
    (hinputHead : inp₀.head ≤ inputHeadBound)
    (hwork : ∀ i, Parked (work₀ i)) (houtput : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (rewindInputTM (n := n)).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp.head = 1 ∧ inp.cells = inp₀.cells ∧
        work = work₀ ∧ out = out₀)
      (inputHeadBound + 2) inputLength initialSpace :=
  rewindInputTM_hoareTimeSpace_frame_internal inputHeadBound inputLength
    initialSpace inp₀ work₀ out₀ hinputInvariant hinput hinputHead
    hwork houtput hworkSpace hinputSpace

/-- Rewinding the input tape never moves the output head left. -/
theorem rewindInputTM_isTransducer {n : ℕ} :
    (rewindInputTM (n := n)).IsTransducer :=
  rewindInputTM_isTransducer_internal

end TM

end Complexity
