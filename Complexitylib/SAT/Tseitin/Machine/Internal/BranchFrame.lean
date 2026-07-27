/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Internal.FrontEndSpec

/-!
# Shared branch frame for the Tseitin reduction machine

After validation, both branches of `reductionTMWith` receive the same tape
frame.  This module records that frame once: the scanned input, initialized
work registers, validator verdict, tape well-formedness, and the standard
`ifTM` transition into the selected branch.

## Main results

- `validatedInputTape`
- `validationBranchPre`
- `validEmitterPre`
- `validationFramedPost_allTapesWF_internal`
- `validationFramedPost_to_branchPre_internal`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- Input tape after the validation scan reaches the first trailing blank. -/
def validatedInputTape (z : List Bool) : Tape :=
  ⟨z.length + 1, (Tape.init (z.map Γ.ofBool)).cells⟩

/-- The common frame received by either branch after `ifTM` has rewound the
validator output head to cell one. -/
def validationBranchPre (z : List Bool) : TapePred workTapeCount :=
  fun inp work out =>
    inp = validatedInputTape z ∧ work = frontEndWork z ∧
      out.head = 1 ∧ out.cells 0 = Γ.start ∧
      (∃ verdict : Bool, out.cells 1 = Γ.ofBool verdict) ∧
      ∀ j, 2 ≤ j → out.cells j = Γ.blank

/-- The exact tape frame handed to a valid-input emitter after the verdict is
cleared and the source is rewound to cell one. -/
def validEmitterPre (z : List Bool) : TapePred workTapeCount :=
  TM.EmitPred ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩ (frontEndWork z) []

/-- The scanned source input is parked. -/
theorem validatedInputTape_parked (z : List Bool) :
    TM.Parked (validatedInputTape z) := by
  refine ⟨by simp [validatedInputTape], ?_⟩
  intro j hj
  exact (TM.parked_init_input z).2 j hj

/-- Every initialized work register retains the left-end marker at cell zero. -/
theorem frontEndWork_cell_zero (z : List Bool) (i : Fin workTapeCount) :
    (frontEndWork z i).cells 0 = Γ.start := by
  by_cases hi : i = freshReg
  · subst i
    rw [frontEndWork, Function.update_self]
    exact (TM.reg_regT (z.length + 1)).cell0
  · rw [frontEndWork, Function.update_of_ne hi]
    exact (TM.reg_regT 0).cell0

/-- The framed front-end postcondition supplies the tape well-formedness
premise required by `ifTM`. -/
theorem validationFramedPost_allTapesWF_internal (z : List Bool)
    {inp out : Tape} {work : Fin workTapeCount → Tape}
    (h : validationFramedPost z (frontEndWork z) inp work out) :
    TM.AllTapesWF inp work out := by
  rcases h with ⟨hinCells, hinHead, hwork, houtHead, houtZero, houtOne,
    houtBlank⟩
  refine ⟨?_, ?_, ?_, ?_, houtZero, ?_⟩
  · rw [hinCells]
    rfl
  · intro j hj
    rw [hinCells]
    exact Tape.init_ofBool_cells_ne_start z j hj
  · intro i
    rw [hwork]
    exact frontEndWork_cell_zero z i
  · intro i j hj
    rw [hwork]
    exact (frontEndWork_parked z i).2 j hj
  · intro j hj
    by_cases hjOne : j = 1
    · subst j
      rw [houtOne]
      exact Γ.ofBool_ne_start _
    · rw [houtBlank j (by omega)]
      decide

/-- The standard `ifTM` phase transition turns the framed validation result
into the common branch frame. -/
theorem validationFramedPost_to_branchPre_internal (z : List Bool)
    {inp out : Tape} {work : Fin workTapeCount → Tape}
    (h : validationFramedPost z (frontEndWork z) inp work out) :
    validationBranchPre z (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) ⟨1, out.cells⟩ := by
  rcases h with ⟨hinCells, hinHead, hwork, houtHead, houtZero, houtOne,
    houtBlank⟩
  have hinpEq : inp = validatedInputTape z := by
    exact Tape.ext hinHead hinCells
  have hinpTransition : TM.transitionInput inp = validatedInputTape z := by
    rw [hinpEq]
    exact (validatedInputTape_parked z).transitionInput_eq_self
  have hworkTransition :
      (fun i => TM.transitionTape (work i)) = frontEndWork z := by
    funext i
    rw [hwork]
    exact (frontEndWork_parked z i).transitionTape_eq_self
  exact ⟨hinpTransition, hworkTransition, rfl, houtZero,
    ⟨validEncoding z, houtOne⟩, houtBlank⟩

end Machine

end ThreeSAT

end SAT

end Complexity
