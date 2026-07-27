/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Internal.Setup
public import Complexitylib.SAT.Tseitin.Machine.Internal.ValidationFramed

/-!
# Hoare specification for the Tseitin reduction front end

`reductionFrontEndTM` first initializes the fresh-variable register to one
more than the source bit length and then validates the source encoding.  This
module composes the two framed contracts.  The sequence boundary is an exact
no-op on the parked input, unary registers, and empty output accumulator.

The resulting postcondition records all state needed by the branch assembly:

- the input head is on the first trailing blank at `|z| + 1`;
- `freshReg` contains `|z| + 1` and every other work register is zero;
- all work registers are preserved by validation; and
- output cell one contains `validEncoding z`, with the output head at one and
  a blank tail.

## Main results

- `reductionFrontEndTM_hoareTime_internal` -- structural bound `5|z| + 13`
- `reductionFrontEndTM_linear_hoareTime_internal` -- rounded bound
  `13(|z| + 1)`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- Work-register family established by `seedFreshTM`: the fresh register
contains the source bit length plus one and the remaining five registers are
zero. -/
def frontEndWork (z : List Bool) : Fin workTapeCount → Tape :=
  Function.update (fun _ => TM.regTape 0) freshReg
    (TM.regTape (z.length + 1))

/-- Every initialized front-end register is parked. -/
theorem frontEndWork_parked (z : List Bool) :
    ∀ i, TM.Parked (frontEndWork z i) := by
  intro i
  by_cases hi : i = freshReg
  · subst i
    rw [frontEndWork, Function.update_self]
    exact TM.parked_regTape (z.length + 1)
  · rw [frontEndWork, Function.update_of_ne hi]
    exact TM.parked_regTape 0

/-- The structural front-end budget is bounded by a convenient linear
polynomial with one coefficient. -/
theorem reductionFrontEndTime_le_linear_internal (n : ℕ) :
    5 * n + 13 ≤ 13 * (n + 1) := by
  omega

/-- **Framed front-end execution.**  Starting from the ordinary initial tape
layout, initialize all six registers and validate `z`.  Validation preserves
the initialized register family exactly and leaves its Boolean verdict at
output cell one. -/
theorem reductionFrontEndTM_hoareTime_internal (z : List Bool) :
    reductionFrontEndTM.HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
          (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (validationFramedPost z (frontEndWork z))
      (5 * z.length + 13) := by
  let inp₁ : Tape := ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
  have hinp₁ : TM.Parked inp₁ := by
    simpa only [inp₁] using TM.parked_init_input z
  have hseed := seedFreshTM_hoareTime_internal z
  have hvalidation :=
    validationTM_started_framed_hoareTime_internal z (frontEndWork z)
      (frontEndWork_parked z)
  have htransition : ∀ inp work out,
      TM.EmitPred inp₁ (frontEndWork z) [] inp work out →
        TM.EmitPred inp₁ (frontEndWork z) []
          (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) :=
    TM.emitPred_transition hinp₁ (frontEndWork_parked z) []
  have hfront := TM.seqTM_hoareTime seedFreshTM validationTM
    (by simpa only [inp₁, frontEndWork] using hseed)
    htransition
    (by simpa only [inp₁] using hvalidation)
  have hbound := hfront.mono_bound (by omega :
    (4 * z.length + 11) + 1 + (z.length + 1) ≤ 5 * z.length + 13)
  simpa only [reductionFrontEndTM] using hbound

/-- Rounded linear-time form of the front-end contract, ready for later
polynomial assembly. -/
theorem reductionFrontEndTM_linear_hoareTime_internal (z : List Bool) :
    reductionFrontEndTM.HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
          (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (validationFramedPost z (frontEndWork z))
      (13 * (z.length + 1)) :=
  (reductionFrontEndTM_hoareTime_internal z).mono_bound
    (reductionFrontEndTime_le_linear_internal z.length)

end Machine

end ThreeSAT

end SAT

end Complexity
