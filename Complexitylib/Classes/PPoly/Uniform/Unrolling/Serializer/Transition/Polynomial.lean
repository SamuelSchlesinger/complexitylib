/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Polynomial.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Polynomial.Internal

/-!
# Fixed transition-schedule size polynomials

This module exposes literal evaluation theorems for the fixed polynomials that
measure nested transition schedules as functions of the tableau horizon.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem readSchedulePolynomial_eval (T : ℕ) :
    readSchedulePolynomial.eval T = caseReadSize T :=
  readSchedulePolynomial_eval_internal T

theorem caseSchedulePolynomial_eval
    (workCount T : ℕ) (choiceValue : Bool) :
    (caseSchedulePolynomial workCount choiceValue).eval T =
      caseFormulaScheduleSize workCount T choiceValue :=
  caseSchedulePolynomial_eval_internal workCount T choiceValue

theorem effectCasePolynomial_eval
    (workCount T : ℕ) (selected choiceValue : Bool) :
    (effectCasePolynomial workCount selected choiceValue).eval T =
      effectFormulaCaseSize workCount T selected choiceValue :=
  effectCasePolynomial_eval_internal workCount T selected choiceValue

theorem effectSchedulePolynomial_eval
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    (effectSchedulePolynomial caseCount workCount selectedAt choiceAt).eval T =
      effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt :=
  effectSchedulePolynomial_eval_internal caseCount workCount T selectedAt
    choiceAt

theorem predecessorHeadSchedulePolynomial_eval (T : ℕ) :
    predecessorHeadSchedulePolynomial.eval T = movedHeadPredecessorSize T :=
  predecessorHeadSchedulePolynomial_eval_internal T

theorem movedHeadMemberPolynomial_eval
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    (movedHeadMemberPolynomial caseCount workCount selectedAt choiceAt).eval T =
      effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt +
        movedHeadPredecessorSize T + 1 :=
  movedHeadMemberPolynomial_eval_internal caseCount workCount T selectedAt
    choiceAt

theorem movedHeadSchedulePolynomial_eval
    (caseCount workCount T : ℕ) (selectedAt : ℕ → ℕ → Bool)
    (choiceAt : ℕ → Bool) :
    (movedHeadSchedulePolynomial caseCount workCount selectedAt choiceAt).eval T =
      movedHeadFormulaScheduleSize caseCount workCount T selectedAt choiceAt :=
  movedHeadSchedulePolynomial_eval_internal caseCount workCount T selectedAt
    choiceAt

theorem writtenCellSchedulePolynomial_eval
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    (writtenCellSchedulePolynomial caseCount workCount selectedAt choiceAt).eval T =
      writtenCellScheduleSize caseCount workCount T selectedAt choiceAt :=
  writtenCellSchedulePolynomial_eval_internal caseCount workCount T selectedAt
    choiceAt

theorem nextSchedulePolynomial_eval
    (caseCount workCount T atomKind : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    (nextSchedulePolynomial caseCount workCount atomKind selectedAt
        choiceAt).eval T =
      nextFormulaScheduleSize caseCount workCount T atomKind selectedAt
        choiceAt :=
  nextSchedulePolynomial_eval_internal caseCount workCount T atomKind
    selectedAt choiceAt

end Serializer

end CircuitUnrolling

end Complexity
