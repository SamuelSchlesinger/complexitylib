/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Polynomial.Defs

/-!
# Fixed transition-schedule size polynomials -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

private theorem eval_list_sum (polynomials : List (Polynomial ℕ)) (T : ℕ) :
    polynomials.sum.eval T = (polynomials.map fun p => p.eval T).sum := by
  induction polynomials with
  | nil => simp
  | cons polynomial polynomials ih => simp [ih]

@[simp] theorem readSchedulePolynomial_eval_internal (T : ℕ) :
    readSchedulePolynomial.eval T = caseReadSize T := by
  simp [readSchedulePolynomial, caseReadSize]

@[simp] theorem caseSchedulePolynomial_eval_internal
    (workCount T : ℕ) (choiceValue : Bool) :
    (caseSchedulePolynomial workCount choiceValue).eval T =
      caseFormulaScheduleSize workCount T choiceValue := by
  simp [caseSchedulePolynomial, caseFormulaScheduleSize,
    caseFormulaMembersSize, readSchedulePolynomial_eval_internal]
  omega

@[simp] theorem effectCasePolynomial_eval_internal
    (workCount T : ℕ) (selected choiceValue : Bool) :
    (effectCasePolynomial workCount selected choiceValue).eval T =
      effectFormulaCaseSize workCount T selected choiceValue := by
  cases selected <;>
    simp [effectCasePolynomial, effectFormulaCaseSize]

@[simp] theorem effectSchedulePolynomial_eval_internal
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    (effectSchedulePolynomial caseCount workCount selectedAt choiceAt).eval T =
      effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt := by
  rw [effectSchedulePolynomial, Polynomial.eval_add, eval_list_sum]
  simp only [List.map_map, Polynomial.eval_C, effectFormulaScheduleSize]
  rw [prefixSize_eq_sum_range]
  have hmap :
      List.map
          ((fun p : Polynomial ℕ => p.eval T) ∘ fun caseIndex =>
            effectCasePolynomial workCount (selectedAt caseIndex)
              (choiceAt caseIndex))
          (List.range caseCount) =
        List.map
          (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
          (List.range caseCount) := by
    apply List.map_congr_left
    intro caseIndex hcaseIndex
    simp only [Function.comp_apply, effectCasePolynomial_eval_internal,
      effectFormulaSizeAt]
    rw [ite_eq_left (List.mem_range.mp hcaseIndex)]
  rw [hmap]
  omega

@[simp] theorem predecessorHeadSchedulePolynomial_eval_internal (T : ℕ) :
    predecessorHeadSchedulePolynomial.eval T = movedHeadPredecessorSize T := by
  simp [predecessorHeadSchedulePolynomial, movedHeadPredecessorSize]

@[simp] theorem movedHeadMemberPolynomial_eval_internal
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    (movedHeadMemberPolynomial caseCount workCount selectedAt choiceAt).eval T =
      effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt +
        movedHeadPredecessorSize T + 1 := by
  simp [movedHeadMemberPolynomial]

@[simp] theorem movedHeadSchedulePolynomial_eval_internal
    (caseCount workCount T : ℕ) (selectedAt : ℕ → ℕ → Bool)
    (choiceAt : ℕ → Bool) :
    (movedHeadSchedulePolynomial caseCount workCount selectedAt choiceAt).eval T =
      movedHeadFormulaScheduleSize caseCount workCount T selectedAt choiceAt := by
  rw [movedHeadSchedulePolynomial, Polynomial.eval_add, eval_list_sum]
  simp only [List.map_map, Polynomial.eval_C, movedHeadFormulaScheduleSize]
  rw [prefixSize_eq_sum_range]
  have hmap :
      List.map
          ((fun p : Polynomial ℕ => p.eval T) ∘ fun directionCode =>
            movedHeadMemberPolynomial caseCount workCount
              (selectedAt directionCode) choiceAt)
          (List.range movedHeadDirectionCount) =
        List.map
          (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
          (List.range movedHeadDirectionCount) := by
    apply List.map_congr_left
    intro directionCode hdirection
    have hdirectionLt : directionCode < movedHeadDirectionCount :=
      List.mem_range.mp hdirection
    simp [Function.comp_apply, movedHeadMemberSizeAt, movedHeadEffectSizeAt,
      hdirectionLt]
  rw [hmap]
  omega

@[simp] theorem writtenCellSchedulePolynomial_eval_internal
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    (writtenCellSchedulePolynomial caseCount workCount selectedAt choiceAt).eval T =
      writtenCellScheduleSize caseCount workCount T selectedAt choiceAt := by
  simp [writtenCellSchedulePolynomial, writtenCellScheduleSize,
    writtenCellEffectSize]

@[simp] theorem nextSchedulePolynomial_eval_internal
    (caseCount workCount T atomKind : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    (nextSchedulePolynomial caseCount workCount atomKind selectedAt
        choiceAt).eval T =
      nextFormulaScheduleSize caseCount workCount T atomKind selectedAt
        choiceAt := by
  simp only [nextSchedulePolynomial, nextFormulaScheduleSize]
  split <;> rename_i hstate
  · simp [nextStateFormulaScheduleSize, nextHaltedOrScheduleSize]
  · split <;> rename_i hhead
    · simp [nextHeadFormulaScheduleSize, nextHaltedOrScheduleSize]
    · split <;> rename_i hwritten
      · simp [nextWrittenCellFormulaScheduleSize,
          nextHaltedOrScheduleSize]
      · simp [nextCellCopyScheduleSize]

end Serializer

end CircuitUnrolling

end Complexity
