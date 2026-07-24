/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefix.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefix.Internal

/-!
# Binary-bounded work-prefix blanking

This module exposes a reusable reset primitive for work tapes that may contain
sparse data. Given a preserved canonical binary limit and a canonical zero
scratch counter, the machine blanks every target cell from one through the
limit, rewinds the target to cell one, and restores the counter to zero.

The all-prefix contract charges the target's linear scan in the numeric limit
and only binary-width overhead for the loop controller. In the intended probe
application the limit is itself a logarithmic auxiliary-space bound.
-/

namespace Complexity

namespace TM

@[simp] theorem blankPrefixCells_zero (cells : ℕ → Γ) :
    blankPrefixCells cells 0 = cells :=
  blankPrefixCells_zero_internal cells

theorem blankPrefixCells_succ (cells : ℕ → Γ) (count : ℕ) :
    Function.update (blankPrefixCells cells count) (count + 1) Γ.blank =
      blankPrefixCells cells (count + 1) :=
  blankPrefixCells_succ_internal cells count

/-- Blanking through a complete support bound returns the literal canonical
parked blank tape. -/
theorem blankPrefixResultTape_eq_parkedBlank (tape : Tape)
    (limit : ℕ) (hinvariant : tape.StartInvariant)
    (hblank : ∀ index, limit < index → tape.cells index = Γ.blank) :
    blankPrefixResultTape tape limit =
      (Tape.init []).move Dir3.right :=
  blankPrefixResultTape_eq_parkedBlank_internal tape limit hinvariant hblank

/-- A binary-bounded prefix reset preserves the complete external frame,
changes only the selected target cells, and restores the scratch counter. -/
theorem blankWorkPrefixTM_hoareTime_frame {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (limit : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (htargetHead : (work₀ targetIdx).head = 1)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀) :
    (blankWorkPrefixTM targetIdx counterIdx limitIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ targetIdx
          (blankPrefixResultTape (work₀ targetIdx) limit) ∧
        out = out₀)
      (blankWorkPrefixTime limit) :=
  blankWorkPrefixTM_hoareTime_frame_internal targetIdx counterIdx limitIdx
    hdistinct limit inp₀ work₀ out₀ htargetInvariant htargetHead hinp
    hwork hcounter hlimit hout

/-- The complete reset contract with an honest bound for every reachable
configuration. -/
theorem blankWorkPrefixTM_hoareTimeSpace_frame {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (limit inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (htargetHead : (work₀ targetIdx).head = 1)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (blankWorkPrefixTM targetIdx counterIdx limitIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ targetIdx
          (blankPrefixResultTape (work₀ targetIdx) limit) ∧
        out = out₀)
      (blankWorkPrefixTime limit) inputLength
      (blankWorkPrefixSpace initialSpace limit) :=
  blankWorkPrefixTM_hoareTimeSpace_frame_internal targetIdx counterIdx limitIdx
    hdistinct limit inputLength initialSpace inp₀ work₀ out₀
    htargetInvariant htargetHead hinp hwork hcounter hlimit hout hworkSpace
    hinputSpace

/-- Rewind an arbitrary source-space-bounded target head before applying the
same exact sparse-prefix reset. -/
theorem rewindBlankWorkPrefixTM_hoareTimeSpace_frame {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n)
    (hdistinct : BlankWorkPrefixDistinct targetIdx counterIdx limitIdx)
    (headBound limit inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htargetInvariant : (work₀ targetIdx).StartInvariant)
    (htargetHead : (work₀ targetIdx).head ≤ headBound)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ targetIdx → Parked (work₀ i))
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat limit)
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (rewindBlankWorkPrefixTM targetIdx counterIdx limitIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ targetIdx
          (blankPrefixResultTape (work₀ targetIdx) limit) ∧
        out = out₀)
      (rewindBlankWorkPrefixTime headBound limit) inputLength
      (rewindBlankWorkPrefixSpace initialSpace headBound limit) :=
  rewindBlankWorkPrefixTM_hoareTimeSpace_frame_internal targetIdx counterIdx
    limitIdx hdistinct headBound limit inputLength initialSpace inp₀ work₀
    out₀ htargetInvariant htargetHead hinp hother hcounter hlimit hout
    hworkSpace hinputSpace

/-- Bounded-prefix blanking never moves the physical output head left. -/
theorem blankWorkPrefixTM_isTransducer {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n) :
    (blankWorkPrefixTM targetIdx counterIdx limitIdx).IsTransducer :=
  blankWorkPrefixTM_isTransducer_internal targetIdx counterIdx limitIdx

/-- Rewind-then-blank cleanup preserves one-way-output safety. -/
theorem rewindBlankWorkPrefixTM_isTransducer {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n) :
    (rewindBlankWorkPrefixTM targetIdx counterIdx limitIdx).IsTransducer :=
  rewindBlankWorkPrefixTM_isTransducer_internal targetIdx counterIdx limitIdx

end TM

end Complexity
