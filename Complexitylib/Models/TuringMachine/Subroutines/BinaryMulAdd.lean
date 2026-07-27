/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd.Internal

/-!
# Canonical binary multiply-add

This module exposes a nested repeated-addition machine over five
pairwise-distinct canonical binary work tapes. It preserves both operands,
updates only the accumulator, and restores both private counters to canonical
zero. The resource contract gives a width-based all-prefix space bound.

## Main results

- `binaryMulAddIntoTM_hoareTime_frame` gives the literal endpoint and time bound.
- `binaryMulAddIntoTM_hoareTimeSpace_frame` adds the all-prefix space bound.
- `binaryMulAddIntoTM_isTransducer` proves append-only-output safety.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Multiply-add changes only the accumulator, from `accValue` to
`accValue + leftValue * rightValue`; both operands and both zero counters are
restored literally. -/
theorem binaryMulAddIntoTM_hoareTime_frame
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hacc : (work₀ accIdx).HasBinaryNat accValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ accIdx
            ((Tape.init
              ((accValue + leftValue * rightValue).bits.map Γ.ofBool)).move
                Dir3.right) ∧
          out = out₀)
        (binaryMulAddTime leftValue rightValue accValue) :=
  binaryMulAddIntoTM_hoareTime_frame_internal leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue rightValue accValue inp₀
    work₀ out₀ hleft hright hacc hmulCounter haddCounter hinp hother hout

/-- Time-and-space multiply-add contract. Every reachable configuration stays
within the stated width-based bound. -/
theorem binaryMulAddIntoTM_hoareTimeSpace_frame
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx)
    (leftValue rightValue accValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hleft : (work₀ leftIdx).HasBinaryNat leftValue)
    (hright : (work₀ rightIdx).HasBinaryNat rightValue)
    (hacc : (work₀ accIdx).HasBinaryNat accValue)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ leftIdx → i ≠ rightIdx → i ≠ accIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ accIdx
            ((Tape.init
              ((accValue + leftValue * rightValue).bits.map Γ.ofBool)).move
                Dir3.right) ∧
          out = out₀)
        (binaryMulAddTime leftValue rightValue accValue) inputLength
        (binaryMulAddSpace initialSpace leftValue rightValue accValue) :=
  binaryMulAddIntoTM_hoareTimeSpace_frame_internal leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx hdistinct leftValue rightValue accValue
    inputLength initialSpace inp₀ work₀ out₀ hleft hright hacc hmulCounter
    haddCounter hinp hother hout hworkSpace hinputSpace

/-- Binary multiply-add never moves its output head left. -/
theorem binaryMulAddIntoTM_isTransducer
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) :
    (binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx).IsTransducer :=
  binaryMulAddIntoTM_isTransducer_internal leftIdx rightIdx accIdx
    mulCounterIdx addCounterIdx

end TM

end Complexity
