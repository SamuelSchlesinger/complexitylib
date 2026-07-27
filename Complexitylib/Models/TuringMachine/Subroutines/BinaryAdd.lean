/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd.Internal

/-!
# Canonical binary addition

This module exposes binary addition assembled from the canonical count-up
loop and binary successor. Three pairwise-distinct work tapes hold a preserved
source, an updated destination, and scratch counter. The scratch tape starts
at canonical zero and is restored literally after the addition.

The endpoint is a full frame equality: only the destination tape changes,
from `dstValue` to `dstValue + srcValue`. The all-prefix space theorem is
width-based rather than derived from total loop runtime.

## Main results

- `binaryAddLoopTM_reachesIn_frame` gives the exact loop runtime and endpoint.
- `binaryAddIntoTM_hoareTime_frame` restores scratch zero with a full frame.
- `binaryAddIntoTM_hoareTimeSpace_frame` adds an all-prefix space bound.
- `binaryAddIntoTM_isTransducer` proves append-only-output safety.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- The addition loop has an exact runtime and literal endpoint. It preserves
the source and external frame, increments the destination by `srcValue`, and
leaves the scratch counter equal to `srcValue`. -/
theorem binaryAddLoopTM_reachesIn_frame
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddLoopTM srcIdx dstIdx counterIdx).reachesIn
      (binaryAddLoopTime srcValue dstValue)
      { state := (binaryAddLoopTM srcIdx dstIdx counterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (binaryAddLoopTM srcIdx dstIdx counterIdx).qhalt
        input := inp₀
        work := Function.update
          (Function.update work₀ dstIdx
            ((Tape.init ((dstValue + srcValue).bits.map Γ.ofBool)).move
              Dir3.right))
          counterIdx
            ((Tape.init (srcValue.bits.map Γ.ofBool)).move Dir3.right)
        output := out₀ } :=
  binaryAddLoopTM_reachesIn_frame_internal srcIdx dstIdx counterIdx hsrcDst
    hsrcCounter hdstCounter srcValue dstValue inp₀ work₀ out₀ hsrc hdst
    hcounter hinp hother hout

/-- Addition changes only the destination tape, from `dstValue` to
`dstValue + srcValue`. In particular, source, scratch zero, input, output,
and every unrelated work tape are restored literally. -/
theorem binaryAddIntoTM_hoareTime_frame
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddIntoTM srcIdx dstIdx counterIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx
          ((Tape.init ((dstValue + srcValue).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (binaryAddTime srcValue dstValue) :=
  binaryAddIntoTM_hoareTime_frame_internal srcIdx dstIdx counterIdx hsrcDst
    hsrcCounter hdstCounter srcValue dstValue inp₀ work₀ out₀ hsrc hdst
    hcounter hinp hother hout

/-- Time-and-space form of `binaryAddIntoTM_hoareTime_frame`. Every reachable
configuration stays within `binaryAddSpace`; the bound depends on the source
and final-destination binary widths, not on the total iteration count. -/
theorem binaryAddIntoTM_hoareTimeSpace_frame
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryAddIntoTM srcIdx dstIdx counterIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx
          ((Tape.init ((dstValue + srcValue).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (binaryAddTime srcValue dstValue) inputLength
      (binaryAddSpace initialSpace srcValue dstValue) :=
  binaryAddIntoTM_hoareTimeSpace_frame_internal srcIdx dstIdx counterIdx
    hsrcDst hsrcCounter hdstCounter srcValue dstValue inputLength initialSpace
    inp₀ work₀ out₀ hsrc hdst hcounter hinp hother hout hworkSpace
    hinputSpace

/-- Binary addition never moves its output head left. -/
theorem binaryAddIntoTM_isTransducer
    (srcIdx dstIdx counterIdx : Fin n) :
    (binaryAddIntoTM srcIdx dstIdx counterIdx).IsTransducer :=
  binaryAddIntoTM_isTransducer_internal srcIdx dstIdx counterIdx

end TM

end Complexity
