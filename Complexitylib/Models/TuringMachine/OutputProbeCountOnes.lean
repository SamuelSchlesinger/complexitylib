/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes.Defs
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes.Internal

/-!
# Counting one bits through dynamically indexed output probes

This module certifies the Boolean continuations used by an occupancy-counting
scan. Both branches start with the physical query latch reset to zero. The
zero branch preserves the complete controller frame; the one branch increments
one canonical binary count register and updates only that register.
-/

namespace Complexity

namespace TM

/-- Extending a valid prefix by one position adds exactly the queried bit to
the running one count. -/
theorem outputProbePrefixOnes_succ (bits : List Bool)
    (address : ℕ) (haddress : address < bits.length) :
    outputProbePrefixOnes bits (address + 1) =
      outputProbePrefixOnes bits address +
        if bits[address]'haddress then 1 else 0 :=
  outputProbePrefixOnes_succ_internal bits address haddress

/-- Taking the full prefix recovers the total number of true bits. -/
theorem outputProbePrefixOnes_all (bits : List Bool) :
    outputProbePrefixOnes bits bits.length = bits.count true :=
  outputProbePrefixOnes_all_internal bits

/-- Controller registers other than the address and count retain their base
outer-frame tapes throughout the prefix-count invariant. -/
theorem outputProbeCountOnesOuterExtrasAt_other
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx idx : Fin controllerTapes}
    (haddress : idx ≠ addressIdx) (hcount : idx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) :
    outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
        address (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) :=
  outputProbeCountOnesOuterExtrasAt_other_internal n haddress hcount
    outerExtras bits address

/-- Updating the canonical address and prefix-count registers preserves a
parked outer controller frame. -/
theorem outputProbeCountOnesOuterExtrasAt_parked
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (bits : List Bool) (address : ℕ) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx
        outerExtras bits address i) :=
  outputProbeCountOnesOuterExtrasAt_parked_internal n outerExtras houter bits
    address

/-- The canonical count-ones frame realizes its exact restored latch and
prefix-count tape predicate. -/
theorem outputProbeCountOnesFrameCfg_post
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (address : ℕ) :
    outputProbeLatchFramePost tm controllerTapes
      (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
        address)
      input output extras false
      (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
        outerExtras bits input output extras address).input
      (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
        outerExtras bits input output extras address).work
      (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
        outerExtras bits input output extras address).output :=
  outputProbeCountOnesFrameCfg_post_internal tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras address

/-- The halted canonical scan frame exposes the exact one count of the
processed prefix in the designated count register. -/
theorem outputProbeCountOnesDoneCfg_count
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (limitValue : ℕ) :
    ((outputProbeCountOnesDoneCfg tm controllerTapes addressIdx scratchIdx
      limitIdx countIdx outerExtras bits input output extras limitValue).work
      (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        (outputProbePrefixOnes bits limitValue) :=
  outputProbeCountOnesDoneCfg_count_internal tm controllerTapes addressIdx
    scratchIdx limitIdx countIdx outerExtras bits input output extras
    limitValue

/-- The canonical scan frame stores the running prefix count in the designated
controller register. -/
theorem outputProbeCountOnesOuterExtrasAt_count
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) :
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address
      (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        (outputProbePrefixOnes bits address) :=
  outputProbeCountOnesOuterExtrasAt_count_internal n outerExtras bits address

/-- The canonical scan frame stores the current address in the designated
controller register. -/
theorem outputProbeCountOnesOuterExtrasAt_address
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (hne : addressIdx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) :
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address
      (outputProbeIndexedControllerIdx n addressIdx)).HasBinaryNat address :=
  outputProbeCountOnesOuterExtrasAt_address_internal n hne outerExtras bits
    address

/-- Conditional count dispatch updates the outer frame to the next prefix
count while leaving the current address unchanged. -/
theorem outputProbeCountOnesOuterExtrasAfter_eq
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) (haddress : address < bits.length) :
    outputProbeCountOnesOuterExtrasAfter n countIdx
        (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras
          bits address)
        (outputProbePrefixOnes bits address) (bits[address]'haddress) =
      Function.update
        (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras
          bits address)
        (outputProbeIndexedControllerIdx n countIdx)
        (outputProbeCounterTape (outputProbePrefixOnes bits (address + 1))) :=
  outputProbeCountOnesOuterExtrasAfter_eq_internal n outerExtras bits address
    haddress

/-- After count dispatch and the loop's address successor, the complete outer
frame is exactly the canonical next-prefix frame. -/
theorem outputProbeCountOnesOuterExtrasAt_succ
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (hne : addressIdx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) (haddress : address < bits.length) :
    Function.update
        (outputProbeCountOnesOuterExtrasAfter n countIdx
          (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras
            bits address)
          (outputProbePrefixOnes bits address) (bits[address]'haddress))
        (outputProbeIndexedControllerIdx n addressIdx)
        (outputProbeCounterTape (address + 1)) =
      outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
        (address + 1) :=
  outputProbeCountOnesOuterExtrasAt_succ_internal n hne outerExtras bits
    address haddress

/-- Package bounded composite-iteration witnesses into a count-ones scan
certificate whose configurations expose the exact prefix-count invariant.

The comparison, loopback, and final equality phases are discharged here;
clients only provide the source-dependent query/count iterations. -/
noncomputable def outputProbeCountOnesSegmentSpecOfIterationWitnesses
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (haddressLimit : addressIdx ≠ limitIdx)
    (haddressCount : addressIdx ≠ countIdx)
    (hcountLimit : countIdx ≠ limitIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (bodyTime : ℕ → ℕ) (startValue limitValue : ℕ)
    (hlimit :
      (outerExtras (outputProbeIndexedControllerIdx n limitIdx)).HasBinaryNat
        limitValue)
    (iterationWitness : ∀ value, startValue ≤ value → value < limitValue →
      ∃ time, time ≤ binaryForIterationTime bodyTime value ∧
        (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx
          limitIdx countIdx).reachesIn time
          (outputProbeCountOnesIterationStartCfg tm controllerTapes addressIdx
            scratchIdx limitIdx countIdx outerExtras bits input output extras
            value)
          (outputProbeCountOnesIterationDoneCfg tm controllerTapes addressIdx
            scratchIdx limitIdx countIdx outerExtras bits input output extras
            value)) :
    BinaryForSegmentSpec
      (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
        countIdx)
      (outputProbeIndexedControllerIdx n addressIdx)
      (outputProbeIndexedControllerIdx n limitIdx)
      bodyTime startValue limitValue :=
  outputProbeCountOnesSegmentSpecOfIterationWitnessesInternal tm
    controllerTapes addressIdx scratchIdx limitIdx countIdx haddressLimit
    haddressCount hcountLimit outerExtras bits input output extras hextras
    houter houtput bodyTime startValue limitValue hlimit iterationWitness

/-- Build the same exact prefix-count scan certificate from bounded Hoare
witnesses for the query/count body.

This constructor closes the body-to-successor seam and leaves clients only
the source-specific task of supplying each valid-address body contract. -/
noncomputable def outputProbeCountOnesSegmentSpecOfBodyWitnesses
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (haddressLimit : addressIdx ≠ limitIdx)
    (haddressCount : addressIdx ≠ countIdx)
    (hcountLimit : countIdx ≠ limitIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (bodyTime : ℕ → ℕ) (startValue limitValue : ℕ)
    (hlimitBits : limitValue ≤ bits.length)
    (hlimit :
      (outerExtras (outputProbeIndexedControllerIdx n limitIdx)).HasBinaryNat
        limitValue)
    (bodyWitness : ∀ value, startValue ≤ value → value < limitValue →
      (hvalueBits : value < bits.length) →
      ∃ (bodyBound : ℕ)
        (pre : TapePred
          (0 + outputProbeControllerTapes n + controllerTapes)),
        bodyBound ≤ bodyTime value ∧
        pre
          (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
            outerExtras bits input output extras value).input
          (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
            outerExtras bits input output extras value).work
          (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
            outerExtras bits input output extras value).output ∧
        (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
          countIdx).HoareTime pre
            (outputProbeLatchFramePost tm controllerTapes
              (outputProbeCountOnesOuterExtrasAfter n countIdx
                (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx
                  outerExtras bits value)
                (outputProbePrefixOnes bits value) (bits[value]'hvalueBits))
              input output extras false)
            bodyBound) :
    BinaryForSegmentSpec
      (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
        countIdx)
      (outputProbeIndexedControllerIdx n addressIdx)
      (outputProbeIndexedControllerIdx n limitIdx)
      bodyTime startValue limitValue :=
  outputProbeCountOnesSegmentSpecOfBodyWitnessesInternal tm
    controllerTapes addressIdx scratchIdx limitIdx countIdx haddressLimit
    haddressCount hcountLimit outerExtras bits input output extras hextras
    houter houtput bodyTime startValue limitValue hlimitBits hlimit bodyWitness

/-- The zero continuation preserves the complete reset-latch controller frame. -/
theorem outputProbeCountOnes_zero_hoareTimeSpace
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (countIdx : Fin controllerTapes) (count inputLength initialSpace : ℕ)
    (hinitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).Q).WithinAuxSpace inputLength initialSpace) :
    (skipTM (n := 0 + outputProbeControllerTapes n +
      controllerTapes)).HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
          false)
        input output extras false)
      1 inputLength (initialSpace + 1) :=
  outputProbeCountOnes_zero_hoareTimeSpace_internal tm controllerTapes
    outerExtras input output extras hextras houter houtput countIdx count
    inputLength initialSpace hinitial

/-- The one continuation increments exactly the designated canonical binary
count and preserves every other tape in the reset-latch controller frame. -/
theorem outputProbeCountOnes_one_hoareTimeSpace
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (countIdx : Fin controllerTapes) (count inputLength initialSpace : ℕ)
    (hcount :
      (outerExtras (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        count)
    (hinitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).Q).WithinAuxSpace
            inputLength initialSpace) :
    (binarySuccTM
      (outputProbeIndexedControllerIdx n countIdx)).HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count true)
        input output extras false)
      (binarySuccTime count) inputLength
      (initialSpace + binarySuccTime count) :=
  outputProbeCountOnes_one_hoareTimeSpace_internal tm controllerTapes
    outerExtras input output extras hextras houter houtput countIdx count
    inputLength initialSpace hcount hinitial

/-- A certified dynamic latch phase composes with reset-and-count dispatch.
The resulting body preserves the reset latch and updates only the count frame
when the queried bit is true. -/
theorem outputProbeCountOnesBodyTM_of_latch_hoareTimeSpace
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (count : ℕ)
    (hcount :
      (outerExtras (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        count)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {latchTime latchSpace inputLength clearInitialSpace zeroInitialSpace
      oneInitialSpace : ℕ}
    (hlatch : (outputProbeIndexedLatchTM tm controllerTapes addressIdx
      scratchIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit)
        latchTime inputLength latchSpace)
    (hclearInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
        ({ state :=
              (clearWorkTM
                (outputProbeLatchIdx n controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).Q).WithinAuxSpace
            inputLength clearInitialSpace)
    (hzeroInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).Q).WithinAuxSpace inputLength
            zeroInitialSpace)
    (honeInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).Q).WithinAuxSpace
            inputLength oneInitialSpace) :
    (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
      countIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            bit)
          input output extras false)
        (latchTime + 1 +
          outputProbeLatchDispatchTime bit 1
            (clearWorkTimeBound 1 + 1 + binarySuccTime count))
        inputLength
        (max latchSpace
          (if bit then
            max (clearInitialSpace + clearWorkTimeBound 1)
              (oneInitialSpace + binarySuccTime count)
          else zeroInitialSpace + 1)) :=
  outputProbeCountOnesBodyTM_of_latch_hoareTimeSpace_internal tm
    controllerTapes addressIdx scratchIdx countIdx outerExtras input output
    extras bit hextras houter houtput count hcount hlatch hclearInitial
    hzeroInitial honeInitial

/-- Build one exact query/reset/count body contract directly from a
space-bounded source transducer and a canonical restored latch frame.

All finite head maxima needed by the lower-level space contracts are chosen
internally. The caller supplies only the stable cleanup/controller invariants
and the cleanup limit needed for this query address. -/
theorem ComputesInSpace.outputProbeCountOnesBodyTM_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (address : ℕ) (haddress : address < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (address + 1) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (addressIdx scratchIdx countIdx : Fin controllerTapes)
    (haddressScratch : addressIdx ≠ scratchIdx)
    (hsource :
      (outerExtras (outputProbeIndexedControllerIdx n addressIdx))
        |>.HasBinaryNat address)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0)
    (count : ℕ)
    (hcount :
      (outerExtras (outputProbeIndexedControllerIdx n countIdx))
        |>.HasBinaryNat count) :
    ∃ (bodyBound : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
        countIdx).HoareTime pre
          (outputProbeLatchFramePost tm controllerTapes
            (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
              ((f input)[address]'haddress))
            input output extras false)
          bodyBound :=
  hcomp.outputProbeCountOnesBodyTM_hoareTime_internal input address haddress
    output houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit
    hlimit controllerTapes outerExtras houter addressIdx scratchIdx countIdx
    haddressScratch hsource hscratch count hcount

/-- Derive a complete exact-prefix count scan from the source transducer's
`ComputesInSpace` contract.

Per-address runtimes are selected noncomputably from the deterministic source
runs. The returned segment certificate fixes every comparison, iteration, and
halted frame; no caller-supplied latch or body witnesses remain. -/
noncomputable def ComputesInSpace.outputProbeCountOnesSegmentSpec
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (haddressLimit : addressIdx ≠ limitIdx)
    (haddressCount : addressIdx ≠ countIdx)
    (hcountLimit : countIdx ≠ limitIdx)
    (haddressScratch : addressIdx ≠ scratchIdx)
    (hscratchAddress : scratchIdx ≠ addressIdx)
    (hscratchCount : scratchIdx ≠ countIdx)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0)
    (startValue limitValue : ℕ)
    (hlimitBits : limitValue ≤ (f input).length)
    (hlimitRegister :
      (outerExtras (outputProbeIndexedControllerIdx n limitIdx))
        |>.HasBinaryNat limitValue)
    (hqueryLimit : ∀ value, startValue ≤ value → value < limitValue →
      outputProbeCaptureSpace (max 1 (space input.length)) (value + 1) ≤
        cleanupLimit) :
    Σ bodyTime : ℕ → ℕ,
      BinaryForSegmentSpec
        (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
          countIdx)
        (outputProbeIndexedControllerIdx n addressIdx)
        (outputProbeIndexedControllerIdx n limitIdx)
        bodyTime startValue limitValue :=
  hcomp.outputProbeCountOnesSegmentSpecInternal input output houtput extras
    hextras hcleanupCounter cleanupLimit hcleanupLimit controllerTapes
    outerExtras houter addressIdx scratchIdx limitIdx countIdx haddressLimit
    haddressCount hcountLimit haddressScratch hscratchAddress hscratchCount
    hscratch startValue limitValue hlimitBits hlimitRegister hqueryLimit

/-- Counting queried one bits preserves one-way output safety. -/
theorem outputProbeCountOnesTM_isTransducer
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes) :
    (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx limitIdx
      countIdx).IsTransducer :=
  IsTransducer.outputProbeCountOnesTM_internal

end TM

end Complexity
