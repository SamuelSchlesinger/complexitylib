/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDispatch
import Complexitylib.Models.TuringMachine.OutputProbeIndexed
import Complexitylib.Models.TuringMachine.OutputProbeScan.Internal
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Counting one bits through dynamically indexed output probes -- internals
-/

namespace Complexity

namespace TM

private theorem skipTM_isTransducer_internal {n : ℕ} :
    (skipTM (n := n)).IsTransducer := by
  intro state _iHead _wHeads oHead
  cases state <;> cases oHead <;> simp [skipTM, idleDir]

private theorem outputProbeCountOnesHasBinaryNat_parked_internal
    {t : Tape} {value : ℕ} (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem outputProbeCountOnesBinarySuccCanonical_reachesIn_internal
    (idx : Fin n) (value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hvalue : (work idx).HasBinaryNat value)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binarySuccTM idx).reachesIn (binarySuccTime value)
      { state := (binarySuccTM idx).qstart
        input := inp
        work := work
        output := out }
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := Function.update work idx
          (outputProbeCounterTape (value + 1))
        output := out } := by
  obtain ⟨c', hreach, hhalt, hinput, hother, htarget, houtput⟩ :=
    binarySuccTM_reachesIn_frame idx value inp work out hvalue
      hinp.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkEq : c'.work = Function.update work idx
      (outputProbeCounterTape (value + 1)) := by
    funext i
    by_cases hi : i = idx
    · subst i
      simp only [Function.update_self]
      simpa [outputProbeCounterTape] using htarget.eq_init_move_right
    · rw [Function.update_of_ne hi, hother i hi]
  have hc' : c' =
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := Function.update work idx
          (outputProbeCounterTape (value + 1))
        output := out } :=
    Cfg.ext hhalt hinput hworkEq houtput
  simpa [hc'] using hreach

theorem outputProbePrefixOnes_succ_internal (bits : List Bool)
    (address : ℕ) (haddress : address < bits.length) :
    outputProbePrefixOnes bits (address + 1) =
      outputProbePrefixOnes bits address +
        if bits[address]'haddress then 1 else 0 := by
  rw [outputProbePrefixOnes, outputProbePrefixOnes,
    List.take_succ_eq_append_getElem haddress, List.count_append]
  by_cases hbit : bits[address]'haddress
  · simp [hbit]
  · simp [hbit]

theorem outputProbePrefixOnes_all_internal (bits : List Bool) :
    outputProbePrefixOnes bits bits.length = bits.count true := by
  simp [outputProbePrefixOnes]

theorem outputProbeCountOnesOuterExtrasAt_count_internal
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) :
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address
      (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        (outputProbePrefixOnes bits address) := by
  simp only [outputProbeCountOnesOuterExtrasAt, Function.update_self]
  exact Tape.init_move_right_hasBinaryNat _

theorem outputProbeCountOnesOuterExtrasAt_address_internal
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (hne : addressIdx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) :
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address
      (outputProbeIndexedControllerIdx n addressIdx)).HasBinaryNat
        address := by
  rw [outputProbeCountOnesOuterExtrasAt, Function.update_of_ne]
  · rw [Function.update_self]
    exact Tape.init_move_right_hasBinaryNat address
  · exact outputProbeScan_address_ne_limit_internal n hne

theorem outputProbeCountOnesOuterExtrasAt_other_internal
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx idx : Fin controllerTapes}
    (haddress : idx ≠ addressIdx) (hcount : idx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) :
    outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
        address (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  rw [outputProbeCountOnesOuterExtrasAt, Function.update_of_ne,
    Function.update_of_ne]
  · exact fun heq => haddress
      (outputProbeIndexedControllerIdx_injective_internal n heq)
  · exact fun heq => hcount
      (outputProbeIndexedControllerIdx_injective_internal n heq)

theorem outputProbeCountOnesOuterExtrasAt_parked_internal
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
        outerExtras bits address i) := by
  intro i hi
  by_cases hcount :
      i = outputProbeIndexedControllerIdx n countIdx
  · subst i
    simp only [outputProbeCountOnesOuterExtrasAt, Function.update_self]
    exact outputProbeCountOnesHasBinaryNat_parked_internal
      (Tape.init_move_right_hasBinaryNat _)
  · rw [outputProbeCountOnesOuterExtrasAt, Function.update_of_ne hcount]
    by_cases haddress :
        i = outputProbeIndexedControllerIdx n addressIdx
    · subst i
      simp only [Function.update_self]
      exact outputProbeCountOnesHasBinaryNat_parked_internal
        (Tape.init_move_right_hasBinaryNat _)
    · rw [Function.update_of_ne haddress]
      exact houter i hi

theorem outputProbeCountOnesOuterExtrasAfter_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (count : ℕ) (bit : Bool) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras
        count bit i) := by
  intro i hi
  by_cases hbit : bit
  · simp only [outputProbeCountOnesOuterExtrasAfter, hbit, if_true]
    by_cases hcount : i = outputProbeIndexedControllerIdx n countIdx
    · subst i
      simp only [Function.update_self]
      exact outputProbeCountOnesHasBinaryNat_parked_internal
        (Tape.init_move_right_hasBinaryNat _)
    · rw [Function.update_of_ne hcount]
      exact houter i hi
  · simpa [outputProbeCountOnesOuterExtrasAfter, hbit] using houter i hi

theorem outputProbeCountOnesOuterExtrasAfter_address_internal
    (n : ℕ) {controllerTapes : ℕ}
    {addressIdx countIdx : Fin controllerTapes}
    (hne : addressIdx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits : List Bool) (address : ℕ) (bit : Bool) :
    (outputProbeCountOnesOuterExtrasAfter n countIdx
      (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
        address)
      (outputProbePrefixOnes bits address) bit
      (outputProbeIndexedControllerIdx n addressIdx)).HasBinaryNat address := by
  by_cases hbit : bit
  · rw [outputProbeCountOnesOuterExtrasAfter, if_pos hbit,
      Function.update_of_ne]
    · exact outputProbeCountOnesOuterExtrasAt_address_internal n hne
        outerExtras bits address
    · exact outputProbeScan_address_ne_limit_internal n hne
  · rw [outputProbeCountOnesOuterExtrasAfter, if_neg hbit]
    exact outputProbeCountOnesOuterExtrasAt_address_internal n hne outerExtras
      bits address

theorem outputProbeCountOnesFrameCfg_post_internal
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
        outerExtras bits input output extras address).output := by
  exact outputProbeLatchFrameCfg_post tm controllerTapes
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address)
    input output extras false

theorem outputProbeCountOnesFrameCfg_address_internal
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx countIdx : Fin controllerTapes)
    (hne : addressIdx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (address : ℕ) :
    ((outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).work
      (outputProbeIndexedControllerIdx n addressIdx)).HasBinaryNat address := by
  rw [outputProbeLatchFramePost_controller tm controllerTapes
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address)
    input output extras false
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).input
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).work
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).output
    (outputProbeCountOnesFrameCfg_post_internal tm controllerTapes addressIdx
      countIdx outerExtras bits input output extras address)
    addressIdx]
  exact outputProbeCountOnesOuterExtrasAt_address_internal n hne outerExtras
    bits address

theorem outputProbeCountOnesFrameCfg_other_internal
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx countIdx idx : Fin controllerTapes)
    (haddress : idx ≠ addressIdx) (hcount : idx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (address : ℕ) :
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
        outerExtras bits input output extras address).work
        (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  rw [outputProbeLatchFramePost_controller tm controllerTapes
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address)
    input output extras false
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).input
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).work
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).output
    (outputProbeCountOnesFrameCfg_post_internal tm controllerTapes addressIdx
      countIdx outerExtras bits input output extras address)
    idx]
  exact outputProbeCountOnesOuterExtrasAt_other_internal n haddress hcount
    outerExtras bits address

theorem outputProbeCountOnesFrameCfg_parked_internal
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houtput : Parked output) (address : ℕ) :
    Parked (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
        countIdx outerExtras bits input output extras address).input ∧
      (∀ i, Parked
        ((outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
          outerExtras bits input output extras address).work i)) ∧
      Parked (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
        countIdx outerExtras bits input output extras address).output := by
  exact outputProbeLatchFramePost_parked tm controllerTapes
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      address)
    input output extras false hextras
    (outputProbeCountOnesOuterExtrasAt_parked_internal n outerExtras houter bits
      address)
    houtput
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).input
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).work
    (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
      outerExtras bits input output extras address).output
    (outputProbeCountOnesFrameCfg_post_internal tm controllerTapes addressIdx
      countIdx outerExtras bits input output extras address)

theorem outputProbeCountOnesDoneCfg_count_internal
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (limitValue : ℕ) :
    ((outputProbeCountOnesDoneCfg tm controllerTapes addressIdx scratchIdx
      limitIdx countIdx outerExtras bits input output extras limitValue).work
      (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
        (outputProbePrefixOnes bits limitValue) := by
  let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras limitValue
  have hpost := outputProbeCountOnesFrameCfg_post_internal tm controllerTapes
    addressIdx countIdx outerExtras bits input output extras limitValue
  change (frame.work
    (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
      (outputProbePrefixOnes bits limitValue)
  rw [outputProbeLatchFramePost_controller tm controllerTapes
    (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
      limitValue)
    input output extras false frame.input frame.work frame.output hpost countIdx]
  simpa [outputProbeCountOnesDoneCfg, frame] using
    outputProbeCountOnesOuterExtrasAt_count_internal n outerExtras bits
      limitValue

theorem outputProbeCountOnesOuterExtrasAfter_eq_internal
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
        (outputProbeCounterTape (outputProbePrefixOnes bits (address + 1))) := by
  by_cases hbit : bits[address]'haddress
  · simp only [outputProbeCountOnesOuterExtrasAfter, hbit, if_true]
    rw [outputProbePrefixOnes_succ_internal bits address haddress, if_pos hbit]
  · simp only [outputProbeCountOnesOuterExtrasAfter]
    rw [if_neg hbit]
    rw [outputProbePrefixOnes_succ_internal bits address haddress, if_neg hbit,
      Nat.add_zero]
    funext i
    by_cases hi : i = outputProbeIndexedControllerIdx n countIdx
    · subst i
      simp [outputProbeCountOnesOuterExtrasAt]
    · rw [Function.update_of_ne hi]

theorem outputProbeCountOnesOuterExtrasAt_succ_internal
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
        (address + 1) := by
  rw [outputProbeCountOnesOuterExtrasAfter_eq_internal n outerExtras bits
    address haddress]
  let addressPhysical := outputProbeIndexedControllerIdx n addressIdx
  let countPhysical := outputProbeIndexedControllerIdx n countIdx
  have hphysical : addressPhysical ≠ countPhysical :=
    outputProbeScan_address_ne_limit_internal n hne
  funext i
  by_cases hiAddress : i = addressPhysical
  · subst i
    simp [outputProbeCountOnesOuterExtrasAt, addressPhysical, countPhysical,
      hphysical]
  · by_cases hiCount : i = countPhysical
    · subst i
      rw [Function.update_of_ne hiAddress]
      simp [outputProbeCountOnesOuterExtrasAt, countPhysical]
    · simp [outputProbeCountOnesOuterExtrasAt, addressPhysical,
        countPhysical, hiAddress, hiCount]

theorem outputProbeCountOnesBodyTM_reachesIn_frame_internal
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx countIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (count : ℕ) (bit : Bool)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {bodyBound : ℕ}
    (hpre : pre
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).input
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).output)
    (hbody : (outputProbeCountOnesBodyTM tm controllerTapes addressIdx
      scratchIdx countIdx).HoareTime pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            bit)
          input output extras false)
        bodyBound) :
    ∃ time, time ≤ bodyBound ∧
      (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
        countIdx).reachesIn time
        { state := (outputProbeCountOnesBodyTM tm controllerTapes addressIdx
              scratchIdx countIdx).qstart
          input := (outputProbeLatchFrameCfg tm controllerTapes outerExtras
            input output extras false).input
          work := (outputProbeLatchFrameCfg tm controllerTapes outerExtras
            input output extras false).work
          output := (outputProbeLatchFrameCfg tm controllerTapes outerExtras
            input output extras false).output }
        { state := (outputProbeCountOnesBodyTM tm controllerTapes addressIdx
              scratchIdx countIdx).qhalt
          input := (outputProbeLatchFrameCfg tm controllerTapes
            (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
              bit)
            input output extras false).input
          work := (outputProbeLatchFrameCfg tm controllerTapes
            (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
              bit)
            input output extras false).work
          output := (outputProbeLatchFrameCfg tm controllerTapes
            (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
              bit)
            input output extras false).output } := by
  obtain ⟨done, time, htime, hreach, hhalt, hpost⟩ := hbody
    (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
      extras false).input
    (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
      extras false).work
    (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
      extras false).output hpre
  obtain ⟨hinput, hwork, houtput⟩ :=
    outputProbeLatchFramePost_eq_frameCfg tm controllerTapes
      (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count bit)
      input output extras false done.input done.work done.output hpost
  have hdone : done =
      { state := (outputProbeCountOnesBodyTM tm controllerTapes addressIdx
            scratchIdx countIdx).qhalt
        input := (outputProbeLatchFrameCfg tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            bit)
          input output extras false).input
        work := (outputProbeLatchFrameCfg tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            bit)
          input output extras false).work
        output := (outputProbeLatchFrameCfg tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            bit)
          input output extras false).output } :=
    Cfg.ext hhalt hinput hwork houtput
  exact ⟨time, htime, hdone ▸ hreach⟩

theorem outputProbeCountOnesIteration_reachesIn_of_body_internal
    (tm : TM n) (controllerTapes : ℕ)
    (addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes)
    (haddressCount : addressIdx ≠ countIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (address : ℕ) (haddress : address < bits.length)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {bodyBound : ℕ}
    (hpre : pre
      (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
        outerExtras bits input output extras address).input
      (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
        outerExtras bits input output extras address).work
      (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx countIdx
        outerExtras bits input output extras address).output)
    (hbody : (outputProbeCountOnesBodyTM tm controllerTapes addressIdx
      scratchIdx countIdx).HoareTime pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx
            (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx
              outerExtras bits address)
            (outputProbePrefixOnes bits address) (bits[address]'haddress))
          input output extras false)
        bodyBound) :
    ∃ time, time ≤ bodyBound + 1 + binarySuccTime address ∧
      (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx
        limitIdx countIdx).reachesIn time
        (outputProbeCountOnesIterationStartCfg tm controllerTapes addressIdx
          scratchIdx limitIdx countIdx outerExtras bits input output extras
          address)
        (outputProbeCountOnesIterationDoneCfg tm controllerTapes addressIdx
          scratchIdx limitIdx countIdx outerExtras bits input output extras
          address) := by
  let currentOuter := outputProbeCountOnesOuterExtrasAt n addressIdx countIdx
    outerExtras bits address
  let afterOuter := outputProbeCountOnesOuterExtrasAfter n countIdx
    currentOuter (outputProbePrefixOnes bits address) (bits[address]'haddress)
  let body := outputProbeCountOnesBodyTM tm controllerTapes addressIdx
    scratchIdx countIdx
  let counter := outputProbeIndexedControllerIdx n addressIdx
  let limit := outputProbeIndexedControllerIdx n limitIdx
  let startFrame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras address
  let afterFrame := outputProbeLatchFrameCfg tm controllerTapes afterOuter
    input output extras false
  let nextFrame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
    countIdx outerExtras bits input output extras (address + 1)
  obtain ⟨bodySteps, hbodySteps, hbodyRun⟩ :=
    outputProbeCountOnesBodyTM_reachesIn_frame_internal tm controllerTapes
      addressIdx scratchIdx countIdx currentOuter input output extras
      (outputProbePrefixOnes bits address) (bits[address]'haddress) hpre hbody
  have hcurrentOuterParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (currentOuter i) :=
    outputProbeCountOnesOuterExtrasAt_parked_internal n outerExtras houter bits
      address
  have hafterOuterParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (afterOuter i) :=
    outputProbeCountOnesOuterExtrasAfter_parked_internal n countIdx
      currentOuter hcurrentOuterParked (outputProbePrefixOnes bits address)
      (bits[address]'haddress)
  have hafterPost := outputProbeLatchFrameCfg_post tm controllerTapes
    afterOuter input output extras false
  have hafterParked := outputProbeLatchFramePost_parked tm controllerTapes
    afterOuter input output extras false hextras hafterOuterParked houtput
    afterFrame.input afterFrame.work afterFrame.output hafterPost
  have hafterAddress : (afterFrame.work counter).HasBinaryNat address := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes afterOuter
      input output extras false afterFrame.input afterFrame.work
      afterFrame.output hafterPost addressIdx]
    exact outputProbeCountOnesOuterExtrasAfter_address_internal n
      haddressCount outerExtras bits address (bits[address]'haddress)
  have hsucc := outputProbeCountOnesBinarySuccCanonical_reachesIn_internal
    counter address afterFrame.input afterFrame.work afterFrame.output
    hafterAddress hafterParked.1 hafterParked.2.1 hafterParked.2.2
  let updatedOuter := Function.update afterOuter counter
    (outputProbeCounterTape (address + 1))
  have hupdatedPost : outputProbeLatchFramePost tm controllerTapes
      updatedOuter input output extras false afterFrame.input
      (Function.update afterFrame.work counter
        (outputProbeCounterTape (address + 1)))
      afterFrame.output := by
    exact outputProbeLatchFramePost_updateController tm controllerTapes
      afterOuter input output extras false afterFrame.input afterFrame.work
      afterFrame.output hafterPost addressIdx
      (outputProbeCounterTape (address + 1))
  have hupdatedEq := outputProbeLatchFramePost_eq_frameCfg tm controllerTapes
    updatedOuter input output extras false afterFrame.input
    (Function.update afterFrame.work counter
      (outputProbeCounterTape (address + 1)))
    afterFrame.output hupdatedPost
  have hupdatedOuter : updatedOuter =
      outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras bits
        (address + 1) := by
    exact outputProbeCountOnesOuterExtrasAt_succ_internal n haddressCount
      outerExtras bits address haddress
  have hnextInput : afterFrame.input = nextFrame.input := by
    simpa [updatedOuter, hupdatedOuter, nextFrame,
      outputProbeCountOnesFrameCfg] using hupdatedEq.1
  have hnextWork :
      Function.update afterFrame.work counter
          (outputProbeCounterTape (address + 1)) = nextFrame.work := by
    simpa [updatedOuter, hupdatedOuter, nextFrame,
      outputProbeCountOnesFrameCfg] using hupdatedEq.2.1
  have hnextOutput : afterFrame.output = nextFrame.output := by
    simpa [updatedOuter, hupdatedOuter, nextFrame,
      outputProbeCountOnesFrameCfg] using hupdatedEq.2.2
  have hsuccNext : (binarySuccTM counter).reachesIn
      (binarySuccTime address)
      { state := (binarySuccTM counter).qstart
        input := afterFrame.input
        work := afterFrame.work
        output := afterFrame.output }
      { state := (binarySuccTM counter).qhalt
        input := nextFrame.input
        work := nextFrame.work
        output := nextFrame.output } := by
    have hend :
        ({ state := (binarySuccTM counter).qhalt
           input := afterFrame.input
           work := Function.update afterFrame.work counter
             (outputProbeCounterTape (address + 1))
           output := afterFrame.output } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (binarySuccTM counter).Q) =
        { state := (binarySuccTM counter).qhalt
          input := nextFrame.input
          work := nextFrame.work
          output := nextFrame.output } :=
      Cfg.ext rfl hnextInput hnextWork hnextOutput
    exact hend ▸ hsucc
  have hinpTransition : transitionInput afterFrame.input = afterFrame.input :=
    hafterParked.1.transitionInput_eq_self
  have hworkTransition :
      (fun i => transitionTape (afterFrame.work i)) = afterFrame.work := by
    funext i
    exact (hafterParked.2.1 i).transitionTape_eq_self
  have houtTransition : transitionTape afterFrame.output = afterFrame.output :=
    hafterParked.2.2.transitionTape_eq_self
  have hsuccNext' : (binarySuccTM counter).reachesIn
      (binarySuccTime address)
      { state := (binarySuccTM counter).qstart
        input := transitionInput afterFrame.input
        work := fun i => transitionTape (afterFrame.work i)
        output := transitionTape afterFrame.output }
      { state := (binarySuccTM counter).qhalt
        input := nextFrame.input
        work := nextFrame.work
        output := nextFrame.output } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hsuccNext
  have hseq := seqTM_reachesIn_of_reachesIn body (binarySuccTM counter)
    hbodyRun rfl hsuccNext'
  have hlift := binaryForTM_iteration_reachesIn_internal body counter limit
    hseq
  refine ⟨bodySteps + 1 + binarySuccTime address, ?_, ?_⟩
  · omega
  · simpa [body, counter, limit, startFrame, afterFrame, nextFrame,
      outputProbeCountOnesTM, outputProbeCountOnesIterationStartCfg,
      outputProbeCountOnesIterationDoneCfg, binaryForIterationWrap,
      binaryForIterationTM, phase1Wrap, phase2Wrap] using hlift

/-- Internal constructor for the explicit count-ones segment invariant. -/
noncomputable def outputProbeCountOnesSegmentSpecOfIterationWitnessesInternal
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
      bodyTime startValue limitValue := by
  let body := outputProbeCountOnesBodyTM tm controllerTapes addressIdx
    scratchIdx countIdx
  let counter := outputProbeIndexedControllerIdx n addressIdx
  let limit := outputProbeIndexedControllerIdx n limitIdx
  let scanCfg := outputProbeCountOnesScanCfg tm controllerTapes addressIdx
    scratchIdx limitIdx countIdx outerExtras bits input output extras
  let iterationStartCfg := outputProbeCountOnesIterationStartCfg tm
    controllerTapes addressIdx scratchIdx limitIdx countIdx outerExtras bits
    input output extras
  let iterationDoneCfg := outputProbeCountOnesIterationDoneCfg tm
    controllerTapes addressIdx scratchIdx limitIdx countIdx outerExtras bits
    input output extras
  let doneCfg := outputProbeCountOnesDoneCfg tm controllerTapes addressIdx
    scratchIdx limitIdx countIdx outerExtras bits input output extras limitValue
  apply BinaryForSegmentSpec.ofWitnessesInternal
    (outputProbeScan_address_ne_limit_internal n haddressLimit)
    scanCfg iterationStartCfg iterationDoneCfg doneCfg
  · intro value _hstart hvalue
    let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
      countIdx outerExtras bits input output extras value
    have hparked := outputProbeCountOnesFrameCfg_parked_internal tm
      controllerTapes addressIdx countIdx outerExtras houter bits input output
      extras hextras houtput value
    have hcounter := outputProbeCountOnesFrameCfg_address_internal tm
      controllerTapes addressIdx countIdx haddressCount outerExtras bits input
      output extras value
    have hlimitFrame : (frame.work limit).HasBinaryNat limitValue := by
      rw [outputProbeCountOnesFrameCfg_other_internal tm controllerTapes
        addressIdx countIdx limitIdx (Ne.symm haddressLimit)
        (Ne.symm hcountLimit) outerExtras bits input output extras value]
      exact hlimit
    have hrun := binaryForTM_compare_reachesIn_frame_of_lt_internal body
      counter limit (outputProbeScan_address_ne_limit_internal n haddressLimit)
      value limitValue hvalue frame.input frame.work frame.output hcounter
      hlimitFrame hparked.1.read_ne_start
      (fun i _ _ => (hparked.2.1 i).read_ne_start)
      hparked.2.2.read_ne_start
    simpa [body, counter, limit, scanCfg, iterationStartCfg,
      outputProbeCountOnesTM, outputProbeCountOnesScanCfg,
      outputProbeCountOnesIterationStartCfg, frame] using hrun
  · intro value hstart hvalue
    simpa [scanCfg, iterationStartCfg, iterationDoneCfg,
      outputProbeCountOnesTM] using iterationWitness value hstart hvalue
  · intro value _hstart _hvalue
    let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
      countIdx outerExtras bits input output extras (value + 1)
    let c : Cfg (0 + outputProbeControllerTapes n + controllerTapes)
        (binaryForIterationTM body counter).Q :=
      { state := (binaryForIterationTM body counter).qhalt
        input := frame.input
        work := frame.work
        output := frame.output }
    have hparked := outputProbeCountOnesFrameCfg_parked_internal tm
      controllerTapes addressIdx countIdx outerExtras houter bits input output
      extras hextras houtput (value + 1)
    have hstep := binaryForTM_step_iteration_halt_internal body counter limit c
      rfl hparked.1.read_ne_start
      (fun i => (hparked.2.1 i).read_ne_start) hparked.2.2.read_ne_start
    simpa [body, counter, limit, iterationDoneCfg, scanCfg,
      outputProbeCountOnesTM, outputProbeCountOnesIterationDoneCfg,
      outputProbeCountOnesScanCfg, binaryForIterationWrap, c, frame] using hstep
  · let frame := outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
      countIdx outerExtras bits input output extras limitValue
    have hparked := outputProbeCountOnesFrameCfg_parked_internal tm
      controllerTapes addressIdx countIdx outerExtras houter bits input output
      extras hextras houtput limitValue
    have hcounter := outputProbeCountOnesFrameCfg_address_internal tm
      controllerTapes addressIdx countIdx haddressCount outerExtras bits input
      output extras limitValue
    have hlimitFrame : (frame.work limit).HasBinaryNat limitValue := by
      rw [outputProbeCountOnesFrameCfg_other_internal tm controllerTapes
        addressIdx countIdx limitIdx (Ne.symm haddressLimit)
        (Ne.symm hcountLimit) outerExtras bits input output extras limitValue]
      exact hlimit
    have hrun := binaryForTM_compare_reachesIn_frame_of_eq_internal body
      counter limit (outputProbeScan_address_ne_limit_internal n haddressLimit)
      limitValue frame.input frame.work frame.output hcounter hlimitFrame
      hparked.1.read_ne_start
      (fun i _ _ => (hparked.2.1 i).read_ne_start)
      hparked.2.2.read_ne_start
    simpa [body, counter, limit, scanCfg, doneCfg, outputProbeCountOnesTM,
      outputProbeCountOnesScanCfg, outputProbeCountOnesDoneCfg, frame] using
      hrun
  · simp [doneCfg, outputProbeCountOnesDoneCfg, outputProbeCountOnesTM,
      binaryForTM]

/-- Internal constructor lifting bounded body contracts into a segment. -/
noncomputable def outputProbeCountOnesSegmentSpecOfBodyWitnessesInternal
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
                (outputProbePrefixOnes bits value)
                (bits[value]'hvalueBits))
              input output extras false)
            bodyBound) :
    BinaryForSegmentSpec
      (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
        countIdx)
      (outputProbeIndexedControllerIdx n addressIdx)
      (outputProbeIndexedControllerIdx n limitIdx)
      bodyTime startValue limitValue := by
  apply outputProbeCountOnesSegmentSpecOfIterationWitnessesInternal tm
    controllerTapes addressIdx scratchIdx limitIdx countIdx haddressLimit
    haddressCount hcountLimit outerExtras bits input output extras hextras
    houter houtput bodyTime startValue limitValue hlimit
  intro value hstart hvalue
  have hvalueBits : value < bits.length := by omega
  obtain ⟨bodyBound, pre, hbound, hpre, hbody⟩ :=
    bodyWitness value hstart hvalue hvalueBits
  obtain ⟨time, htime, hrun⟩ :=
    outputProbeCountOnesIteration_reachesIn_of_body_internal tm
      controllerTapes addressIdx scratchIdx limitIdx countIdx haddressCount
      outerExtras bits input output extras hextras houter houtput value
      hvalueBits hpre hbody
  refine ⟨time, ?_, hrun⟩
  simp only [binaryForIterationTime]
  omega

theorem outputProbeCountOnes_zero_hoareTimeSpace_internal
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
      1 inputLength (initialSpace + 1) := by
  have htime : (skipTM (n := 0 + outputProbeControllerTapes n +
      controllerTapes)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
          false)
        input output extras false) 1 := by
    intro inp work out hpost
    obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes outerExtras input output extras false hextras houter
      houtput inp work out hpost
    have hskip := skipTM_hoareTime_frame inp work out hinput hwork hout
    obtain ⟨done, elapsed, helapsed, hreach, hhalt, hinputDone,
        hworkDone, houtputDone⟩ :=
      hskip inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨done, elapsed, helapsed, hreach, hhalt, ?_⟩
    rw [hinputDone, hworkDone, houtputDone]
    simpa [outputProbeCountOnesOuterExtrasAfter] using hpost
  exact htime.toHoareTimeSpace hinitial

theorem outputProbeCountOnes_one_hoareTimeSpace_internal
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
      (initialSpace + binarySuccTime count) := by
  let physicalCount := outputProbeIndexedControllerIdx n countIdx
  let nextTape := outputProbeCounterTape (count + 1)
  have htime : (binarySuccTM physicalCount).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count true)
        input output extras false)
      (binarySuccTime count) := by
    intro inp work out hpost
    obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes outerExtras input output extras false hextras houter
      houtput inp work out hpost
    have hcountWork : (work physicalCount).HasBinaryNat count := by
      rw [outputProbeLatchFramePost_controller tm controllerTapes
        outerExtras input output extras false inp work out hpost countIdx]
      exact hcount
    obtain ⟨done, hreach, hhalt, hinputDone, hotherDone, hcountDone,
        houtputDone⟩ :=
      binarySuccTM_reachesIn_frame physicalCount count inp work out
        hcountWork hinput.read_ne_start
        (fun i _ => (hwork i).read_ne_start) hout.read_ne_start
    have hnext : done.work = Function.update work physicalCount nextTape := by
      funext i
      by_cases hi : i = physicalCount
      · subst i
        rw [Function.update_self]
        exact hcountDone.eq_init_move_right
      · rw [Function.update_of_ne hi]
        exact hotherDone i hi
    refine ⟨done, binarySuccTime count, le_rfl, hreach, hhalt, ?_⟩
    rw [hinputDone, hnext, houtputDone]
    simpa [physicalCount, nextTape, outputProbeCountOnesOuterExtrasAfter]
      using outputProbeLatchFramePost_updateController tm controllerTapes
        outerExtras input output extras false inp work out hpost countIdx
        nextTape
  exact htime.toHoareTimeSpace hinitial

theorem outputProbeCountOnesBodyTM_of_latch_hoareTimeSpace_internal
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
          else zeroInitialSpace + 1)) := by
  have hzero := outputProbeCountOnes_zero_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    countIdx count inputLength zeroInitialSpace hzeroInitial
  have hone := outputProbeCountOnes_one_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    countIdx count inputLength oneInitialSpace hcount honeInitial
  simpa [outputProbeCountOnesBodyTM] using
    outputProbeIndexedResetDispatchTM_of_latch_hoareTimeSpace tm
      controllerTapes addressIdx scratchIdx outerExtras input output extras bit
      hextras houter houtput skipTM
      (binarySuccTM (outputProbeIndexedControllerIdx n countIdx))
      (post := fun branch =>
        outputProbeLatchFramePost tm controllerTapes
          (outputProbeCountOnesOuterExtrasAfter n countIdx outerExtras count
            branch)
          input output extras false)
      hlatch
      hclearInitial hzero hone

theorem ComputesInSpace.outputProbeCountOnesBodyTM_hoareTime_internal
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
          bodyBound := by
  let frame := outputProbeLatchFrameCfg tm controllerTapes outerExtras input
    output extras false
  let queryFrame := placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes
    outerExtras
    (outputProbePlacedFrameCfg tm input
      (outputProbeCounterTape (address + 1)) output extras)
  let frameSpace := Finset.univ.sup fun i => (extras i).head
  let outerFrameSpace := Finset.univ.sup fun i => (outerExtras i).head
  let initialSpace := Finset.univ.sup fun i => (frame.work i).head
  let pre : TapePred
      (0 + outputProbeControllerTapes n + controllerTapes) :=
    fun inp work out =>
      inp = queryFrame.input ∧ work = frame.work ∧ out = output
  have hframePost := outputProbeLatchFrameCfg_post tm controllerTapes
    outerExtras input output extras false
  have hparked := outputProbeLatchFramePost_parked tm controllerTapes
    outerExtras input output extras false hextras houter houtput frame.input
    frame.work frame.output hframePost
  have hframeBound : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace := by
    intro i _hi
    exact Finset.le_sup (f := fun j => (extras j).head)
      (Finset.mem_univ i)
  have houterRead : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).read ≠ Γ.start := by
    intro i hi
    exact (houter i hi).read_ne_start
  have houterBound : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).head ≤ outerFrameSpace := by
    intro i _hi
    exact Finset.le_sup (f := fun j => (outerExtras j).head)
      (Finset.mem_univ i)
  have hworkBound : ∀ i, (frame.work i).head ≤ initialSpace := by
    intro i
    exact Finset.le_sup (f := fun j => (frame.work j).head)
      (Finset.mem_univ i)
  have hqueryInput : queryFrame.input = frame.input := by
    rfl
  have hqueryOutput : frame.output = output := by
    simp [frame, outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg,
      outputProbePlacedFrameCfg]
  have hsourceWork :
      (frame.work (outputProbeIndexedControllerIdx n addressIdx))
        |>.HasBinaryNat address := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hframePost
      addressIdx]
    exact hsource
  have hscratchWork :
      (frame.work (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0 := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hframePost
      scratchIdx]
    exact hscratch
  have hframeWork : frame.work = Function.update queryFrame.work
      (outputProbeIndexedCountdownIdx n controllerTapes)
      (outputProbeCounterTape 0) := by
    exact outputProbeLatchFrameCfg_work_eq_queryUpdate tm input output extras
      hcleanupCounter controllerTapes address outerExtras
  have hcountdown :
      (frame.work (outputProbeIndexedCountdownIdx n controllerTapes))
        |>.HasBinaryNat 0 := by
    rw [hframeWork, Function.update_self]
    exact Tape.init_move_right_hasBinaryNat 0
  have hqueryWork : ∀ i,
      i ≠ outputProbeIndexedCountdownIdx n controllerTapes →
      frame.work i = queryFrame.work i := by
    intro i hi
    rw [hframeWork, Function.update_of_ne hi]
  have hinputSpace : queryFrame.input.head ≤
      input.length + initialSpace + 1 := by
    simp [queryFrame, outputProbePlacedFrameCfg, outputProbeStartedCfg,
      Tape.move]
  obtain ⟨latchTime, hlatch⟩ :=
    hcomp.outputProbeIndexedLatchTM_hoareTimeSpace input address haddress
      output houtput extras frameSpace cleanupLimit hextras hframeBound
      hcleanupCounter hcleanupLimit hlimit controllerTapes outerExtras
      outerFrameSpace houterRead houterBound addressIdx scratchIdx
      haddressScratch initialSpace frame.work hsourceWork hcountdown
      hscratchWork (hqueryInput ▸ hparked.1) hparked.2.1 hworkBound hinputSpace
      hqueryWork
  let falseFrame := outputProbeLatchFrameCfg tm controllerTapes outerExtras
    input output extras false
  let trueFrame := outputProbeLatchFrameCfg tm controllerTapes outerExtras
    input output extras true
  let falseSpace := Finset.univ.sup fun i => (falseFrame.work i).head
  let trueSpace := Finset.univ.sup fun i => (trueFrame.work i).head
  have hframeInitial (bit : Bool) : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit inp work out →
      ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (skipTM (n := 0 + outputProbeControllerTapes n +
            controllerTapes)).Q).WithinAuxSpace input.length
          (Finset.univ.sup fun i =>
            ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input
              output extras bit).work i).head) := by
    intro inp work out hpost
    obtain ⟨hinp, hwork, _hout⟩ := outputProbeLatchFramePost_eq_frameCfg tm
      controllerTapes outerExtras input output extras bit inp work out hpost
    subst inp
    subst work
    constructor
    · intro i
      exact Finset.le_sup
        (f := fun j =>
          ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input
            output extras bit).work j).head)
        (Finset.mem_univ i)
    · simp [outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg,
        outputProbePlacedFrameCfg, outputProbeStartedCfg, Tape.move]
  have hclearInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
      ({ state := (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (clearWorkTM (outputProbeLatchIdx n controllerTapes)).Q
        ).WithinAuxSpace input.length trueSpace := by
    simpa [trueSpace, trueFrame] using hframeInitial true
  have hzeroInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
      ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (skipTM (n := 0 + outputProbeControllerTapes n +
            controllerTapes)).Q).WithinAuxSpace input.length falseSpace := by
    simpa [falseSpace, falseFrame] using hframeInitial false
  have honeInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
      ({ state := (binarySuccTM
              (outputProbeIndexedControllerIdx n countIdx)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (binarySuccTM
            (outputProbeIndexedControllerIdx n countIdx)).Q
        ).WithinAuxSpace input.length falseSpace := by
    simpa [falseSpace, falseFrame] using hframeInitial false
  let bodyBound := outputProbeIndexedPrepareTime address + 1 + latchTime + 1 +
    outputProbeLatchDispatchTime ((f input)[address]'haddress) 1
      (clearWorkTimeBound 1 + 1 + binarySuccTime count)
  have hbody := outputProbeCountOnesBodyTM_of_latch_hoareTimeSpace_internal tm
    controllerTapes addressIdx scratchIdx countIdx outerExtras input output
    extras ((f input)[address]'haddress) hextras houter houtput count hcount
    hlatch hclearInitial hzeroInitial honeInitial
  refine ⟨bodyBound, pre, ?_, ?_⟩
  · exact ⟨hqueryInput.symm, rfl, hqueryOutput⟩
  · simpa [bodyBound] using hbody.1

/-- Internal constructor selecting all source-dependent count-scan runtimes. -/
noncomputable def
    ComputesInSpace.outputProbeCountOnesSegmentSpecInternal
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
        bodyTime startValue limitValue := by
  classical
  let currentOuter (value : ℕ) :=
    outputProbeCountOnesOuterExtrasAt n addressIdx countIdx outerExtras
      (f input) value
  have bodyExists : ∀ value, ∃ bodyBound : ℕ,
      ∀ (hstart : startValue ≤ value) (hvalue : value < limitValue)
        (hvalueBits : value < (f input).length),
        ∃ pre : TapePred
            (0 + outputProbeControllerTapes n + controllerTapes),
          pre
            (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
              countIdx outerExtras (f input) input output extras value).input
            (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
              countIdx outerExtras (f input) input output extras value).work
            (outputProbeCountOnesFrameCfg tm controllerTapes addressIdx
              countIdx outerExtras (f input) input output extras value).output ∧
          (outputProbeCountOnesBodyTM tm controllerTapes addressIdx scratchIdx
            countIdx).HoareTime pre
              (outputProbeLatchFramePost tm controllerTapes
                (outputProbeCountOnesOuterExtrasAfter n countIdx
                  (currentOuter value)
                  (outputProbePrefixOnes (f input) value)
                  ((f input)[value]'hvalueBits))
                input output extras false)
              bodyBound := by
    intro value
    by_cases hrange : startValue ≤ value ∧ value < limitValue
    · have hcurrentParked : ∀ i,
          ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
            Parked (currentOuter value i) :=
        outputProbeCountOnesOuterExtrasAt_parked_internal n outerExtras houter
          (f input) value
      have hsourceCurrent :
          (currentOuter value
            (outputProbeIndexedControllerIdx n addressIdx)).HasBinaryNat
              value := by
        exact outputProbeCountOnesOuterExtrasAt_address_internal n
          haddressCount outerExtras (f input) value
      have hscratchCurrent :
          (currentOuter value
            (outputProbeIndexedControllerIdx n scratchIdx)).HasBinaryNat
              0 := by
        change (outputProbeCountOnesOuterExtrasAt n addressIdx countIdx
          outerExtras (f input) value
          (outputProbeIndexedControllerIdx n scratchIdx)).HasBinaryNat 0
        rw [outputProbeCountOnesOuterExtrasAt_other_internal n
          hscratchAddress hscratchCount outerExtras (f input) value]
        exact hscratch
      have hcountCurrent :
          (currentOuter value
            (outputProbeIndexedControllerIdx n countIdx)).HasBinaryNat
              (outputProbePrefixOnes (f input) value) := by
        exact outputProbeCountOnesOuterExtrasAt_count_internal n outerExtras
          (f input) value
      obtain ⟨bodyBound, pre, hpre, hbody⟩ :=
        hcomp.outputProbeCountOnesBodyTM_hoareTime_internal input value
          (by omega) output houtput extras hextras hcleanupCounter cleanupLimit
          hcleanupLimit (hqueryLimit value hrange.1 hrange.2)
          controllerTapes (currentOuter value) hcurrentParked addressIdx
          scratchIdx countIdx haddressScratch hsourceCurrent hscratchCurrent
          (outputProbePrefixOnes (f input) value) hcountCurrent
      refine ⟨bodyBound, ?_⟩
      intro _hstart _hvalue hvalueBits
      refine ⟨pre, ?_, hbody⟩
      simpa [currentOuter, outputProbeCountOnesFrameCfg] using hpre
    · refine ⟨0, ?_⟩
      intro hstart hvalue _hvalueBits
      exact (hrange ⟨hstart, hvalue⟩).elim
  choose bodyTime hbody using bodyExists
  refine ⟨bodyTime,
    outputProbeCountOnesSegmentSpecOfBodyWitnessesInternal tm controllerTapes
      addressIdx scratchIdx limitIdx countIdx haddressLimit haddressCount
      hcountLimit outerExtras (f input) input output extras hextras houter
      houtput bodyTime startValue limitValue hlimitBits hlimitRegister ?_⟩
  intro value hstart hvalue hvalueBits
  obtain ⟨pre, hpre, hhoare⟩ :=
    hbody value hstart hvalue hvalueBits
  exact ⟨bodyTime value, pre, le_rfl, hpre, hhoare⟩

theorem IsTransducer.outputProbeCountOnesTM_internal
    {tm : TM n} {controllerTapes : ℕ}
    {addressIdx scratchIdx limitIdx countIdx : Fin controllerTapes} :
    (outputProbeCountOnesTM tm controllerTapes addressIdx scratchIdx limitIdx
      countIdx).IsTransducer := by
  unfold outputProbeCountOnesTM
  exact (skipTM_isTransducer_internal.outputProbeIndexedResetDispatchTM
      (binarySuccTM_isTransducer
        (outputProbeIndexedControllerIdx n countIdx))).binaryForTM
    (outputProbeIndexedControllerIdx n addressIdx)
    (outputProbeIndexedControllerIdx n limitIdx)

end TM

end Complexity
