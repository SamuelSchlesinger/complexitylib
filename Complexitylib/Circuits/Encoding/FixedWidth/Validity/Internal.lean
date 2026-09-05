/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Defs
import Complexitylib.Circuits.BinaryComparison
import Complexitylib.Circuits.Encoding.FixedWidth.Codec
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion
import Complexitylib.Circuits.Encoding.Formula
import Complexitylib.Circuits.Encoding.Formula.Batch
import Mathlib.Tactic.FinCases

/-!
# Fixed-width description validity formulas -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace ValidityFormula

theorem code_apply_countCoordinate_internal
    {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound))
    (coordinate : Fin (gateCountWidth gateBound)) :
    code (countCoordinate inputWidth gateBound coordinate) =
      countBits code coordinate := by
  simp [countCoordinate, countBits, Fin.appendEquiv]

theorem code_apply_slotCoordinate_internal
    {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound))
    (slot : Fin gateBound)
    (coordinate : Fin (gateSlotWidth inputWidth gateBound)) :
    code (slotCoordinate inputWidth gateBound slot coordinate) =
      slotBits code slot coordinate := by
  simp [slotCoordinate, slotBits, Fin.appendEquiv]

theorem decode_input0_internal {inputWidth gateBound : Nat}
    (bits : BitString (gateSlotWidth inputWidth gateBound))
    (coordinate : Fin (referenceWidth inputWidth gateBound)) :
    (GateSlot.decode bits).input0 coordinate =
      bits (input0Coordinate inputWidth gateBound coordinate) := by
  simp [GateSlot.decode, input0Coordinate, Fin.appendEquiv]

theorem decode_input1_internal {inputWidth gateBound : Nat}
    (bits : BitString (gateSlotWidth inputWidth gateBound))
    (coordinate : Fin (referenceWidth inputWidth gateBound)) :
    (GateSlot.decode bits).input1 coordinate =
      bits (input1Coordinate inputWidth gateBound coordinate) := by
  simp [GateSlot.decode, input1Coordinate, Fin.appendEquiv]

theorem eval_countAtLeast_internal {inputWidth gateBound : Nat}
    (minimum : Nat) (code : BitString (codeWidth inputWidth gateBound))
    (hminimum : minimum < 2 ^ gateCountWidth gateBound) :
    (countAtLeast inputWidth gateBound minimum).eval code.toTotal =
      decide (minimum ≤ countValue code) := by
  have hconstant :
      (GateSlot.referenceBits (gateCountWidth gateBound) minimum).unsignedValue =
        minimum := by
    unfold BitString.unsignedValue
    rw [GateSlot.toList_referenceBits,
      Nat.fromBitsLE_toBitsLE hminimum]
  have hcount :
      (fun coordinate : Fin (gateCountWidth gateBound) =>
        (countBit inputWidth gateBound coordinate).eval code.toTotal) =
        countBits code := by
    funext coordinate
    simp only [countBit, BoolFormula.eval, BitString.toTotal_apply]
    exact code_apply_countCoordinate_internal code coordinate
  rw [countAtLeast, BoolFormula.eval_unsignedLEOf,
    BitString.unsignedLE_eq_decide]
  simp only [BoolFormula.eval_ofBool, hconstant, hcount]
  rfl

theorem eval_countAtMost_internal {inputWidth gateBound : Nat}
    (maximum : Nat) (code : BitString (codeWidth inputWidth gateBound))
    (hmaximum : maximum < 2 ^ gateCountWidth gateBound) :
    (countAtMost inputWidth gateBound maximum).eval code.toTotal =
      decide (countValue code ≤ maximum) := by
  have hconstant :
      (GateSlot.referenceBits (gateCountWidth gateBound) maximum).unsignedValue =
        maximum := by
    unfold BitString.unsignedValue
    rw [GateSlot.toList_referenceBits,
      Nat.fromBitsLE_toBitsLE hmaximum]
  have hcount :
      (fun coordinate : Fin (gateCountWidth gateBound) =>
        (countBit inputWidth gateBound coordinate).eval code.toTotal) =
        countBits code := by
    funext coordinate
    simp only [countBit, BoolFormula.eval, BitString.toTotal_apply]
    exact code_apply_countCoordinate_internal code coordinate
  rw [countAtMost, BoolFormula.eval_unsignedLEOf,
    BitString.unsignedLE_eq_decide]
  simp only [BoolFormula.eval_ofBool, hconstant, hcount]
  rfl

theorem eval_referenceBelow_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (first : Bool) (available : Nat)
    (code : BitString (codeWidth inputWidth gateBound))
    (havailable : available < 2 ^ referenceWidth inputWidth gateBound) :
    (referenceBelow inputWidth gateBound slot first available).eval
        code.toTotal =
      decide (if first then
        (GateSlot.decode (slotBits code slot)).input0Value < available
      else
        (GateSlot.decode (slotBits code slot)).input1Value < available) := by
  have hconstant :
      (GateSlot.referenceBits (referenceWidth inputWidth gateBound)
        available).unsignedValue = available := by
    unfold BitString.unsignedValue
    rw [GateSlot.toList_referenceBits,
      Nat.fromBitsLE_toBitsLE havailable]
  cases first with
  | false =>
      have hbits :
          (fun coordinate : Fin (referenceWidth inputWidth gateBound) =>
            (input1Bit inputWidth gateBound slot coordinate).eval
              code.toTotal) =
            (GateSlot.decode (slotBits code slot)).input1 := by
        funext coordinate
        simp only [input1Bit, slotBit, BoolFormula.eval,
          BitString.toTotal_apply]
        rw [code_apply_slotCoordinate_internal code slot
          (input1Coordinate inputWidth gateBound coordinate)]
        exact (decode_input1_internal (slotBits code slot) coordinate).symm
      change
        Bool.not ((BoolFormula.unsignedLEOf
          (fun coordinate => BoolFormula.ofBool
            (GateSlot.referenceBits
              (referenceWidth inputWidth gateBound) available coordinate))
          (input1Bit inputWidth gateBound slot)).eval code.toTotal) =
          decide ((GateSlot.decode
            (slotBits code slot)).input1Value < available)
      rw [BoolFormula.eval_unsignedLEOf,
        BitString.unsignedLE_eq_decide]
      simp only [BoolFormula.eval_ofBool, hconstant, hbits]
      change Bool.not (decide (available ≤
          (GateSlot.decode (slotBits code slot)).input1Value)) =
        decide ((GateSlot.decode
          (slotBits code slot)).input1Value < available)
      by_cases hle : available ≤
          (GateSlot.decode (slotBits code slot)).input1Value
      · have hnlt : ¬(GateSlot.decode
            (slotBits code slot)).input1Value < available :=
          Nat.not_lt.mpr hle
        simp [hle, hnlt]
      · have hlt : (GateSlot.decode
            (slotBits code slot)).input1Value < available :=
          Nat.lt_of_not_ge hle
        simp [hle, hlt]
  | true =>
      have hbits :
          (fun coordinate : Fin (referenceWidth inputWidth gateBound) =>
            (input0Bit inputWidth gateBound slot coordinate).eval
              code.toTotal) =
            (GateSlot.decode (slotBits code slot)).input0 := by
        funext coordinate
        simp only [input0Bit, slotBit, BoolFormula.eval,
          BitString.toTotal_apply]
        rw [code_apply_slotCoordinate_internal code slot
          (input0Coordinate inputWidth gateBound coordinate)]
        exact (decode_input0_internal (slotBits code slot) coordinate).symm
      change
        Bool.not ((BoolFormula.unsignedLEOf
          (fun coordinate => BoolFormula.ofBool
            (GateSlot.referenceBits
              (referenceWidth inputWidth gateBound) available coordinate))
          (input0Bit inputWidth gateBound slot)).eval code.toTotal) =
          decide ((GateSlot.decode
            (slotBits code slot)).input0Value < available)
      rw [BoolFormula.eval_unsignedLEOf,
        BitString.unsignedLE_eq_decide]
      simp only [BoolFormula.eval_ofBool, hconstant, hbits]
      change Bool.not (decide (available ≤
          (GateSlot.decode (slotBits code slot)).input0Value)) =
        decide ((GateSlot.decode
          (slotBits code slot)).input0Value < available)
      by_cases hle : available ≤
          (GateSlot.decode (slotBits code slot)).input0Value
      · have hnlt : ¬(GateSlot.decode
            (slotBits code slot)).input0Value < available :=
          Nat.not_lt.mpr hle
        simp [hle, hnlt]
      · have hlt : (GateSlot.decode
            (slotBits code slot)).input0Value < available :=
          Nat.lt_of_not_ge hle
        simp [hle, hlt]

private theorem fromBits_replicate_false : ∀ width : Nat,
    Nat.fromBits (List.replicate width false) = 0
  | 0 => rfl
  | width + 1 => by
      simp [List.replicate_succ, Nat.fromBits,
        fromBits_replicate_false width]

private theorem unsignedValue_eq_zero_iff {width : Nat}
    (bits : BitString width) :
    bits.unsignedValue = 0 ↔ bits = fun _ => false := by
  constructor
  · intro hvalue
    apply BitString.toList_inj.mp
    apply Nat.fromBitsLE_inj_of_length_eq
    · simp
    · rw [show Nat.fromBitsLE bits.toList = 0 by exact hvalue]
      simp [BitString.toList, Nat.fromBitsLE,
        fromBits_replicate_false]
  · rintro rfl
    simp [BitString.unsignedValue, BitString.toList,
      Nat.fromBitsLE, fromBits_replicate_false]

private theorem decode_eq_zero_iff {width : Nat}
    (bits : BitString (3 + (width + width))) :
    GateSlot.decode bits = GateSlot.zero width ↔
      bits.unsignedValue = 0 := by
  have hzero : GateSlot.encode (GateSlot.zero width) =
      (fun _ => false) := by
    funext coordinate
    refine Fin.addCases (fun control => ?_) (fun inputs => ?_) coordinate
    · fin_cases control <;> rfl
    · refine Fin.addCases (fun input => ?_) (fun input => ?_) inputs
      · simp [GateSlot.encode, GateSlot.zero]
      · simp only [GateSlot.encode, GateSlot.zero, Fin.append_right]
  rw [unsignedValue_eq_zero_iff]
  constructor
  · intro hslot
    have hcode := congrArg GateSlot.encode hslot
    rw [GateSlot.encode_decode] at hcode
    simpa [hzero] using hcode
  · intro hcode
    apply GateSlot.encode_injective
    rw [GateSlot.encode_decode]
    simpa [hzero] using hcode

theorem eval_slotZero_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (code : BitString (codeWidth inputWidth gateBound)) :
    (slotZero inputWidth gateBound slot).eval code.toTotal =
      decide (GateSlot.decode (slotBits code slot) =
        GateSlot.zero (referenceWidth inputWidth gateBound)) := by
  have hbits :
      (fun coordinate : Fin (gateSlotWidth inputWidth gateBound) =>
        (slotBit inputWidth gateBound slot coordinate).eval code.toTotal) =
        slotBits code slot := by
    funext coordinate
    simp only [slotBit, BoolFormula.eval, BitString.toTotal_apply]
    exact code_apply_slotCoordinate_internal code slot coordinate
  rw [slotZero, BoolFormula.eval_unsignedLEOf,
    BitString.unsignedLE_eq_decide]
  simp only [BoolFormula.eval, hbits]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  have hzeroValue :
      BitString.unsignedValue
        (fun _ : Fin (gateSlotWidth inputWidth gateBound) => false) = 0 := by
    rw [unsignedValue_eq_zero_iff]
  rw [hzeroValue, Nat.le_zero]
  exact (decode_eq_zero_iff (slotBits code slot)).symm

theorem eval_slotWellFormed_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (code : BitString (codeWidth inputWidth gateBound)) :
    (slotWellFormed inputWidth gateBound slot).eval code.toTotal =
      decide ((GateSlot.decode (slotBits code slot)).WellFormedAt
        (inputWidth + slot.val)) := by
  have havailable : inputWidth + slot.val <
      2 ^ referenceWidth inputWidth gateBound :=
    lt_of_lt_of_le (Nat.add_lt_add_left slot.isLt inputWidth)
      (inputWidth_add_gateBound_le_two_pow_referenceWidth
        inputWidth gateBound)
  rw [slotWellFormed]
  simp only [BoolFormula.eval]
  rw [eval_referenceBelow_internal slot true
      (inputWidth + slot.val) code havailable,
    eval_referenceBelow_internal slot false
      (inputWidth + slot.val) code havailable]
  simp [GateSlot.WellFormedAt, ← Bool.decide_and]

theorem eval_slotValid_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (code : BitString (codeWidth inputWidth gateBound)) :
    (slotValid inputWidth gateBound slot).eval code.toTotal =
      decide
        ((slot.val < countValue code →
            (GateSlot.decode (slotBits code slot)).WellFormedAt
              (inputWidth + slot.val)) ∧
          (countValue code ≤ slot.val →
            GateSlot.decode (slotBits code slot) =
              GateSlot.zero (referenceWidth inputWidth gateBound))) := by
  have hminimum : slot.val + 1 < 2 ^ gateCountWidth gateBound :=
    lt_of_le_of_lt (Nat.succ_le_iff.mpr slot.isLt)
      (gateBound_lt_two_pow_gateCountWidth gateBound)
  rw [slotValid]
  simp only [BoolFormula.eval]
  rw [eval_countAtLeast_internal (slot.val + 1) code hminimum,
    eval_slotWellFormed_internal slot code,
    eval_slotZero_internal slot code]
  by_cases hactive : slot.val < countValue code
  · have hminimum' : slot.val + 1 ≤ countValue code := by omega
    have hinactive : ¬countValue code ≤ slot.val := by omega
    simp [hactive, hminimum', hinactive]
  · have hminimum' : ¬slot.val + 1 ≤ countValue code := by omega
    have hinactive : countValue code ≤ slot.val := by omega
    simp [hactive, hminimum', hinactive]

theorem eval_wellFormed_internal (inputWidth gateBound : Nat)
    (code : BitString (codeWidth inputWidth gateBound)) :
    (wellFormed inputWidth gateBound).eval code.toTotal =
      decide (EncodedWellFormed code) := by
  have hone : 1 < 2 ^ gateCountWidth gateBound :=
    Nat.one_lt_two_pow (by
      have := one_le_gateCountWidth gateBound
      omega)
  have hbound : gateBound < 2 ^ gateCountWidth gateBound :=
    gateBound_lt_two_pow_gateCountWidth gateBound
  have hslots :
      (BoolFormula.conjs <| List.ofFn fun slot : Fin gateBound =>
        slotValid inputWidth gateBound slot).eval code.toTotal =
      decide (∀ slot : Fin gateBound,
        (slot.val < countValue code →
            (GateSlot.decode (slotBits code slot)).WellFormedAt
              (inputWidth + slot.val)) ∧
          (countValue code ≤ slot.val →
            GateSlot.decode (slotBits code slot) =
              GateSlot.zero (referenceWidth inputWidth gateBound))) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq,
      BoolFormula.eval_conjs, List.all_eq_true,
      List.forall_mem_ofFn_iff]
    simp only [eval_slotValid_internal, decide_eq_true_eq]
  rw [wellFormed]
  simp only [BoolFormula.eval]
  rw [eval_countAtLeast_internal 1 code hone,
    eval_countAtMost_internal gateBound code hbound, hslots]
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  unfold EncodedWellFormed
  unfold decode?
  by_cases hcount : countValue code < gateBound + 1
  · rw [dite_eq_left hcount]
    let description : Description inputWidth gateBound :=
      { gateCount := ⟨countValue code, hcount⟩
        slots := fun slot => GateSlot.decode (slotBits code slot) }
    change
      (1 ≤ countValue code ∧ countValue code ≤ gateBound ∧
          ∀ slot : Fin gateBound,
            (slot.val < countValue code →
                (GateSlot.decode (slotBits code slot)).WellFormedAt
                  (inputWidth + slot.val)) ∧
              (countValue code ≤ slot.val →
                GateSlot.decode (slotBits code slot) =
                  GateSlot.zero (referenceWidth inputWidth gateBound))) ↔
        description.WellFormed
    constructor
    · rintro ⟨hpositive, hcountBound, hslotsValid⟩
      refine ⟨by
        simp only [Description.Positive, Description.gateCountNat, description]
        omega, ?_, ?_⟩
      · intro index
        let slot : Fin gateBound :=
          ⟨index.val, lt_of_lt_of_le index.isLt hcountBound⟩
        have hvalid := (hslotsValid slot).1 index.isLt
        simpa [Description.TopologicallyWellFormed,
          Description.activeSlot, Description.gateCountNat,
          description, slot] using hvalid
      · intro slot hinactive
        exact (hslotsValid slot).2 hinactive
    · rintro ⟨hpositive, htopological, hpadded⟩
      refine ⟨by
        exact hpositive, Nat.le_of_lt_succ hcount, ?_⟩
      intro slot
      constructor
      · intro hactive
        let index : Fin (countValue code) := ⟨slot.val, hactive⟩
        have hvalid := htopological index
        simpa [Description.TopologicallyWellFormed,
          Description.activeSlot, Description.gateCountNat,
          description, index] using hvalid
      · intro hinactive
        exact hpadded slot hinactive
  · rw [dite_eq_right hcount]
    constructor
    · rintro ⟨_, hcountBound, _⟩
      omega
    · exact False.elim

private theorem size_countAtLeast (inputWidth gateBound minimum : Nat) :
    (countAtLeast inputWidth gateBound minimum).size =
      15 * gateCountWidth gateBound + 1 := by
  unfold countAtLeast
  apply BoolFormula.size_unsignedLEOf
  · intro coordinate
    exact BoolFormula.size_ofBool_internal _
  · intro coordinate
    rfl

private theorem size_countAtMost (inputWidth gateBound maximum : Nat) :
    (countAtMost inputWidth gateBound maximum).size =
      15 * gateCountWidth gateBound + 1 := by
  unfold countAtMost
  apply BoolFormula.size_unsignedLEOf
  · intro coordinate
    rfl
  · intro coordinate
    exact BoolFormula.size_ofBool_internal _

private theorem size_referenceBelow (inputWidth gateBound : Nat)
    (slot : Fin gateBound) (first : Bool) (available : Nat) :
    (referenceBelow inputWidth gateBound slot first available).size =
      15 * referenceWidth inputWidth gateBound + 2 := by
  cases first with
  | false =>
      rw [referenceBelow]
      simp only [Bool.false_eq_true, ↓reduceIte, BoolFormula.size]
      have hcomparison := BoolFormula.size_unsignedLEOf
        (fun coordinate => BoolFormula.ofBool
          (GateSlot.referenceBits
            (referenceWidth inputWidth gateBound) available coordinate))
        (input1Bit inputWidth gateBound slot)
        (fun coordinate => BoolFormula.size_ofBool_internal _)
        (fun coordinate => rfl)
      rw [hcomparison]
  | true =>
      rw [referenceBelow]
      simp only [↓reduceIte, BoolFormula.size]
      have hcomparison := BoolFormula.size_unsignedLEOf
        (fun coordinate => BoolFormula.ofBool
          (GateSlot.referenceBits
            (referenceWidth inputWidth gateBound) available coordinate))
        (input0Bit inputWidth gateBound slot)
        (fun coordinate => BoolFormula.size_ofBool_internal _)
        (fun coordinate => rfl)
      rw [hcomparison]

private theorem size_slotZero (inputWidth gateBound : Nat)
    (slot : Fin gateBound) :
    (slotZero inputWidth gateBound slot).size =
      15 * gateSlotWidth inputWidth gateBound + 1 := by
  unfold slotZero
  apply BoolFormula.size_unsignedLEOf
  · intro coordinate
    rfl
  · intro coordinate
    rfl

private theorem size_slotWellFormed (inputWidth gateBound : Nat)
    (slot : Fin gateBound) :
    (slotWellFormed inputWidth gateBound slot).size =
      30 * referenceWidth inputWidth gateBound + 5 := by
  rw [slotWellFormed]
  simp only [BoolFormula.size,
    size_referenceBelow inputWidth gateBound slot true,
    size_referenceBelow inputWidth gateBound slot false]
  omega

theorem size_slotValid_internal (inputWidth gateBound : Nat)
    (slot : Fin gateBound) :
    (slotValid inputWidth gateBound slot).size =
      slotValidSize inputWidth gateBound := by
  rw [slotValid]
  simp only [BoolFormula.size,
    size_countAtLeast inputWidth gateBound (slot.val + 1),
    size_slotWellFormed inputWidth gateBound slot,
    size_slotZero inputWidth gateBound slot]
  unfold slotValidSize
  omega

theorem size_wellFormed_internal (inputWidth gateBound : Nat) :
    (wellFormed inputWidth gateBound).size =
      wellFormedSize inputWidth gateBound := by
  have hsum :
      ((List.ofFn fun slot : Fin gateBound =>
        slotValid inputWidth gateBound slot).map
          (fun formula => formula.size + 1)).sum =
        gateBound * (slotValidSize inputWidth gateBound + 1) := by
    rw [List.map_ofFn]
    change
      (List.ofFn fun slot : Fin gateBound =>
        (slotValid inputWidth gateBound slot).size + 1).sum = _
    simp_rw [size_slotValid_internal]
    simp
  rw [wellFormed]
  simp only [BoolFormula.size,
    size_countAtLeast inputWidth gateBound 1,
    size_countAtMost inputWidth gateBound gateBound,
    BoolFormula.size_conjs, hsum]
  unfold wellFormedSize
  omega

private theorem vars_ofBool_empty (value : Bool) :
    (BoolFormula.ofBool value).vars = ∅ := by
  cases value <;> rfl

private theorem vars_countAtLeast_lt (inputWidth gateBound minimum : Nat) :
    ∀ wire ∈ (countAtLeast inputWidth gateBound minimum).vars,
      wire < codeWidth inputWidth gateBound := by
  unfold countAtLeast
  apply BoolFormula.vars_unsignedLEOf_lt_internal
  · intro coordinate wire hwire
    rw [vars_ofBool_empty] at hwire
    simp at hwire
  · intro coordinate wire hwire
    simp only [countBit, BoolFormula.vars, Finset.mem_singleton] at hwire
    subst wire
    exact (countCoordinate inputWidth gateBound coordinate).isLt

private theorem vars_countAtMost_lt (inputWidth gateBound maximum : Nat) :
    ∀ wire ∈ (countAtMost inputWidth gateBound maximum).vars,
      wire < codeWidth inputWidth gateBound := by
  unfold countAtMost
  apply BoolFormula.vars_unsignedLEOf_lt_internal
  · intro coordinate wire hwire
    simp only [countBit, BoolFormula.vars, Finset.mem_singleton] at hwire
    subst wire
    exact (countCoordinate inputWidth gateBound coordinate).isLt
  · intro coordinate wire hwire
    rw [vars_ofBool_empty] at hwire
    simp at hwire

private theorem vars_referenceBelow_lt (inputWidth gateBound : Nat)
    (slot : Fin gateBound) (first : Bool) (available : Nat) :
    ∀ wire ∈
        (referenceBelow inputWidth gateBound slot first available).vars,
      wire < codeWidth inputWidth gateBound := by
  cases first with
  | false =>
      simp only [referenceBelow, Bool.false_eq_true, ↓reduceIte,
        BoolFormula.vars]
      apply BoolFormula.vars_unsignedLEOf_lt_internal
      · intro coordinate wire hwire
        rw [vars_ofBool_empty] at hwire
        simp at hwire
      · intro coordinate wire hwire
        simp only [input1Bit, slotBit, BoolFormula.vars,
          Finset.mem_singleton] at hwire
        subst wire
        exact (slotCoordinate inputWidth gateBound slot
          (input1Coordinate inputWidth gateBound coordinate)).isLt
  | true =>
      simp only [referenceBelow, ↓reduceIte, BoolFormula.vars]
      apply BoolFormula.vars_unsignedLEOf_lt_internal
      · intro coordinate wire hwire
        rw [vars_ofBool_empty] at hwire
        simp at hwire
      · intro coordinate wire hwire
        simp only [input0Bit, slotBit, BoolFormula.vars,
          Finset.mem_singleton] at hwire
        subst wire
        exact (slotCoordinate inputWidth gateBound slot
          (input0Coordinate inputWidth gateBound coordinate)).isLt

private theorem vars_slotZero_lt (inputWidth gateBound : Nat)
    (slot : Fin gateBound) :
    ∀ wire ∈ (slotZero inputWidth gateBound slot).vars,
      wire < codeWidth inputWidth gateBound := by
  unfold slotZero
  apply BoolFormula.vars_unsignedLEOf_lt_internal
  · intro coordinate wire hwire
    simp only [slotBit, BoolFormula.vars, Finset.mem_singleton] at hwire
    subst wire
    exact (slotCoordinate inputWidth gateBound slot coordinate).isLt
  · intro coordinate wire hwire
    simp [BoolFormula.vars] at hwire

private theorem vars_slotWellFormed_lt (inputWidth gateBound : Nat)
    (slot : Fin gateBound) :
    ∀ wire ∈ (slotWellFormed inputWidth gateBound slot).vars,
      wire < codeWidth inputWidth gateBound := by
  intro wire hwire
  simp only [slotWellFormed, BoolFormula.vars, Finset.mem_union] at hwire
  rcases hwire with hwire | hwire
  · exact vars_referenceBelow_lt inputWidth gateBound slot true
      (inputWidth + slot.val) wire hwire
  · exact vars_referenceBelow_lt inputWidth gateBound slot false
      (inputWidth + slot.val) wire hwire

private theorem vars_slotValid_lt (inputWidth gateBound : Nat)
    (slot : Fin gateBound) :
    ∀ wire ∈ (slotValid inputWidth gateBound slot).vars,
      wire < codeWidth inputWidth gateBound := by
  intro wire hwire
  simp only [slotValid, BoolFormula.vars, Finset.mem_union] at hwire
  rcases hwire with (hwire | hwire) | (hwire | hwire)
  · exact vars_countAtLeast_lt inputWidth gateBound (slot.val + 1)
      wire hwire
  · exact vars_slotWellFormed_lt inputWidth gateBound slot wire hwire
  · exact vars_countAtLeast_lt inputWidth gateBound (slot.val + 1)
      wire hwire
  · exact vars_slotZero_lt inputWidth gateBound slot wire hwire

private theorem vars_conjs_lt (available : Nat)
    (formulas : List BoolFormula)
    (hformulas : ∀ formula ∈ formulas,
      ∀ wire ∈ formula.vars, wire < available) :
    ∀ wire ∈ (BoolFormula.conjs formulas).vars,
      wire < available := by
  induction formulas with
  | nil =>
      simp [BoolFormula.conjs, BoolFormula.vars]
  | cons formula formulas ih =>
      intro wire hwire
      simp only [BoolFormula.conjs, BoolFormula.vars,
        Finset.mem_union] at hwire
      rcases hwire with hwire | hwire
      · exact hformulas formula (by simp) wire hwire
      · apply ih
        · intro tail htail
          exact hformulas tail (by simp [htail])
        · exact hwire

theorem vars_wellFormed_lt_internal (inputWidth gateBound : Nat) :
    ∀ wire ∈ (wellFormed inputWidth gateBound).vars,
      wire < codeWidth inputWidth gateBound := by
  intro wire hwire
  simp only [wellFormed, BoolFormula.vars, Finset.mem_union] at hwire
  rcases hwire with hwire | hwire | hwire
  · exact vars_countAtLeast_lt inputWidth gateBound 1 wire hwire
  · exact vars_countAtMost_lt inputWidth gateBound gateBound wire hwire
  · apply vars_conjs_lt (codeWidth inputWidth gateBound)
      (List.ofFn fun slot : Fin gateBound =>
        slotValid inputWidth gateBound slot)
    · intro formula hformula
      rw [List.mem_ofFn'] at hformula
      obtain ⟨slot, rfl⟩ := hformula
      exact vars_slotValid_lt inputWidth gateBound slot
    · exact hwire

theorem length_compileRaw_internal (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).length =
      wellFormedSize inputWidth gateBound := by
  rw [compileRaw, BoolFormula.length_compileRaw,
    size_wellFormed_internal]

theorem compileRaw_wellFormed_internal (inputWidth gateBound : Nat) :
    (compileRaw inputWidth gateBound).WellFormed
      (codeWidth inputWidth gateBound) := by
  constructor
  · intro hempty
    have hlength := length_compileRaw_internal inputWidth gateBound
    rw [hempty] at hlength
    simp only [List.length_nil] at hlength
    have hcountWidth := one_le_gateCountWidth gateBound
    unfold wellFormedSize at hlength
    omega
  · apply BoolFormula.topologicallyWellFormed_compileRaw
    exact vars_wellFormed_lt_internal inputWidth gateBound

theorem eval?_compileRaw_internal (inputWidth gateBound : Nat)
    (code : BitString (codeWidth inputWidth gateBound)) :
    (compileRaw inputWidth gateBound).eval? code.toList =
      some (decide (EncodedWellFormed code)) := by
  let wires := code.toList.toArray
  have hwiresSize : wires.size = codeWidth inputWidth gateBound := by
    simp [wires]
  have hwiresInput : ∀ wire < codeWidth inputWidth gateBound,
      wires[wire]? = some (code.toTotal wire) := by
    intro wire hwire
    simp [wires, BitString.toList, BitString.toTotal, hwire]
  obtain ⟨result, heval, _hresultSize, _hprefix, houtput⟩ :=
    BoolFormula.evalAux?_compileRaw
      (codeWidth inputWidth gateBound)
      (wellFormed inputWidth gateBound) code.toTotal wires
      hwiresSize hwiresInput
      (vars_wellFormed_lt_internal inputWidth gateBound)
  have heval' :
      RawCircuit.evalAux? (compileRaw inputWidth gateBound)
        code.toList.toArray = some result := by
    simpa [compileRaw, wires] using heval
  have hwell := compileRaw_wellFormed_internal inputWidth gateBound
  have hnonempty : (compileRaw inputWidth gateBound).isEmpty = false := by
    cases hraw : compileRaw inputWidth gateBound with
    | nil => exact (hwell.1 hraw).elim
    | cons gate gates => rfl
  have houtputIndex :
      code.toList.length + (compileRaw inputWidth gateBound).length - 1 =
        BoolFormula.rawOutputWire (codeWidth inputWidth gateBound)
          (wellFormed inputWidth gateBound) := by
    simp [BoolFormula.rawOutputWire, length_compileRaw_internal,
      size_wellFormed_internal]
  rw [RawCircuit.eval?]
  simp only [hnonempty, Bool.false_eq_true, ite_false, heval']
  rw [houtputIndex]
  change result[BoolFormula.rawOutputWire
      (codeWidth inputWidth gateBound)
      (wellFormed inputWidth gateBound)]? =
    some (decide (EncodedWellFormed code))
  rw [houtput]
  simpa using congrArg some
    (eval_wellFormed_internal inputWidth gateBound code)

end ValidityFormula

end Description

end FixedWidth

end CircuitCode

end Complexity
