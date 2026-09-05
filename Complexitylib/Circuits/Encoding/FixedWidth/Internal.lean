/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Defs
import Complexitylib.Classes.FiniteCounting

/-!
# Fixed-width binary circuit descriptions -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

theorem one_le_referenceWidth_internal (inputWidth gateBound : Nat) :
    1 ≤ referenceWidth inputWidth gateBound := by
  simp [referenceWidth]

theorem one_le_gateCountWidth_internal (gateBound : Nat) :
    1 ≤ gateCountWidth gateBound := by
  simp [gateCountWidth]

theorem inputWidth_add_gateBound_le_two_pow_referenceWidth_internal
    (inputWidth gateBound : Nat) :
    inputWidth + gateBound ≤ 2 ^ referenceWidth inputWidth gateBound := by
  calc
    inputWidth + gateBound ≤
        2 ^ Fin.bitWidth (inputWidth + gateBound) :=
      Nat.le_pow_clog Nat.one_lt_two _
    _ ≤ 2 ^ referenceWidth inputWidth gateBound := by
      exact Nat.pow_le_pow_right (by omega)
        (Nat.le_max_right 1 (Fin.bitWidth (inputWidth + gateBound)))

theorem gateBound_lt_two_pow_gateCountWidth_internal (gateBound : Nat) :
    gateBound < 2 ^ gateCountWidth gateBound := by
  have hcapacity : gateBound + 1 ≤
      2 ^ Fin.bitWidth (gateBound + 1) :=
    Nat.le_pow_clog Nat.one_lt_two _
  have hmono : 2 ^ Fin.bitWidth (gateBound + 1) ≤
      2 ^ gateCountWidth gateBound := by
    exact Nat.pow_le_pow_right (by omega)
      (Nat.le_max_right 1 (Fin.bitWidth (gateBound + 1)))
  omega

theorem card_gateSlot_internal (width : Nat) :
    Fintype.card (GateSlot width) = 2 ^ (3 + 2 * width) := by
  rw [Fintype.card_congr (gateSlotEquiv width)]
  simp only [Fintype.card_prod, Fintype.card_bool, card_finArrowBool]
  simp only [pow_add, pow_mul, Nat.reducePow]
  rw [show 2 * (2 * (2 * (2 ^ width * 2 ^ width))) =
      8 * (2 ^ width * 2 ^ width) by omega]
  change 8 * (2 ^ width * 2 ^ width) = 8 * (2 * 2) ^ width
  rw [mul_pow]

theorem card_description_internal (inputWidth gateBound : Nat) :
    Fintype.card (Description inputWidth gateBound) =
      (gateBound + 1) *
        2 ^ (gateBound * gateSlotWidth inputWidth gateBound) := by
  rw [Fintype.card_congr (descriptionEquiv inputWidth gateBound),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    card_gateSlot_internal]
  simp only [Fintype.card_fin]
  have hwidth :
      3 + 2 * referenceWidth inputWidth gateBound =
        gateSlotWidth inputWidth gateBound := by
    simp [gateSlotWidth]
    omega
  rw [hwidth]
  rw [← pow_mul]
  rw [Nat.mul_comm (gateSlotWidth inputWidth gateBound)]

namespace Description

theorem gateCountNat_le_gateBound_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.gateCountNat ≤ gateBound := by
  exact Nat.le_of_lt_succ description.gateCount.isLt

theorem length_toRawCircuit_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.toRawCircuit.length = description.gateCountNat := by
  simp [toRawCircuit]

@[simp] theorem getElem_toRawCircuit_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (index : Fin description.toRawCircuit.length) :
    description.toRawCircuit[index.val]'index.isLt =
      (description.activeSlot ⟨index.val, by
        have hindex := index.isLt
        simpa only [length_toRawCircuit_internal] using hindex⟩).toRawGate := by
  simp [toRawCircuit]

theorem topologicallyWellFormed_toRawCircuit_iff_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.toRawCircuit.TopologicallyWellFormed inputWidth ↔
      description.TopologicallyWellFormed := by
  unfold RawCircuit.TopologicallyWellFormed TopologicallyWellFormed
  constructor
  · intro h index
    let rawIndex : Fin description.toRawCircuit.length :=
      ⟨index.val, by
        simpa only [length_toRawCircuit_internal] using index.isLt⟩
    have hgate := h rawIndex
    simp only [List.get_eq_getElem, getElem_toRawCircuit_internal] at hgate
    exact hgate
  · intro h index
    let active : Fin description.gateCountNat :=
      ⟨index.val, by
        have hindex := index.isLt
        simpa only [length_toRawCircuit_internal] using hindex⟩
    have hslot := h active
    simp only [List.get_eq_getElem, getElem_toRawCircuit_internal]
    exact hslot

theorem wellFormed_toRawCircuit_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed) :
    description.toRawCircuit.WellFormed inputWidth := by
  constructor
  · intro hempty
    have hlength := congrArg List.length hempty
    have hpositive : 0 < description.gateCountNat := hdescription.1
    simp only [length_toRawCircuit_internal, List.length_nil] at hlength
    omega
  · exact
      (topologicallyWellFormed_toRawCircuit_iff_internal description).2
        hdescription.2.1

end Description

end FixedWidth

end CircuitCode

end Complexity
