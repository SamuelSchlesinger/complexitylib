/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Codec.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Internal
import Mathlib.Tactic.FinCases

/-!
# Fixed-width binary circuit-description codec -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace GateSlot

theorem decode_encode_internal {width : Nat}
    (slot : GateSlot width) :
    decode (encode slot) = slot := by
  cases slot
  rw [GateSlot.mk.injEq]
  simp [encode, decode, Fin.appendEquiv]
  funext index
  rw [← Fin.natAdd_eq_addNat width index]
  exact Fin.append_right _ _ index

theorem encode_decode_internal {width : Nat}
    (bits : BitString (3 + (width + width))) :
    encode (decode bits) = bits := by
  let blocks := (Fin.appendEquiv 3 (width + width)).symm bits
  let inputs := (Fin.appendEquiv width width).symm blocks.2
  change Fin.append ![blocks.1 0, blocks.1 1, blocks.1 2]
      (Fin.append inputs.1 inputs.2) = bits
  have hcontrol : ![blocks.1 0, blocks.1 1, blocks.1 2] = blocks.1 := by
    funext index
    fin_cases index <;> rfl
  rw [hcontrol]
  have hinputs : Fin.append inputs.1 inputs.2 = blocks.2 :=
    (Fin.appendEquiv width width).apply_symm_apply blocks.2
  rw [hinputs]
  exact (Fin.appendEquiv 3 (width + width)).apply_symm_apply bits

theorem encode_injective_internal {width : Nat} :
    Function.Injective (@encode width) :=
  Function.LeftInverse.injective decode_encode_internal

/-- Internal exact equivalence between gate slots and their fixed-width
binary words. -/
def codecEquivInternal (width : Nat) :
    GateSlot width ≃ BitString (3 + (width + width)) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode_internal
  right_inv := encode_decode_internal

end GateSlot

namespace Description

theorem countBits_encode_internal {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    countBits (encode description) =
      GateSlot.referenceBits (gateCountWidth gateBound)
        description.gateCountNat := by
  simp [countBits, encode, Fin.appendEquiv]

theorem slotBits_encode_internal {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (slot : Fin gateBound) :
    slotBits (encode description) slot =
      GateSlot.encode (description.slots slot) := by
  funext coordinate
  let body : BitString
      (gateBound * gateSlotWidth inputWidth gateBound) :=
    fun flatCoordinate =>
      let position := finProdFinEquiv.symm flatCoordinate
      GateSlot.encode (description.slots position.1) position.2
  have hsplit :
      ((Fin.appendEquiv (gateCountWidth gateBound)
        (gateBound * gateSlotWidth inputWidth gateBound)).symm
          (encode description)).2 = body := by
    simp [encode, body, Fin.appendEquiv]
  change
    ((Fin.appendEquiv (gateCountWidth gateBound)
      (gateBound * gateSlotWidth inputWidth gateBound)).symm
        (encode description)).2 (finProdFinEquiv (slot, coordinate)) = _
  rw [hsplit]
  change
    GateSlot.encode
      (description.slots
        (finProdFinEquiv.symm (finProdFinEquiv (slot, coordinate))).1)
      (finProdFinEquiv.symm (finProdFinEquiv (slot, coordinate))).2 = _
  rw [finProdFinEquiv.symm_apply_apply]

theorem countValue_encode_internal {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    countValue (encode description) = description.gateCountNat := by
  unfold countValue
  rw [countBits_encode_internal,
    GateSlot.toList_referenceBits_internal,
    Nat.fromBitsLE_toBitsLE_mod]
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt description.gateCountNat_le_gateBound
    (gateBound_lt_two_pow_gateCountWidth gateBound)

theorem decode?_encode_internal {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    decode? (encode description) = some description := by
  unfold decode?
  rw [countValue_encode_internal]
  have hcount : description.gateCountNat < gateBound + 1 :=
    description.gateCount.isLt
  rw [dite_eq_left hcount]
  congr 1
  rw [Description.mk.injEq]
  constructor
  · apply Fin.ext
    rfl
  · funext slot
    rw [slotBits_encode_internal]
    exact GateSlot.decode_encode_internal _

private theorem encode_decoded_of_countValue_lt
    {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound))
    (hcount : countValue code < gateBound + 1) :
    encode
        { gateCount := ⟨countValue code, hcount⟩
          slots := fun slot => GateSlot.decode (slotBits code slot) } =
      code := by
  let blocks :=
    (Fin.appendEquiv (gateCountWidth gateBound)
      (gateBound * gateSlotWidth inputWidth gateBound)).symm code
  have hcountBits :
      GateSlot.referenceBits (gateCountWidth gateBound) (countValue code) =
        blocks.1 := by
    change GateSlot.referenceBits (gateCountWidth gateBound)
      (Nat.fromBitsLE (countBits code).toList) = blocks.1
    have hsplit : countBits code = blocks.1 := rfl
    rw [hsplit, GateSlot.referenceBits_fromBitsLE_internal]
  have hslots :
      (fun flatCoordinate =>
        let position := finProdFinEquiv.symm flatCoordinate
        GateSlot.encode
          (GateSlot.decode (slotBits code position.1)) position.2) =
        blocks.2 := by
    funext flatCoordinate
    let position := finProdFinEquiv.symm flatCoordinate
    change GateSlot.encode
      (GateSlot.decode (slotBits code position.1)) position.2 =
        blocks.2 flatCoordinate
    erw [GateSlot.encode_decode_internal]
    unfold slotBits
    change blocks.2 (finProdFinEquiv (position.1, position.2)) =
      blocks.2 flatCoordinate
    have hposition : (position.1, position.2) = position := by
      cases position
      rfl
    exact congrArg blocks.2 <|
      (congrArg finProdFinEquiv hposition).trans
        (finProdFinEquiv.apply_symm_apply flatCoordinate)
  change
    Fin.append
      (GateSlot.referenceBits (gateCountWidth gateBound) (countValue code))
      (fun flatCoordinate =>
        let position := finProdFinEquiv.symm flatCoordinate
        GateSlot.encode
          (GateSlot.decode (slotBits code position.1)) position.2) = code
  rw [hcountBits, hslots]
  exact
    (Fin.appendEquiv (gateCountWidth gateBound)
      (gateBound * gateSlotWidth inputWidth gateBound)).apply_symm_apply code

theorem encode_eq_of_decode?_eq_some_internal
    {inputWidth gateBound : Nat}
    {code : BitString (codeWidth inputWidth gateBound)}
    {description : Description inputWidth gateBound}
    (hdecode : decode? code = some description) :
    encode description = code := by
  unfold decode? at hdecode
  split at hdecode
  · have hdescription := Option.some.inj hdecode
    rw [← hdescription]
    exact encode_decoded_of_countValue_lt code _
  · contradiction

theorem decode?_eq_some_iff_internal
    {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound))
    (description : Description inputWidth gateBound) :
    decode? code = some description ↔ encode description = code := by
  constructor
  · exact encode_eq_of_decode?_eq_some_internal
  · intro hencode
    rw [← hencode]
    exact decode?_encode_internal description

theorem encode_injective_internal {inputWidth gateBound : Nat} :
    Function.Injective
      (@encode inputWidth gateBound) := by
  intro first second hequal
  have hfirst := decode?_encode_internal first
  have hsecond := decode?_encode_internal second
  rw [hequal, hsecond] at hfirst
  exact Option.some.inj hfirst.symm

end Description

end FixedWidth

end CircuitCode

end Complexity
