/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.Code
public import Complexitylib.Algebraic.MassProduction.HighRate.Packing
public import Complexitylib.Algebraic.MassProduction.ResourcePacking

/-!
# Boolean packing and recovery for the high-rate code

An offline injection places source bits into the information coordinates of
several copies of the high-rate code. Each resource is an ordinary Boolean
function of the shorter suffix. Summing its selected basis coordinate along
a punctured line recovers the requested original Boolean value.

These are semantic recovery theorems. A circuit-size bound additionally
requires the runtime lookup, scheduling, and routing circuits.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators LinearAlgebra.Projectivization

/-- One information bit is identified by its code copy, information point,
and binary coordinate inside the field symbol. -/
abbrev InformationBit (code : LineCode (BinaryExtension width) (Fin dimension)) (copies : Nat) :=
  Fin copies × code.information × Fin width

/-- Fill unused information bits with false. The injection makes occupied
positions unambiguous. -/
noncomputable def informationBit
    {Source : Type*} (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (values : Source → Bool)
    (position : InformationBit code copies) : Bool := by
  classical
  exact if occupied : ∃ source, placement source = position then values (Classical.choose occupied)
    else false

/-- Every occupied position contains exactly its assigned source bit. -/
theorem informationBitAtPlacement
    {Source : Type*} (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (values : Source → Bool) (source : Source) :
    informationBit code placement values (placement source) = values source := by
  classical
  unfold informationBit
  rw [dite_eq_left ⟨source, rfl⟩]
  apply congrArg values
  apply placement.injective
  exact Classical.choose_spec (show ∃ candidate, placement candidate = placement source from ⟨source, rfl⟩)

/-- Pack one code copy's information symbols in the fixed binary basis. -/
noncomputable def informationMessage
    {Source : Type*} (widthPositive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (values : Source → Bool)
    (copy : Fin copies) : code.information → BinaryExtension width :=
  fun point => encodeBinaryExtension widthPositive
    (fun bit => informationBit code placement values (copy, point, bit))

/-- A Boolean resource function at one codeword coordinate and one basis bit. -/
noncomputable def booleanResource
    {Source Suffix : Type*} (widthPositive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (function : Source → Suffix → Bool)
    (copy : Fin copies) (point : Fin dimension → BinaryExtension width) (bit : Fin width)
    (suffix : Suffix) : Bool :=
  decodeBinaryExtension widthPositive
    (code.encode (informationMessage widthPositive code placement
      (fun source => function source suffix) copy) point) bit

/-- Each requested bit is the XOR of Boolean resource values on any
punctured recovery line through its information point. -/
theorem booleanResourceRecovers
    {Source Suffix : Type*} (widthPositive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (function : Source → Suffix → Bool)
    (source : Source) (suffix : Suffix)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :
    (∑ point ∈ puncturedLine (placement source).2.1.val direction,
      booleanResource widthPositive code placement function (placement source).1 point
        (placement source).2.2 suffix) = function source suffix := by
  classical
  let message := informationMessage widthPositive code placement
    (fun source => function source suffix) (placement source).1
  have recovered := congrArg
    (fun symbol => decodeBinaryExtension widthPositive symbol (placement source).2.2)
    (code.lineRecovery message (placement source).2.1.val direction)
  rw [code.systematic, decodeBinaryExtension_finset_sum] at recovered
  simp only [Finset.sum_apply] at recovered
  have informationValue : decodeBinaryExtension widthPositive (message (placement source).2.1)
      (placement source).2.2 = function source suffix := by
    dsimp only [message, informationMessage]
    rw [decodeBinaryExtension_encode]
    exact informationBitAtPlacement code placement (fun source => function source suffix) source
  rw [informationValue] at recovered
  exact recovered.symm

/-- Distinct requests with disjoint recovery lines cannot compete for a
resource in the same code copy. -/
theorem resourceIncidence_injective
    {K Request Copy : Type*} [Field K] [Finite K]
    (targets : Request → Fin dimension → K)
    (directions : Request → ℙ K (Fin dimension → K)) (copy : Request → Copy)
    (disjoint : ∀ left right, copy left = copy right → left ≠ right →
      Disjoint (puncturedLine (targets left) (directions left))
        (puncturedLine (targets right) (directions right))) :
    Function.Injective (fun incidence : Request × {scalar : K // scalar ≠ 0} =>
      (copy incidence.1, targets incidence.1 + incidence.2.val • (directions incidence.1).rep)) := by
  classical
  intro left right equal
  have sameCopy := congrArg Prod.fst equal
  have samePoint := congrArg Prod.snd equal
  change targets left.1 + left.2.val • (directions left.1).rep =
    targets right.1 + right.2.val • (directions right.1).rep at samePoint
  have onLine (incidence : Request × {scalar : K // scalar ≠ 0}) :
      targets incidence.1 + incidence.2.val • (directions incidence.1).rep ∈
        puncturedLine (targets incidence.1) (directions incidence.1) := by
    exact (memPuncturedLine_iff _ _ _).mpr ⟨incidence.2.val, incidence.2.property, rfl⟩
  have sameRequest : left.1 = right.1 := by
    by_contra different
    apply Finset.disjoint_left.mp (disjoint _ _ sameCopy different) (onLine left)
    rw [samePoint]
    exact onLine right
  apply Prod.ext sameRequest
  apply Subtype.ext
  apply smul_left_injective K (directions left.1).rep_nonzero
  apply add_left_cancel (a := targets left.1)
  simpa only [← sameRequest] using samePoint

end Algebraic.MassProduction.HighRate
