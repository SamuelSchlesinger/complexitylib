/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PaddedLinePoints
public import Complexitylib.Algebraic.MassProduction.HighRate.BooleanRecovery

/-!
# Recovery by a fixed padded XOR fold

The circuit-friendly power-of-two scalar list has one invalid zero slot.
Masking that slot by false makes its Boolean sum exactly the punctured-line
sum in the high-rate code's recovery theorem.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.PaddedLinePoints

open scoped LinearAlgebra.Projectivization

/-- The underlying affine points, including the target, are all distinct. -/
theorem point_injective (positive : 0 < width)
    (target : Fin dimension → BinaryExtension width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :
    Function.Injective (point positive target direction) := by
  intro left right equal
  exact pointBits_injective positive target direction (congrArg (binaryExtensionVectorBits positive) equal)

/-- Every valid scalar slot is on the punctured line. -/
theorem point_mem_puncturedLine (positive : 0 < width)
    (target : Fin dimension → BinaryExtension width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (slot : Fin (2 ^ width)) (active : valid positive slot = true) :
    point positive target direction slot ∈ puncturedLine target direction := by
  exact (memPuncturedLine_iff _ _ _).mpr
    ⟨scalarAt positive slot, (valid_eq_true_iff positive slot).mp active, rfl⟩

/-- Zero-masked padded scalar summation equals punctured-line summation. -/
theorem sum_valid_points {Value : Type*} [AddCommMonoid Value]
    (positive : 0 < width) (target : Fin dimension → BinaryExtension width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (values : (Fin dimension → BinaryExtension width) → Value) :
    (∑ slot : Fin (2 ^ width), if valid positive slot then values (point positive target direction slot) else 0) =
      ∑ value ∈ puncturedLine target direction, values value := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun slot _ => point positive target direction slot)
  · intro slot member
    exact point_mem_puncturedLine positive target direction slot (Finset.mem_filter.mp member).2
  · intro left _ right _ equal
    exact point_injective positive target direction equal
  · intro value member
    obtain ⟨scalar, nonzero, same⟩ := (memPuncturedLine_iff target direction value).mp member
    obtain ⟨slot, equal⟩ := scalarAt_surjective positive scalar
    refine ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact (valid_eq_true_iff positive slot).mpr (equal ▸ nonzero)
    · simpa only [point, equal] using same
  · intro slot _
    rfl

/-- The padded Boolean fold recovers exactly the original requested source bit. -/
theorem booleanResourceRecovers
    {Source Suffix : Type*} (positive : 0 < width)
    (code : HighRate.LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ HighRate.InformationBit code copies)
    (function : Source → Suffix → Bool) (source : Source) (suffix : Suffix)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :
    (∑ slot : Fin (2 ^ width), if valid positive slot then
      HighRate.booleanResource positive code placement function (placement source).1
        (point positive (placement source).2.1.val direction slot) (placement source).2.2 suffix else false) =
      function source suffix := by
  have sumEq := sum_valid_points positive (placement source).2.1.val direction
    (fun value => HighRate.booleanResource positive code placement function (placement source).1
      value (placement source).2.2 suffix)
  simp only [Bool.zero_eq_false] at sumEq
  rw [sumEq]
  exact HighRate.booleanResourceRecovers positive code placement function source suffix direction

end Algebraic.MassProduction.Nonuniform.PaddedLinePoints
