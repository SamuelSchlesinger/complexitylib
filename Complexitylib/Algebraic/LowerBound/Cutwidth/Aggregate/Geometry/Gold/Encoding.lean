/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Gold.Field
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Properties

/-!
# The Gold map in Boolean coordinates

A linear coordinate equivalence `e : 𝔽₂ⁿ ≃ K` supplies an arbitrary basis of a binary
field `K`. The Gold map encodes its input with `e`, cubes it in `K`, and decodes all
`n` output bits in the same basis. When `n` is odd, three is coprime to `2^n - 1`, so
cubing and hence the encoded map are permutations.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Gold

open Inversion (encode encode_xorThree card_field)

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {n : ℕ}

/-- The Gold map `x ↦ x³` of a binary field, in the Boolean coordinates of `e`. -/
noncomputable def goldFunction (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (x : Fin n → Bool) : Fin n → Bool := (encode e).symm (encode e x ^ 3)

/-- Decoding the Gold map recovers exactly the field cube. -/
theorem encode_goldFunction (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (x : Fin n → Bool) :
    encode e (goldFunction e x) = encode e x ^ 3 :=
  (encode e).apply_symm_apply _

/-- In odd dimension, cubing is injective on the field. -/
theorem cube_injective_of_odd [Fintype K] (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (odd : Odd n) : Function.Injective fun x : K => x ^ 3 :=
  cube_injective (by rw [card_field e]; exact coprime_three_two_pow_sub_one odd)

/-- In odd dimension, the encoded Gold map is a permutation. -/
theorem goldFunction_bijective [Fintype K] (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (odd : Odd n) : Function.Bijective (goldFunction e) :=
  (encode e).symm.bijective.comp
    ((Finite.injective_iff_bijective.mp (cube_injective_of_odd e odd)).comp
      (encode e).bijective)

end Algebraic.Aggregate.Geometry.Gold
