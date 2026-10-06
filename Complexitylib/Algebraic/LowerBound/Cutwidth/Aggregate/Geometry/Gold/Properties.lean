/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Gold.Encoding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.RestrictionRank

/-!
# Circuit hardness properties of the Gold map

All output coordinates of the encoded Gold map are simultaneously affine only on
flats of at most two points. In odd dimension `n`, no nonzero linear output
component is affine on a flat with at least `2^((n+3)/2)` points: its direction space
would be totally isotropic for the polar form, whose radical has dimension at most
one. In dimension at least three no output coordinate is a signed primary literal.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Gold

open Inversion (encode encode_xorThree bitEquiv_decode card_field)

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {n : ℕ}

private theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-- Every simultaneous affine restriction of the Gold map contains at most two points. -/
theorem card_flat_le_two (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (S : AffineFlat n)
    (affine : ∀ i, AffineOn S (fun x => goldFunction e x i)) : S.carrier.card ≤ 2 := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have small := card_le_two_of_cube_affine (S.carrier.image (encode e)) (by
    intro a ha b hb c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    rw [← encode_xorThree]
    have same : goldFunction e (xorThree x y z) =
        xorThree (goldFunction e x) (goldFunction e y) (goldFunction e z) := by
      funext i
      exact affine i x hx y hy z hz
    rw [← encode_goldFunction, same, encode_xorThree,
      encode_goldFunction, encode_goldFunction, encode_goldFunction])
  simpa only [Finset.card_image_of_injective _ (encode e).injective] using small

/-- In odd dimension, every nonzero linear component of the Gold map is nonaffine on
each flat with at least `2^((n+3)/2)` points. -/
theorem goldFunction_nonaffineOnFlats [Fintype K] (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (odd : Odd n) : NonaffineOnFlats (goldFunction e) ((n + 3) / 2) := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  intro S large w affine
  let L₀ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ i, w i • LinearMap.proj i
  let ℓ := L₀.comp e.symm.toLinearMap
  have component (x : Fin n → Bool) :
      ∑ i, w i * bitValue (goldFunction e x i) = ℓ (encode e x ^ 3) := by
    simp only [ℓ, L₀, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, LinearEquiv.coe_toLinearMap]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact bitEquiv_decode e _ i
  suffices zero : ℓ = 0 by
    funext i
    have hi := LinearMap.congr_fun zero (e (Pi.single i 1))
    simpa [ℓ, L₀, LinearMap.sum_apply, Pi.single_apply, Finset.sum_ite_eq'] using hi
  by_contra nonzero
  obtain ⟨x₀, hx₀⟩ := S.nonempty
  let a := encode e x₀
  have sum (u w : K) : (a + u) + a + (a + w) = a + (u + w) := by
    linear_combination a * two
  let U : Submodule (ZMod 2) K :=
    { carrier := {d | (encode e).symm (a + d) ∈ S.carrier}
      zero_mem' := by
        change (encode e).symm (a + 0) ∈ S.carrier
        simpa [a] using hx₀
      add_mem' := by
        intro u w hu hw
        change (encode e).symm (a + (u + w)) ∈ S.carrier
        have closed := S.closed _ hu x₀ hx₀ _ hw
        have same : xorThree ((encode e).symm (a + u)) x₀ ((encode e).symm (a + w)) =
            (encode e).symm (a + (u + w)) := by
          apply (encode e).injective
          rw [encode_xorThree, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
            Equiv.apply_symm_apply, sum]
        rwa [same] at closed
      smul_mem' := by
        intro c d hd
        change (encode e).symm (a + c • d) ∈ S.carrier
        rcases zmod_two_cases c with rfl | rfl
        · simpa [a] using hx₀
        · simpa using hd }
  have member (d : K) : d ∈ U ↔ (encode e).symm (a + d) ∈ S.carrier := Iff.rfl
  let points : U ≃ S.carrier :=
    { toFun := fun d => ⟨(encode e).symm (a + d), d.2⟩
      invFun := fun x => ⟨encode e x + a, by
        rw [member]
        have : a + (encode e x + a) = encode e x := by linear_combination a * two
        rw [this, Equiv.symm_apply_apply]
        exact x.2⟩
      left_inv := by
        rintro ⟨d, hd⟩
        apply Subtype.ext
        change encode e ((encode e).symm (a + d)) + a = d
        rw [Equiv.apply_symm_apply]
        linear_combination a * two
      right_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change (encode e).symm (a + (encode e x + a)) = x
        have : a + (encode e x + a) = encode e x := by linear_combination a * two
        rw [this, Equiv.symm_apply_apply] }
  have card : 2 ^ Module.finrank (ZMod 2) U = S.carrier.card := by
    rw [← Fintype.card_coe S.carrier, ← Nat.card_eq_fintype_card, ← Nat.card_congr points,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have isotropic : ∀ u ∈ U, ∀ w ∈ U, ℓ (u ^ 2 * w + u * w ^ 2) = 0 := by
    intro u hu w hw
    have identity := affine _ hu x₀ hx₀ _ hw
    simp only [component, encode_xorThree, Equiv.apply_symm_apply] at identity
    have base : encode e x₀ = a := rfl
    rw [base] at identity
    have product := map_product_eq_zero_of_cube_affine ℓ.toAddMonoidHom identity
    have expand : (a + u + a) * (a + (a + w)) * (a + w + (a + u)) = u ^ 2 * w + u * w ^ 2 := by
      linear_combination a * (u * w + (u + w) ^ 2 + 4 * a * (u + w) + 4 * a ^ 2) * two
    rw [expand] at product
    exact product
  have dimension := two_mul_finrank_le_of_isotropic ℓ nonzero (cube_injective_of_odd e odd)
    U isotropic
  have finrankK : Module.finrank (ZMod 2) K = n := by
    rw [← e.finrank_eq, Module.finrank_fin_fun]
  have exponent : (n + 3) / 2 ≤ Module.finrank (ZMod 2) U :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (large.trans card.ge)
  obtain ⟨k, rfl⟩ := odd
  omega

/-- In odd dimension at least three, no Gold output coordinate is a signed primary
literal. -/
theorem goldFunction_nonliteral [Fintype K] (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (odd : Odd n) (dimension : 3 ≤ n) (i j : Fin n) (b : Bool) :
    (fun x => goldFunction e x i) ≠ fun x => b ^^ x j := by
  intro same
  have large : 2 ^ ((n + 3) / 2) ≤ (AffineFlat.full n).carrier.card := by
    rw [AffineFlat.card_full]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have zero := goldFunction_nonaffineOnFlats e odd (AffineFlat.full n) large (Pi.single i 1) (by
    have literal : (fun x => ∑ k, (Pi.single i 1 : Fin n → ZMod 2) k *
        bitValue (goldFunction e x k)) = fun x => bitValue (b ^^ x j) := by
      funext x
      simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact congrArg bitValue (congrFun same x)
    rw [literal]
    exact affineOn_iff_mem_flatAffineFunctions.mp
      ((affineOn_coordinate j).unary fun t => b ^^ t))
  have := congrFun zero i
  simp at this

end Algebraic.Aggregate.Geometry.Gold
