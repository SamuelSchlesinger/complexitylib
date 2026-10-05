/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Collisions
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Inversion.Components
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Features
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.LowerBound

/-!
# The actual nonlinear-feature budget for inversion circuits

Actual conjunction gate outputs generate every output modulo affine primary
functions. Their multiple-primary subfamily has quarter-biased marginals, so the
average-collision estimate charges these features as well as the circuit's
primary summaries. No independence, arity, depth, or reuse restriction is needed.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

open scoped BigOperators Classical
open Cutwidth.Aggregate.Geometry

/-- An inversion circuit's actual conjunction outputs pay an entropy charge for every
multiple-primary conjunction. -/
theorem input_add_feature_bias_le_conjunctionCount {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (c : Circuit signature n n) (computes : c.Computes interpretation (inverseFunction e)) :
    (n : ℝ) + multiCount c.program * Entropy.bitSaving - Real.log 5 / Real.log 2 ≤
      conjunctionCount c.program := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  let J := {i : Fin c.size // (c.program.lines i).op.isConjunction = true}
  let key (x : K) (j : J) := c.program.gateFunction interpretation j ((encode e).symm x)
  choose b L w representation using output_affine_conjunction_representation c
  let A : K →ₗ[ZMod 2] K :=
    e.toLinearMap.comp ((LinearMap.pi L).comp e.symm.toLinearMap)
  let a := e b
  let decode (h : J → Bool) := e (fun j => ∑ i, w j i * bitValue (h i))
  have represents (x : K) : x⁻¹ + A x + a = decode (key x) := by
    have coordinates : e.symm x⁻¹ = b + (LinearMap.pi L) (e.symm x) +
        (fun j => ∑ i, w j i * bitValue (key x i)) := by
      funext j
      have hj := representation j ((encode e).symm x)
      rw [computes, bitVector_decode] at hj
      simp only [inverseFunction, Equiv.apply_symm_apply] at hj
      change bitEquiv ((encode e).symm x⁻¹ j) = _ at hj
      rw [bitEquiv_decode] at hj
      exact hj
    have field := congrArg e coordinates
    simp only [map_add, LinearEquiv.apply_symm_apply] at field
    change x⁻¹ + e ((LinearMap.pi L) (e.symm x)) + e b =
      e (fun j => ∑ i, w j i * bitValue (key x i))
    rw [field]
    have cancel : ∀ u v z : K, (u + v + z) + v + u = z := by
      intro u v z
      calc
        (u + v + z) + v + u = (u + u) + (v + v) + z := by ac_rfl
        _ = z := by simp only [CharTwo.add_self_eq_zero, zero_add]
    exact cancel _ _ _
  let B : Finset J := Finset.univ.filter fun j => multiPrimary (c.program.lines j.val) = true
  have countJ : Fintype.card J = conjunctionCount c.program := Fintype.card_subtype _
  have countB : B.card = multiCount c.program := by
    rw [multiCount_eq_card_filter]
    have image : B.image Subtype.val =
        Finset.univ.filter fun j => multiPrimary (c.program.lines j) = true := by
      ext j
      constructor
      · intro h
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      · intro h
        have marked := (Finset.mem_filter.mp h).2
        have conjunction := ((multiPrimary_iff_exists_pair _).mp marked).1
        exact Finset.mem_image.mpr ⟨⟨j, conjunction⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, marked⟩, rfl⟩
    rw [← image, Finset.card_image_of_injective _ Subtype.val_injective]
  have quarter (j : J) : ∃ rare : Bool, multiPrimary (c.program.lines j.val) = true →
      4 * (Finset.univ.filter fun x : K => key x j = rare).card ≤ Fintype.card K := by
    by_cases marked : multiPrimary (c.program.lines j.val) = true
    · obtain ⟨rare, small⟩ := multiPrimary_quarter c.program j.val marked
      refine ⟨rare, fun _ => ?_⟩
      have cards := Fintype.card_congr ((encode e).symm.subtypeEquivOfSubtype
        (p := fun y => c.program.gateFunction interpretation j.val y = rare))
      have same : (Finset.univ.filter fun x : K => key x j = rare).card =
          Fintype.card {y : Fin n → Bool //
            c.program.gateFunction interpretation j.val y = rare} := by
        simpa only [Fintype.card_subtype] using cards
      rw [same, card_field e]
      exact small
    · exact ⟨false, fun h => (marked h).elim⟩
  choose rare bias using quarter
  have bound := log_card_le_of_inverse_features_and_bias key decode A.toAddMonoidHom a
    represents B rare (fun j hj => bias j (Finset.mem_filter.mp hj).2)
  rw [countJ, countB, card_field e] at bound
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at bound
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_left₀ logpos).mp
  rw [sub_mul, add_mul, Entropy.bitSaving, mul_assoc,
    div_mul_cancel₀ _ logpos.ne', div_mul_cancel₀ _ logpos.ne']
  linarith

/-- Charging actual nonlinear features and primary summaries strengthens the inversion
bound, with leading coefficient `(3 + 4c) / (2 + 2c)` for `c = 1 - H₂(1/4)`. -/
theorem feature_entropy_mul_size_lower_bound {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (c : Circuit signature n n)
    (computes : c.Computes interpretation (inverseFunction e)) :
    (3 + 4 * Entropy.bitSaving) * n - (Real.log 5 / Real.log 2 + 8 * Entropy.bitSaving) ≤
      (2 + 2 * Entropy.bitSaving) * c.size := by
  have out (i : Fin n) : c.outputFunction interpretation i = fun x => inverseFunction e x i := by
    funext x
    exact congrFun (computes x) i
  have same : c.eval interpretation = inverseFunction e := funext computes
  have bijective : Function.Bijective (c.eval interpretation) := by
    rw [same]
    exact inverseFunction_bijective e
  have nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j := by
    intro i j b
    rw [out]
    exact inverseFunction_nonliteral e dimension i j b
  have outputs := input_add_conjunctionCount_le_size_add_outputConjunctionCount c bijective
    (by intro i j; simpa using nonliteral i j false)
  have information := input_le_size_sub_outputConjunctionCount_sub_bias c bijective nonliteral
  have pairing := two_mul_input_le_size_add_multi_of_affine_restrictions (r := 2) c (by
    intro S affine
    exact card_flat_le_four e S (fun i => by simpa only [out i] using affine i))
  have features := input_add_feature_bias_le_conjunctionCount e c computes
  have counts : (n : ℝ) + conjunctionCount c.program ≤
      c.size + outputConjunctionCount c := by exact_mod_cast outputs
  have pairs : 2 * (n : ℝ) ≤ c.size + multiCount c.program + 4 := by
    exact_mod_cast pairing
  have positive := Entropy.bitSaving_pos
  nlinarith [mul_nonneg positive.le (sub_nonneg.mpr pairs)]

/-- The nonlinear-feature inequality in normalized gate-count form. -/
theorem featureCoefficient_mul_sub_penalty_le_size {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K)
    (dimension : 3 ≤ n) (c : Circuit signature n n)
    (computes : c.Computes interpretation (inverseFunction e)) :
    (3 + 4 * Entropy.bitSaving) / (2 + 2 * Entropy.bitSaving) * n -
        (Real.log 5 / Real.log 2 + 8 * Entropy.bitSaving) / (2 + 2 * Entropy.bitSaving) ≤
      c.size := by
  have bound := feature_entropy_mul_size_lower_bound e dimension c computes
  have positive : 0 < 2 + 2 * Entropy.bitSaving := by
    linarith [Entropy.bitSaving_pos]
  rw [div_mul_eq_mul_div, ← sub_div]
  exact (div_le_iff₀ positive).mpr (by simpa only [mul_comm] using bound)

end Algebraic.Aggregate.Geometry.Inversion
