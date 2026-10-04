/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.BadSeeds
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Sign estimates from conditional uniformity

A balanced Boolean observation has zero mean on a uniform output. Any
bounded statistic of the retained tag can multiply its sign without
changing that cancellation. The remaining error is bounded by the finite
absolute sum defining twice total variation. No positivity or normalization
of the original weights is needed for this calculation.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem balanced_sign_sum {Out : Type*} [Fintype Out]
    (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool) :
    ∑ o, uniformWeight Out o * (if bit o then (1 : ℝ) else -1) = 0 := by
  rw [← merging_sum_mapWeight_mul (uniformWeight Out) bit
    (fun b => if b then (1 : ℝ) else -1), balanced]
  norm_num [uniformWeight, Fintype.sum_bool]

theorem weightSign_mul_le_dist {Tag Out : Type*} [Fintype Tag] [Fintype Out]
    (p : Tag × Out → ℝ) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : Tag → ℝ) (bound : ∀ tag, |mask tag| ≤ 1) :
    |∑ z, p z * ((if bit z.2 then (1 : ℝ) else -1) * mask z.1)| ≤
      2 * weightDist p (uniformSecondWeight p) := by
  let f := fun z : Tag × Out => (if bit z.2 then (1 : ℝ) else -1) * mask z.1
  have zero : ∑ z, uniformSecondWeight p z * f z = 0 := by
    simp only [Fintype.sum_prod_type, uniformSecondWeight, uniformExtensionWeight, f]
    have row (tag : Tag) : ∑ o, firstWeight p tag * uniformWeight Out o *
        ((if bit o then (1 : ℝ) else -1) * mask tag) = 0 := by
      calc
        _ = firstWeight p tag *
            (∑ o, uniformWeight Out o * (if bit o then (1 : ℝ) else -1)) * mask tag := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro o _
          ring
        _ = 0 := by rw [balanced_sign_sum bit balanced]; ring
    simp only [row, Finset.sum_const_zero]
  have bounded (z : Tag × Out) : |f z| ≤ 1 := by
    dsimp only [f]
    cases bit z.2 <;> simpa using bound z.1
  have center : ∑ z, p z * f z = ∑ z, (p z - uniformSecondWeight p z) * f z := by
    simp only [sub_mul, Finset.sum_sub_distrib, zero, sub_zero]
  change |∑ z, p z * f z| ≤ _
  rw [center]
  calc
    |∑ z, (p z - uniformSecondWeight p z) * f z| ≤
        ∑ z, |(p z - uniformSecondWeight p z) * f z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, |p z - uniformSecondWeight p z| := by
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (bounded z) (abs_nonneg (p z - uniformSecondWeight p z))
    _ = 2 * weightDist p (uniformSecondWeight p) := by
      unfold weightDist
      ring

theorem weightSign_xor_le_dist {Tag Out : Type*} [Fintype Tag] [Fintype Out]
    (p : Tag × Out → ℝ) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : Tag → Bool) :
    |∑ z, p z * (if Bool.xor (bit z.2) (mask z.1) then (1 : ℝ) else -1)| ≤
      2 * weightDist p (uniformSecondWeight p) := by
  have sign (z : Tag × Out) :
      (if Bool.xor (bit z.2) (mask z.1) then (1 : ℝ) else -1) =
        (if bit z.2 then (1 : ℝ) else -1) * (if mask z.1 then (-1 : ℝ) else 1) := by
    cases bit z.2 <;> cases mask z.1 <;> norm_num
  simp_rw [sign]
  exact weightSign_mul_le_dist p bit balanced
    (fun tag => if mask tag then (-1 : ℝ) else 1) (by intro tag; cases mask tag <;> norm_num)

theorem mapWeight_uniform_bool_coordinate {M : Nat} (j : Fin M) :
    mapWeight (fun x : Fin M → Bool => x j) (uniformWeight (Fin M → Bool)) =
      uniformWeight Bool := by
  classical
  let Tail := {k : Fin M // k ≠ j} → Bool
  let e : (Fin M → Bool) ≃ Bool × Tail := Equiv.funSplitAt j Bool
  have uniform : mapWeight e (uniformWeight (Fin M → Bool)) =
      uniformWeight (Bool × Tail) := by
    funext z
    rw [mapWeight_equiv_apply]
    simp only [uniformWeight, Fintype.card_congr e]
  have positive : (Fintype.card Tail : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Tail)
  calc
    mapWeight (fun x : Fin M → Bool => x j) (uniformWeight (Fin M → Bool)) =
        mapWeight Prod.fst (mapWeight e (uniformWeight (Fin M → Bool))) := by
      rw [mapWeight_comp]
      rfl
    _ = mapWeight Prod.fst (uniformWeight (Bool × Tail)) := by rw [uniform]
    _ = uniformWeight Bool := by
      rw [mapWeight_fst]
      funext b
      simp only [firstWeight, uniformWeight, Fintype.card_prod, Nat.cast_mul,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem affineLeakage_sign_mul_le_of_not_mem_badSeeds {n d t : Nat}
    {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool)
    (good : y ∉ affineLeakageBadSeeds cb p leak advice γ)
    (b : Fin n → Bool) (ys : Fin t → Fin d → Bool) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : (Fin t → Out) → ℝ) (bound : ∀ outputs, |mask outputs| ≤ 1) :
    |∑ x, p x *
      ((if bit (cb (xorInput x b) (xorInput y (leak x none)) (advice none))
        then (1 : ℝ) else -1) *
        mask (fun i => cb (xorInput x b)
          (xorInput (ys i) (leak x (some i))) (advice (some i))))| ≤ 2 * γ := by
  have near := (not_mem_affineLeakageBadSeeds cb p leak advice γ y).mp good b ys
  have estimate := (weightSign_mul_le_dist
    (affineLeakageOutputWeight cb p leak advice b y ys) bit balanced mask bound).trans
      (mul_le_mul_of_nonneg_left near (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [affineLeakageOutputWeight, merging_sum_mapWeight_mul] using estimate

theorem affineLeakage_sign_le_of_not_mem_badSeeds {n d t : Nat}
    {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool)
    (good : y ∉ affineLeakageBadSeeds cb p leak advice γ)
    (b : Fin n → Bool) (ys : Fin t → Fin d → Bool) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : (Fin t → Out) → Bool) :
    |∑ x, p x *
      (if Bool.xor
        (bit (cb (xorInput x b) (xorInput y (leak x none)) (advice none)))
        (mask (fun i => cb (xorInput x b)
          (xorInput (ys i) (leak x (some i))) (advice (some i))))
        then (1 : ℝ) else -1)| ≤ 2 * γ := by
  have near := (not_mem_affineLeakageBadSeeds cb p leak advice γ y).mp good b ys
  have estimate := (weightSign_xor_le_dist
    (affineLeakageOutputWeight cb p leak advice b y ys) bit balanced mask).trans
      (mul_le_mul_of_nonneg_left near (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [affineLeakageOutputWeight, merging_sum_mapWeight_mul] using estimate

theorem affineLeakage_coordinate_sign_le_of_not_mem_badSeeds {n d t M : Nat}
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Fin M → Bool)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool)
    (good : y ∉ affineLeakageBadSeeds cb p leak advice γ)
    (b : Fin n → Bool) (ys : Fin t → Fin d → Bool) (j : Fin M)
    (mask : (Fin t → Fin M → Bool) → Bool) :
    |∑ x, p x *
      (if Bool.xor
        (cb (xorInput x b) (xorInput y (leak x none)) (advice none) j)
        (mask (fun i => cb (xorInput x b)
          (xorInput (ys i) (leak x (some i))) (advice (some i))))
        then (1 : ℝ) else -1)| ≤ 2 * γ :=
  affineLeakage_sign_le_of_not_mem_badSeeds cb p leak advice γ y good b ys
    (fun output => output j) (mapWeight_uniform_bool_coordinate j) mask

end Algebraic.Cutwidth.Extractor.Internal
