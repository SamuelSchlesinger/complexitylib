/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Direction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.FieldMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.RestrictionRank
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic.LinearCombination

/-!
# Affine restrictions of binary-field multiplication

A nonzero component `ℓ(xy)` of multiplication is a quadratic form on the `2n`-dimensional
input space. It is affine on `a + U` exactly when `U` is totally isotropic for its polar
form `B((x, y), (x', y')) = ℓ(xy' + x'y)`. This form is nondegenerate, because
`t ↦ ℓ(xt)` is nonzero whenever `x ≠ 0`. Totally isotropic subspaces therefore have
dimension at most `n`, so no nonzero component is affine on a flat with `2^(n+1)`
points.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.FieldMul

open Cutwidth.MultiOutput

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {n : ℕ}

/-- The first factor encoded by the first `n` prime-field inputs. -/
noncomputable def firstFactor (b : Module.Basis (Fin n) (ZMod 2) K) :
    (Fin (n + n) → ZMod 2) →ₗ[ZMod 2] K :=
  b.equivFun.symm.toLinearMap ∘ₗ LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd n)

/-- The second factor encoded by the last `n` prime-field inputs. -/
noncomputable def secondFactor (b : Module.Basis (Fin n) (ZMod 2) K) :
    (Fin (n + n) → ZMod 2) →ₗ[ZMod 2] K :=
  b.equivFun.symm.toLinearMap ∘ₗ LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd n)

/-- Multiplication in coordinates multiplies the two encoded factors. -/
theorem fieldMul_eq (b : Module.Basis (Fin n) (ZMod 2) K) (v : Fin (n + n) → ZMod 2) :
    fieldMul b v = b.repr (firstFactor b v * secondFactor b v) := by
  funext i
  simp [fieldMul, firstFactor, secondFactor, LinearMap.funLeft_apply,
    Module.Basis.equivFun_symm_apply]

private theorem bitValue_decide : ∀ t : ZMod 2, bitValue (decide (t = 1)) = t := by decide

/-- The prime-field outputs of Boolean multiplication. -/
theorem bitValue_boolFieldMul (b : Module.Basis (Fin n) (ZMod 2) K) (z : Fin (n + n) → Bool)
    (i : Fin n) : bitValue (boolFieldMul b z i) =
      b.repr (firstFactor b (bitVector z) * secondFactor b (bitVector z)) i := by
  rw [boolFieldMul, bitValue_decide, fieldMul_eq]

/-- The encoded factors of concatenated coordinates. -/
theorem factors_append (b : Module.Basis (Fin n) (ZMod 2) K) (p q : Fin n → ZMod 2) :
    firstFactor b (Fin.append p q) = b.equivFun.symm p ∧
      secondFactor b (Fin.append p q) = b.equivFun.symm q := by
  constructor
  · change b.equivFun.symm (fun j => Fin.append p q (Fin.castAdd n j)) = _
    congr 1
    funext j
    exact Fin.append_left p q j
  · change b.equivFun.symm (fun j => Fin.append p q (Fin.natAdd n j)) = _
    congr 1
    funext j
    exact Fin.append_right p q j

/-- Both encoded factors vanish only at the zero vector. -/
theorem eq_zero_of_factors (b : Module.Basis (Fin n) (ZMod 2) K) {v : Fin (n + n) → ZMod 2}
    (first : firstFactor b v = 0) (second : secondFactor b v = 0) : v = 0 := by
  have left : (fun j => v (Fin.castAdd n j)) = 0 :=
    (LinearEquiv.map_eq_zero_iff b.equivFun.symm).mp first
  have right : (fun j => v (Fin.natAdd n j)) = 0 :=
    (LinearEquiv.map_eq_zero_iff b.equivFun.symm).mp second
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · exact congrFun left j
  · exact congrFun right j

/-- The polar form `B(u, w) = ℓ(x_u y_w + x_w y_u)` of the component `ℓ(xy)`. -/
noncomputable def polarForm (b : Module.Basis (Fin n) (ZMod 2) K) (ℓ : K →ₗ[ZMod 2] ZMod 2) :
    LinearMap.BilinForm (ZMod 2) (Fin (n + n) → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2)
    (fun u w => ℓ (firstFactor b u * secondFactor b w + firstFactor b w * secondFactor b u))
    (by
      intro u u' w
      rw [← map_add]
      congr 1
      simp only [map_add]
      ring)
    (by
      intro c u w
      rw [← map_smul]
      congr 1
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_add])
    (by
      intro u w w'
      rw [← map_add]
      congr 1
      simp only [map_add]
      ring)
    (by
      intro c u w
      rw [← map_smul]
      congr 1
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_add])

@[simp] theorem polarForm_apply (b : Module.Basis (Fin n) (ZMod 2) K)
    (ℓ : K →ₗ[ZMod 2] ZMod 2) (u w : Fin (n + n) → ZMod 2) :
    polarForm b ℓ u w =
      ℓ (firstFactor b u * secondFactor b w + firstFactor b w * secondFactor b u) := rfl

/-- A nonzero component makes the polar form nondegenerate. -/
theorem polarForm_ker_eq_bot (b : Module.Basis (Fin n) (ZMod 2) K) {ℓ : K →ₗ[ZMod 2] ZMod 2}
    (nonzero : ℓ ≠ 0) : LinearMap.ker (polarForm b ℓ) = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  have radical (w : Fin (n + n) → ZMod 2) :
      ℓ (firstFactor b u * secondFactor b w + firstFactor b w * secondFactor b u) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hu) w
  have vanish {x : K} (hx : ∀ t, ℓ (x * t) = 0) : x = 0 := by
    by_contra ne
    apply nonzero
    ext s
    simpa [mul_inv_cancel_left₀ ne] using hx (x⁻¹ * s)
  have first : firstFactor b u = 0 := by
    apply vanish
    intro t
    have := radical (Fin.append 0 (b.equivFun t))
    rw [(factors_append b 0 (b.equivFun t)).1, (factors_append b 0 (b.equivFun t)).2] at this
    simpa using this
  have second : secondFactor b u = 0 := by
    apply vanish
    intro t
    have := radical (Fin.append (b.equivFun t) 0)
    rw [(factors_append b (b.equivFun t) 0).1, (factors_append b (b.equivFun t) 0).2] at this
    simpa [mul_comm] using this
  exact (Submodule.mem_bot _).mpr (eq_zero_of_factors b first second)

variable [CharP K 2] in
/-- A component `ℓ(xy)` preserving ternary sums at `a + u`, `a`, `a + w` vanishes on the
polar form at `(u, w)`. -/
theorem polar_eq_zero_of_affine (ℓ : K →ₗ[ZMod 2] ZMod 2) {A P R A' P' R' : K}
    (affine : ℓ ((A + P + A + (A + R)) * (A' + P' + A' + (A' + R'))) =
      ℓ ((A + P) * (A' + P')) + ℓ (A * A') + ℓ ((A + R) * (A' + R'))) :
    ℓ (P * R' + R * P') = 0 := by
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  have expand : (A + P + A + (A + R)) * (A' + P' + A' + (A' + R')) =
      (A + P) * (A' + P') + A * A' + (A + R) * (A' + R') + (P * R' + R * P') := by
    linear_combination (3 * A * A' + A * P' + A * R' + P * A' + R * A') * two
  rw [expand, map_add, map_add, map_add] at affine
  exact add_eq_left.mp affine

/-- No nonzero component of binary-field multiplication is affine on a flat with
`2^(n+1)` points. -/
theorem nonaffineOnFlats_boolFieldMul (b : Module.Basis (Fin n) (ZMod 2) K) :
    NonaffineOnFlats (boolFieldMul b) (n + 1) := by
  classical
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  intro S large w affine
  let ℓ : K →ₗ[ZMod 2] ZMod 2 := ∑ i, w i • b.coord i
  have component (z : Fin (n + n) → Bool) : ∑ i, w i * bitValue (boolFieldMul b z i) =
      ℓ (firstFactor b (bitVector z) * secondFactor b (bitVector z)) := by
    simp only [bitValue_boolFieldMul, ℓ, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, smul_eq_mul]
  suffices zero : ℓ = 0 by
    funext i
    have hi := LinearMap.congr_fun zero (b i)
    simpa [ℓ, Module.Basis.coord_apply, Finsupp.single_apply] using hi
  by_contra nonzero
  obtain ⟨a, U, card, mem⟩ := S.exists_direction
  obtain ⟨y₀, hy₀, base⟩ := mem 0 U.zero_mem
  rw [add_zero] at base
  have isotropic : U ≤ (polarForm b ℓ).orthogonal U := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    obtain ⟨x, hx, hxa⟩ := mem u hu
    obtain ⟨z, hz, hza⟩ := mem v hv
    have identity := affine x hx y₀ hy₀ z hz
    simp only [component, bitVector_xorThree, hxa, base, hza, map_add] at identity
    exact polar_eq_zero_of_affine ℓ identity
  have total := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := polarForm b ℓ) U
  rw [polarForm_ker_eq_bot b nonzero, inf_bot_eq, finrank_bot, add_zero,
    Module.finrank_fin_fun] at total
  have mono := Submodule.finrank_mono isotropic
  have exponent : n + 1 ≤ Module.finrank (ZMod 2) U :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (large.trans card.ge)
  omega

end Algebraic.Aggregate.Geometry.FieldMul
