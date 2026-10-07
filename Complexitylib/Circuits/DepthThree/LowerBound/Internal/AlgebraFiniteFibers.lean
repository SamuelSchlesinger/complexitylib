/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Fintype.Card

/-!
# Unrestricted depth-three lower bound: algebra finite fibers

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/AlgebraFiniteFibers.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound.AlgebraFiniteFibers

variable {A : Type uDepth1} {B : Type uDepth2} [AddCommGroup A] [AddCommGroup B]

/-- Identify a nonempty fiber of a linear map with its kernel by translation. -/
def fiberEquivKernel (L : A →+ B) (hL : Function.Surjective L) (b : B) :
    {a : A // L a = b} ≃ {a : A // L a = 0} := by
  let x : A := Classical.choose (hL b)
  have hx : L x = b := Classical.choose_spec (hL b)
  exact {
    toFun := fun a => ⟨a.val - x, by rw [map_sub, a.property, hx, sub_self]⟩
    invFun := fun a => ⟨a.val + x, by rw [map_add, a.property, hx, zero_add]⟩
    left_inv := by
      intro a
      apply Subtype.ext
      exact sub_add_cancel a.val x
    right_inv := by
      intro a
      apply Subtype.ext
      exact add_sub_cancel_right a.val x
  }

variable [Fintype A] [instFintypeB : Fintype B] [instDecidableEqA : DecidableEq A] [DecidableEq B]

omit [Fintype B] [DecidableEq A] in
theorem card_fiber_eq
    {A : Type uDepth1}
    {B : Type uDepth2}
    [AddCommGroup A]
    [AddCommGroup B]
    [Fintype A]


    [DecidableEq B]
    (L : A →+ B) (hL : Function.Surjective L) (b : B) :
    Fintype.card {a : A // L a = b} = Fintype.card {a : A // L a = 0} :=
  Fintype.card_congr (fiberEquivKernel L hL b)
omit instFintypeB instDecidableEqA in
theorem card_filter_fiber_eq (L : A →+ B) (hL : Function.Surjective L) (b : B) :
    (Finset.univ.filter (fun a : A => L a = b)).card =
      (Finset.univ.filter (fun a : A => L a = 0)).card := by
  simpa only [Fintype.card_subtype] using card_fiber_eq L hL b

omit instDecidableEqA in
theorem card_eq_mul_card_kernel (L : A →+ B) (hL : Function.Surjective L) :
    Fintype.card A = Fintype.card B * Fintype.card {a : A // L a = 0} := by
  calc
    Fintype.card A = ∑ b : B, Fintype.card {a : A // L a = b} := by
      simpa using
        (Fintype.sum_fiberwise' (fun a : A => L a) (fun _ : B => (1 : ℕ))).symm
    _ = ∑ _b : B, Fintype.card {a : A // L a = 0} := by
      exact Finset.sum_congr rfl (fun b _ => card_fiber_eq L hL b)
    _ = Fintype.card B * Fintype.card {a : A // L a = 0} := by simp

omit instDecidableEqA in
theorem sum_comp (L : A →+ B) (hL : Function.Surjective L) (f : B → ℝ) :
    (∑ a : A, f (L a)) =
      (Fintype.card {a : A // L a = 0} : ℝ) * ∑ b : B, f b := by
  calc
    (∑ a : A, f (L a)) = ∑ b : B, ∑ _a : {a : A // L a = b}, f b :=
      (Fintype.sum_fiberwise' (fun a : A => L a) f).symm
    _ = ∑ b : B, (Fintype.card {a : A // L a = 0} : ℝ) * f b := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_fiber_eq L hL b]
    _ = (Fintype.card {a : A // L a = 0} : ℝ) * ∑ b : B, f b :=
      (Finset.mul_sum Finset.univ f _).symm

omit instDecidableEqA in
theorem finiteAvg_comp (L : A →+ B) (hL : Function.Surjective L) (f : B → ℝ) :
    finiteAvg (fun a : A => f (L a)) = finiteAvg f := by
  let : Nonempty {a : A // L a = 0} := ⟨⟨0, map_zero L⟩⟩
  have hk : (Fintype.card {a : A // L a = 0} : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card {a : A // L a = 0} ≠ 0)
  unfold finiteAvg
  rw [card_eq_mul_card_kernel L hL, Nat.cast_mul, sum_comp L hL f, mul_inv]
  calc
    (Fintype.card B : ℝ)⁻¹ * (Fintype.card {a : A // L a = 0} : ℝ)⁻¹ *
        ((Fintype.card {a : A // L a = 0} : ℝ) * ∑ b : B, f b) =
        (Fintype.card B : ℝ)⁻¹ *
          ((Fintype.card {a : A // L a = 0} : ℝ)⁻¹ *
            (Fintype.card {a : A // L a = 0} : ℝ)) * ∑ b : B, f b := by ring
    _ = (Fintype.card B : ℝ)⁻¹ * ∑ b : B, f b := by
      rw [inv_mul_cancel₀ hk, mul_one]

end DepthThreeLowerBound.AlgebraFiniteFibers

end

end Complexity
