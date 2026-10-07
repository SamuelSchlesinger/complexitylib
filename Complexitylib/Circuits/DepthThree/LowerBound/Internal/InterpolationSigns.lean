/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraBits
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.InterpolationEvaluation

/-!
# Unrestricted depth-three lower bound: interpolation signs

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/InterpolationSigns.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound
namespace Interpolation

open BinaryAlgebra

variable {F : Type uDepth1} {ι : Type uDepth2}
variable [Field F] [Module F2 F]

/-- Read a Boolean coordinate of polynomial evaluation. -/
def bitEval (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F) :
    (Fin t → F) →+ (ι → F2) where
  toFun β i := ell (coeffEval t a β i)
  map_zero' := by
    funext i
    simp only [map_zero, Pi.zero_apply]
  map_add' β γ := by
    funext i
    simp only [map_add, Pi.add_apply]

@[simp] theorem bitEval_apply (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) (i : ι) :
    bitEval ell t a β i = ell (∑ j : Fin t, β j * a i ^ (j : ℕ)) := rfl

theorem functional_surjective (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1) :
    Function.Surjective ell := by
  intro b
  refine ⟨b • (1 : F), ?_⟩
  simp only [map_smul, hOne, smul_eq_mul, mul_one]

theorem bitEval_surjective [Fintype ι] (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1)
    {t : ℕ} (a : ι → F) (hsize : Fintype.card ι ≤ t)
    (ha : Function.Injective a) : Function.Surjective (bitEval ell t a) := by
  intro b
  obtain ⟨β, hβ⟩ := coeffEval_surjective a hsize ha (fun i => b i • (1 : F))
  refine ⟨β, ?_⟩
  funext i
  change ell (coeffEval t a β i) = b i
  rw [hβ]
  simp only [map_smul, hOne, smul_eq_mul, mul_one]

/-- Express polynomial coefficients as Boolean bit blocks. -/
def coefficientBits (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) : ι → Bool :=
  fun i => fieldBit (bitEval ell t a β i)

/-- The acceptance bit extracted from polynomial evaluation. -/
def acceptEval (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) : ι → Bool :=
  fun i => !(coefficientBits ell t a β i)

@[simp] theorem acceptEval_eq_true (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) (i : ι) :
    acceptEval ell t a β i = true ↔
      ell (∑ j : Fin t, β j * a i ^ (j : ℕ)) = 0 := by
  simp [acceptEval, coefficientBits]

/-- The coefficient involution that complements the acceptance bit. -/
def complementEquiv (ι : Type uDepth3) : (ι → Bool) ≃ (ι → Bool) where
  toFun b i := !(b i)
  invFun b i := !(b i)
  left_inv b := by funext i; exact Bool.not_not (b i)
  right_inv b := by funext i; exact Bool.not_not (b i)

section Finite

variable [Fintype F] [Fintype ι] [DecidableEq ι]
variable (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1)
variable {t : ℕ} (a : ι → F) (hsize : Fintype.card ι ≤ t)
variable (ha : Function.Injective a)

include hOne hsize ha

theorem finiteAvg_bitEval (Φ : (ι → F2) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (bitEval ell t a β)) = finiteAvg Φ := by
  classical
  exact AlgebraFiniteFibers.finiteAvg_comp (bitEval ell t a)
    (bitEval_surjective ell hOne a hsize ha) Φ

theorem finiteAvg_coefficientBits (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (coefficientBits ell t a β)) =
      finiteAvg Φ := by
  calc
    finiteAvg (fun β : Fin t → F => Φ (coefficientBits ell t a β)) =
        finiteAvg (fun b : ι → F2 => Φ ((bitsEquivF2 ι).symm b)) :=
      finiteAvg_bitEval ell hOne a hsize ha
        (fun b : ι → F2 => Φ ((bitsEquivF2 ι).symm b))
    _ = finiteAvg Φ := finiteAvg_equiv (bitsEquivF2 ι).symm Φ

theorem finiteAvg_acceptEval (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (acceptEval ell t a β)) =
      finiteAvg Φ := by
  calc
    finiteAvg (fun β : Fin t → F => Φ (acceptEval ell t a β)) =
        finiteAvg (fun b : ι → Bool => Φ (complementEquiv ι b)) :=
      finiteAvg_coefficientBits ell hOne a hsize ha
        (fun b : ι → Bool => Φ (complementEquiv ι b))
    _ = finiteAvg Φ := finiteAvg_equiv (complementEquiv ι) Φ

end Finite

section FiberCounts

variable [Fintype F] [DecidableEq F] [Fintype ι]
variable (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1)
variable {t : ℕ} (a : ι → F) (hsize : Fintype.card ι ≤ t)
variable (ha : Function.Injective a)

include hOne hsize ha

omit [DecidableEq F] in
theorem card_bitEval_fiber_mul (b : ι → F2) :
    2 ^ Fintype.card ι *
      Fintype.card {β : Fin t → F // bitEval ell t a β = b} =
        Fintype.card F ^ t := by
  classical
  have hL := bitEval_surjective ell hOne a hsize ha
  have hcard := AlgebraFiniteFibers.card_eq_mul_card_kernel (bitEval ell t a) hL
  rw [← AlgebraFiniteFibers.card_fiber_eq (bitEval ell t a) hL b] at hcard
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using hcard.symm

omit [DecidableEq F] in
theorem card_bitEval_fiber {r : ℕ} (hr : 1 ≤ r)
    (hcard : Fintype.card F = 2 ^ r) (b : ι → F2) :
    Fintype.card {β : Fin t → F // bitEval ell t a β = b} =
      2 ^ (r * t - Fintype.card ι) := by
  have hn : Fintype.card ι ≤ r * t := calc
    Fintype.card ι ≤ t := hsize
    _ = 1 * t := (one_mul t).symm
    _ ≤ r * t := Nat.mul_le_mul_right t hr
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) _)
  calc
    2 ^ Fintype.card ι *
        Fintype.card {β : Fin t → F // bitEval ell t a β = b} =
        Fintype.card F ^ t := card_bitEval_fiber_mul ell hOne a hsize ha b
    _ = 2 ^ (r * t) := by rw [hcard, pow_mul]
    _ = 2 ^ (Fintype.card ι + (r * t - Fintype.card ι)) := by
      rw [Nat.add_sub_of_le hn]
    _ = 2 ^ Fintype.card ι * 2 ^ (r * t - Fintype.card ι) := pow_add _ _ _

end FiberCounts

theorem finiteAvg_acceptEval_finset [Fintype F] {Z : Type uDepth4} [DecidableEq Z]
    (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1) {t : ℕ} (a : Z → F)
    (s : Finset Z) (hsize : s.card ≤ t)
    (ha : Set.InjOn a (↑s : Set Z)) (Φ : (s → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (fun z : s => acceptEval ell t a β z)) =
      finiteAvg Φ := by
  classical
  apply finiteAvg_acceptEval ell hOne (fun z : s => a z)
    (by simpa only [Fintype.card_coe] using hsize)
  intro x y hxy
  exact Subtype.ext (ha x.property y.property hxy)

end Interpolation
end DepthThreeLowerBound

end

end Complexity
