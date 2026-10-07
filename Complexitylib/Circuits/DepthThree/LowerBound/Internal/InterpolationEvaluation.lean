/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.LinearAlgebra.Lagrange
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraFiniteFibers

/-!
# Unrestricted depth-three lower bound: interpolation evaluation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/InterpolationEvaluation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Polynomial

namespace DepthThreeLowerBound
namespace Interpolation

variable {F : Type uDepth1} {ι : Type uDepth2}

/-- Evaluate a polynomial from its finite coefficient vector. -/
def coeffEval [CommSemiring F] (t : ℕ) (a : ι → F) :
    (Fin t → F) →ₗ[F] (ι → F) where
  toFun β i := ∑ j : Fin t, β j * a i ^ (j : ℕ)
  map_add' β γ := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c β := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]

@[simp] theorem coeffEval_apply [CommSemiring F] (t : ℕ) (a : ι → F)
    (β : Fin t → F) (i : ι) :
    coeffEval t a β i = ∑ j : Fin t, β j * a i ^ (j : ℕ) := rfl

theorem coeffEval_surjective [Field F] [Fintype ι] {t : ℕ} (a : ι → F)
    (hsize : Fintype.card ι ≤ t) (ha : Function.Injective a) :
    Function.Surjective (coeffEval t a) := by
  classical
  intro v
  let p : F[X] := Lagrange.interpolate Finset.univ a v
  have hinj : Set.InjOn a (↑(Finset.univ : Finset ι) : Set ι) :=
    fun _ _ _ _ hij => ha hij
  have hp : p ∈ Polynomial.degreeLT F (Fintype.card ι) := by
    apply Polynomial.mem_degreeLT.mpr
    simpa only [Finset.card_univ] using Lagrange.degree_interpolate_lt v hinj
  have hpt : p ∈ Polynomial.degreeLT F t := Polynomial.degreeLT_mono hsize hp
  refine ⟨Polynomial.degreeLTEquiv F t ⟨p, hpt⟩, ?_⟩
  funext i
  change (∑ j : Fin t,
    Polynomial.degreeLTEquiv F t ⟨p, hpt⟩ j * a i ^ (j : ℕ)) = v i
  rw [← Polynomial.eval_eq_sum_degreeLTEquiv hpt]
  exact Lagrange.eval_interpolate_at_node v hinj (Finset.mem_univ i)

section FiniteField

variable [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
variable {t : ℕ} (a : ι → F)
variable (hsize : Fintype.card ι ≤ t) (ha : Function.Injective a)

include hsize ha

theorem card_coeffEval_fiber_mul (v : ι → F) :
    Fintype.card F ^ Fintype.card ι *
      Fintype.card {β : Fin t → F // coeffEval t a β = v} =
        Fintype.card F ^ t := by
  classical
  let L := (coeffEval t a).toAddMonoidHom
  have hL : Function.Surjective L := coeffEval_surjective a hsize ha
  have hcard := AlgebraFiniteFibers.card_eq_mul_card_kernel L hL
  rw [← AlgebraFiniteFibers.card_fiber_eq L hL v] at hcard
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  simp only [Fintype.card_eq_nat_card] at hcard ⊢
  simpa only [L, LinearMap.toAddMonoidHom_coe] using hcard.symm

theorem card_coeffEval_fiber (v : ι → F) :
    Fintype.card {β : Fin t → F // coeffEval t a β = v} =
      Fintype.card F ^ (t - Fintype.card ι) := by
  apply Nat.eq_of_mul_eq_mul_left
    (pow_pos (Fintype.card_pos (α := F)) (Fintype.card ι))
  calc
    Fintype.card F ^ Fintype.card ι *
        Fintype.card {β : Fin t → F // coeffEval t a β = v} =
        Fintype.card F ^ t := card_coeffEval_fiber_mul a hsize ha v
    _ = Fintype.card F ^ (Fintype.card ι + (t - Fintype.card ι)) := by
      rw [Nat.add_sub_of_le hsize]
    _ = Fintype.card F ^ Fintype.card ι *
        Fintype.card F ^ (t - Fintype.card ι) := pow_add _ _ _

theorem finiteAvg_coeffEval (Φ : (ι → F) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (coeffEval t a β)) = finiteAvg Φ := by
  classical
  exact AlgebraFiniteFibers.finiteAvg_comp (coeffEval t a).toAddMonoidHom
    (coeffEval_surjective a hsize ha) Φ

end FiniteField

end Interpolation
end DepthThreeLowerBound

end

end Complexity
