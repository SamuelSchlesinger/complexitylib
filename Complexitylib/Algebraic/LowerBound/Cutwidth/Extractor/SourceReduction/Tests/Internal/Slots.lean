/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Function.Basic

/-!
# Embedding a small test into the fixed tampering slots

The honest call is removed from the Cartesian product of the tested
coordinates with all candidates. At most `4 * C - 1` calls remain. An
embedding places these calls in the fixed slot type; a partial inverse
fills every unused slot with a caller-supplied padding value.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

/-- Change the first advice bit, preserving every remaining bit. -/
def affineTestDummyAdvice : List Bool → List Bool
  | [] => []
  | b :: bs => (!b) :: bs

theorem affineTestDummyAdvice_length (advice : List Bool) :
    (affineTestDummyAdvice advice).length = advice.length := by
  cases advice <;> rfl

theorem affineTestDummyAdvice_ne (advice : List Bool) (positive : 0 < advice.length) :
    advice ≠ affineTestDummyAdvice advice := by
  cases advice with
  | nil => simp at positive
  | cons b bs => cases b <;> simp [affineTestDummyAdvice]

/-- Real calls except for the already chosen honest coordinate and candidate. -/
def affineTestOtherSlots {N C : Nat} (U : Finset (Fin N)) (j : Fin N) (z : Fin C) :
    Finset (Fin N × Fin C) :=
  (U.product Finset.univ).erase (j, z)

theorem affineTestOtherSlots_ne {N C : Nat} (U : Finset (Fin N)) (j : Fin N) (z : Fin C)
    (v : affineTestOtherSlots U j z) : v.1 ≠ (j, z) :=
  (Finset.mem_erase.mp v.2).1

theorem affineTestOtherSlots_card {N C : Nat} (U : Finset (Fin N))
    (small : U.card ≤ 4) (j : Fin N) (member : j ∈ U) (z : Fin C) :
    Fintype.card (affineTestOtherSlots U j z) ≤ Fintype.card (Fin (4 * C - 1)) := by
  rw [Fintype.card_coe (affineTestOtherSlots U j z), affineTestOtherSlots,
    Finset.card_erase_of_mem (show (j, z) ∈ U.product Finset.univ by simp [member])]
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_right C small) 1

theorem affineTestOtherSlots_prod {N C : Nat} (U : Finset (Fin N))
    (j : Fin N) (member : j ∈ U) (z : Fin C) (f : Fin N × Fin C → ℝ) :
    f (j, z) * (∏ v : affineTestOtherSlots U j z, f v) = ∏ i ∈ U, ∏ k, f (i, k) := by
  rw [Finset.prod_coe_sort]
  unfold affineTestOtherSlots
  rw [Finset.mul_prod_erase _ _ (show (j, z) ∈ U.product Finset.univ by simp [member])]
  exact Finset.prod_product _ _ _

/-- Extend the genuinely used slots by a fixed padding value. -/
noncomputable def affineTestPadded {ι α : Type*} {τ : Nat}
    (embedding : ι ↪ Fin τ) (real : ι → α) (padding : α) (i : Fin τ) : α :=
  (Function.partialInv embedding i).elim padding real

theorem affineTestPadded_apply {ι α : Type*} {τ : Nat}
    (embedding : ι ↪ Fin τ) (real : ι → α) (padding : α) (i : ι) :
    affineTestPadded embedding real padding (embedding i) = real i := by
  simp only [affineTestPadded, Function.partialInv_left embedding.injective, Option.elim_some]

theorem affineTestPadded_property {ι α : Type*} {τ : Nat}
    (embedding : ι ↪ Fin τ) (real : ι → α) (padding : α)
    (P : α → Prop) (used : ∀ i, P (real i)) (unused : P padding) (i : Fin τ) :
    P (affineTestPadded embedding real padding i) := by
  unfold affineTestPadded
  cases Function.partialInv embedding i with
  | none => exact unused
  | some v => exact used v

end Algebraic.Cutwidth.Extractor.Internal
