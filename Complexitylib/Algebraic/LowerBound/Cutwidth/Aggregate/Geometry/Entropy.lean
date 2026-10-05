/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Collisions
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Averaging
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.OneWay

/-!
# Entropy savings from designated primary-input pairs

Averaging selects a coordinate partition that retains many designated pairs. Each
retained pair biases one bit of the actual one-way message. The small-fibre and
weighted-counting bounds then yield an exact finite communication inequality.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped Classical

/-- Pair averaging and exact message semantics imply the finite entropy inequality. -/
theorem input_le_bits_of_pair_summaries {n a K : Nat} {f : Cslib.BooleanFunction n}
    (ha : 2 ≤ a) (han : a ≤ n) (hK : 0 < K)
    (free : RectangleFree f K) (freeNot : RectangleFree (fun x => !(f x)) K)
    (large : 2 * K ≤ 2 ^ (n - a))
    {ι J : Type*} [Fintype ι] [Fintype J] (embed : J ↪ ι)
    (left right : J → Fin n) (distinct : ∀ j, left j ≠ right j)
    (summaries : ∀ U : Finset (Fin n), OneWaySummary f U (ι → Bool))
    (rare : ι → Bool)
    (bias : ∀ U : Finset (Fin n), ∀ j, left j ∈ U → right j ∈ U →
      4 * (Finset.univ.filter fun x => (summaries U).key x (embed j) = rare (embed j)).card ≤
        2 ^ U.card) :
    (n : ℝ) ≤ Fintype.card ι + (n - a : Nat) + Real.logb 2 K -
      (((a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1))) * Fintype.card J) * bitSaving := by
  obtain ⟨U, hU, pairs⟩ := exists_subset_pair_ratio ha han left right distinct
  let good := Finset.univ.filter fun j => left j ∈ U ∧ right j ∈ U
  let biased := good.image embed
  have cardinal : biased.card = good.card := Finset.card_image_of_injective _ embed.injective
  have complement : Uᶜ.card = n - a := by rw [Finset.card_compl, Fintype.card_fin, hU]
  have bound := input_le_bits_of_biased_oneWay hK free freeNot U
    (by simpa only [complement] using large) (summaries U) biased rare (by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact bias U j (Finset.mem_filter.mp hj).2.1 (Finset.mem_filter.mp hj).2.2)
  rw [cardinal, complement] at bound
  have savings := mul_le_mul_of_nonneg_right pairs bitSaving_pos.le
  dsimp only [good] at bound
  linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
