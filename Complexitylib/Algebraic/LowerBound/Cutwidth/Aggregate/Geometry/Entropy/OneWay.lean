/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Fibres
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A one-way bit bound with biased coordinates

The two-sided rectangle obstruction bounds message fibres. Product-weight counting
then subtracts the exact binary-entropy deficit of every quarter-biased message bit.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped Classical

/-- The saving in bits from a coordinate with rare probability at most one quarter. -/
noncomputable def bitSaving : ℝ := biasSaving / Real.log 2

/-- A quarter-biased bit saves a strictly positive amount of information. -/
theorem bitSaving_pos : 0 < bitSaving :=
  div_pos biasSaving_pos (Real.log_pos (by norm_num))

/-- The saving is one minus the binary entropy in base two. -/
theorem bitSaving_eq : bitSaving = 1 - Real.binEntropy (1 / 4) / Real.log 2 := by
  rw [bitSaving, biasSaving, sub_div, div_self (Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num) (by norm_num))]

/-- Exact one-way communication bound, including a saving for each biased bit. -/
theorem input_le_bits_of_biased_oneWay {n K : Nat} {f : Cslib.BooleanFunction n}
    (hK : 0 < K) (free : RectangleFree f K)
    (freeNot : RectangleFree (fun x => !(f x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card)
    {ι : Type*} [Fintype ι] (summary : OneWaySummary f U (ι → Bool))
    (biased : Finset ι) (rare : ι → Bool)
    (bias : ∀ i ∈ biased,
      4 * (Finset.univ.filter fun x => summary.key x i = rare i).card ≤ 2 ^ U.card) :
    (n : ℝ) ≤ Fintype.card ι + Uᶜ.card + Real.logb 2 K - biased.card * bitSaving := by
  have bound := log_card_le_of_fibres_and_bias summary.key biased rare hK
    (fun message => by
      convert (card_fibre_lt_of_rectangleFree_both hK free freeNot U large
        summary message).le using 1
      congr 1
      ext x
      simp only [Finset.mem_filter]) (fun i hi => by simpa using bias i hi)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at bound
  have cards : (U.card : ℝ) + Uᶜ.card = n := by
    exact_mod_cast (show U.card + Uᶜ.card = n by simp)
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_left₀ logpos).mp
  have identity : ((Fintype.card ι : ℝ) + Uᶜ.card + Real.logb 2 K -
      biased.card * bitSaving) * Real.log 2 =
      ((Fintype.card ι : ℝ) + Uᶜ.card) * Real.log 2 + Real.log K -
        biased.card * biasSaving := by
    rw [Real.logb, bitSaving]
    field_simp
  rw [identity]
  nlinarith [bound]

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
