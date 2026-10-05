/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted counting of biased Boolean messages

A product distribution assigns probability one quarter to the rare outcome of each
biased coordinate. Summing `log x ≤ x - 1` proves the usual entropy bound directly,
without assuming independence of the message coordinates.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical
open Finset

/-- A finite logarithmic mean bound, derived from the tangent inequality for `log`. -/
theorem sum_log_le_of_sum_le {X : Type*} [Fintype X] (f : X → ℝ)
    (positive : ∀ x, 0 < f x) {a : ℝ} (ha : 0 < a)
    (bound : ∑ x, f x ≤ Fintype.card X * a) :
    ∑ x, Real.log (f x) ≤ Fintype.card X * Real.log a := by
  have point (x : X) : Real.log (f x) - Real.log a ≤ f x / a - 1 := by
    simpa only [Real.log_div (positive x).ne' ha.ne'] using
      Real.log_le_sub_one_of_pos (div_pos (positive x) ha)
  have total := Finset.sum_le_sum (s := Finset.univ) fun x _ => point x
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, div_eq_mul_inv, ← Finset.sum_mul] at total
  have ratio : (∑ x, f x) / a ≤ Fintype.card X := (div_le_iff₀ ha).mpr bound
  rw [div_eq_mul_inv] at ratio
  linarith

/-- The natural-log saving supplied by a coordinate whose rare value has probability at most 1/4. -/
noncomputable def biasSaving : ℝ := Real.log 2 - Real.binEntropy (1 / 4)

/-- The probability assigned to one Boolean coordinate. -/
noncomputable def bitWeight (biased : Bool) (rare value : Bool) : ℝ :=
  if biased then if value = rare then 1 / 4 else 3 / 4 else 1 / 2

/-- Every one-bit outcome receives strictly positive weight. -/
@[simp] theorem bitWeight_pos (biased rare value : Bool) : 0 < bitWeight biased rare value := by
  unfold bitWeight
  split_ifs <;> norm_num

/-- The weights on both one-bit outcomes sum to one. -/
theorem sum_bitWeight (biased rare : Bool) : ∑ value, bitWeight biased rare value = 1 := by
  cases biased <;> cases rare <;> norm_num [Fintype.sum_bool, bitWeight]

/-- Product weights on all the bits of a message. -/
noncomputable def messageWeight {ι : Type*} [Fintype ι]
    (biased : ι → Bool) (rare : ι → Bool) (message : ι → Bool) : ℝ :=
  ∏ i, bitWeight (biased i) (rare i) (message i)

/-- Every full message receives strictly positive product weight. -/
@[simp] theorem messageWeight_pos {ι : Type*} [Fintype ι]
    (biased rare message : ι → Bool) : 0 < messageWeight biased rare message :=
  Finset.prod_pos fun _ _ => bitWeight_pos _ _ _

/-- The product weights form a probability mass on the message cube. -/
@[simp] theorem sum_messageWeight {ι : Type*} [Fintype ι]
    (biased rare : ι → Bool) : ∑ message, messageWeight biased rare message = 1 := by
  unfold messageWeight
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun i _ => sum_bitWeight _ _

/-- A key with fibres of size at most `K` pulls back a probability mass to mass at most `K`. -/
theorem sum_weight_key_le {X T : Type*} [Fintype X] [Fintype T]
    (key : X → T) (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t)
    (mass : ∑ t, weight t = 1) {K : Nat}
    (fibres : ∀ t, (Finset.univ.filter fun x => key x = t).card ≤ K) :
    ∑ x, weight (key x) ≤ K := by
  classical
  calc
    ∑ x, weight (key x) =
        ∑ t, ((Finset.univ.filter fun x => key x = t).card : ℝ) * weight t := by
      rw [← Finset.sum_fiberwise Finset.univ key (fun x => weight (key x))]
      apply Finset.sum_congr rfl
      intro t _
      rw [show (∑ x ∈ Finset.univ.filter (fun x => key x = t), weight (key x)) =
          ∑ _x ∈ Finset.univ.filter (fun x => key x = t), weight t by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]]
      simp
    _ ≤ ∑ t, (K : ℝ) * weight t := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast fibres t) (nonneg t)
    _ = K := by rw [← Finset.mul_sum, mass, mul_one]

/-- Bias gives a strictly positive saving over one unbiased bit. -/
theorem biasSaving_pos : 0 < biasSaving := by
  exact sub_pos.mpr (Real.binEntropy_lt_log_two.mpr (by norm_num))

/-- The total log weight of a biased coordinate is bounded using only its rare count. -/
theorem sum_log_bitWeight_ge {X : Type*} [Fintype X] (bit : X → Bool)
    (rare : Bool) (biased : Bool)
    (bias : biased = true →
      4 * (Finset.univ.filter fun x => bit x = rare).card ≤ Fintype.card X) :
    -(Fintype.card X : ℝ) * Real.log 2 +
        (if biased then Fintype.card X * biasSaving else 0) ≤
      ∑ x, Real.log (bitWeight biased rare (bit x)) := by
  cases biased with
  | false => simp [bitWeight, Real.log_inv]
  | true =>
    let R := (Finset.univ.filter fun x => bit x = rare).card
    have hb : (4 : ℝ) * R ≤ Fintype.card X := by exact_mod_cast bias rfl
    have logs : Real.log (1 / 4 : ℝ) ≤ Real.log (3 / 4 : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have point (x : X) : Real.log (bitWeight true rare (bit x)) =
        Real.log (3 / 4 : ℝ) + (if bit x = rare then (1 : ℝ) else 0) *
          (Real.log (1 / 4 : ℝ) - Real.log (3 / 4 : ℝ)) := by
      by_cases h : bit x = rare <;> simp [bitWeight, h]
    have total : (∑ x, Real.log (bitWeight true rare (bit x))) =
        Fintype.card X * Real.log (3 / 4 : ℝ) +
          R * (Real.log (1 / 4 : ℝ) - Real.log (3 / 4 : ℝ)) := by
      simp_rw [point]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp [R]
    have entropy : Real.binEntropy (1 / 4) =
        -(1 / 4 : ℝ) * Real.log (1 / 4 : ℝ) -
          (3 / 4 : ℝ) * Real.log (3 / 4 : ℝ) := by
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      norm_num [Real.negMulLog_def]
      ring
    rw [total]
    simp only [↓reduceIte, biasSaving, entropy]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr logs)]

/-- A product log weight charges every biased coordinate without assuming independence. -/
theorem sum_log_messageWeight_ge {X ι : Type*} [Fintype X] [Fintype ι]
    (key : X → (ι → Bool)) (biased : Finset ι) (rare : ι → Bool)
    (bias : ∀ i ∈ biased,
      4 * (Finset.univ.filter fun x => key x i = rare i).card ≤ Fintype.card X) :
    -(Fintype.card X : ℝ) * (Fintype.card ι * Real.log 2 -
      biased.card * biasSaving) ≤
      ∑ x, Real.log (messageWeight (fun i => decide (i ∈ biased)) rare (key x)) := by
  let tag (i : ι) : Bool := decide (i ∈ biased)
  let weight := messageWeight tag rare
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    sum_log_bitWeight_ge (fun x => key x i) (rare i) (tag i)
      (fun hi => bias i (by simpa [tag] using hi))
  have logs (x : X) : Real.log (weight (key x)) =
      ∑ i, Real.log (bitWeight (tag i) (rare i) (key x i)) :=
    Real.log_prod fun i _ => (bitWeight_pos _ _ _).ne'
  change -(Fintype.card X : ℝ) * (Fintype.card ι * Real.log 2 -
    biased.card * biasSaving) ≤ ∑ x, Real.log (weight (key x))
  simp_rw [logs]
  rw [Finset.sum_comm]
  convert hh using 1
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, tag, decide_eq_true_eq]
  rw [Finset.sum_ite_mem]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.univ_inter]
  ring

/-- A product distribution yields the exact entropy saving without independence assumptions. -/
theorem log_card_le_of_fibres_and_bias {X ι : Type*} [Fintype X] [Nonempty X]
    [Fintype ι] (key : X → (ι → Bool)) (biased : Finset ι) (rare : ι → Bool)
    {K : Nat} (hK : 0 < K)
    (fibres : ∀ message, (Finset.univ.filter fun x => key x = message).card ≤ K)
    (bias : ∀ i ∈ biased,
      4 * (Finset.univ.filter fun x => key x i = rare i).card ≤ Fintype.card X) :
    Real.log (Fintype.card X) ≤ Real.log K + Fintype.card ι * Real.log 2 -
      biased.card * biasSaving := by
  let tag (i : ι) : Bool := decide (i ∈ biased)
  let weight := messageWeight tag rare
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have mass := sum_weight_key_le (X := X) (T := ι → Bool) (K := K) key weight
    (fun m => (messageWeight_pos tag rare m).le) (sum_messageWeight tag rare) (fun t => by
      convert fibres t using 1
      congr 1
      ext x
      simp only [Finset.mem_filter])
  have upper := sum_log_le_of_sum_le (fun x => weight (key x))
    (fun x => messageWeight_pos tag rare _) (div_pos hKR hN)
    (by simpa only [mul_div_cancel₀ _ hN.ne'] using mass)
  have lower := sum_log_messageWeight_ge key biased rare bias
  rw [Real.log_div hKR.ne' hN.ne'] at upper
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
