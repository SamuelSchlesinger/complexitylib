/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Group.Nat.Even
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: language parameters

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageParameters.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- Use one fifth of the input length for data variables. -/
def dataDimension (n : ℕ) : ℕ := n / 5

theorem five_mul_dataDimension_le (n : ℕ) : 5 * dataDimension n ≤ n := by
  unfold dataDimension
  omega

theorem lt_five_mul_dataDimension_add_five (n : ℕ) :
    n < 5 * dataDimension n + 5 := by
  unfold dataDimension
  omega

theorem dataDimension_eq_zero_iff (n : ℕ) : dataDimension n = 0 ↔ n < 5 := by
  unfold dataDimension
  omega

theorem hashDimension_exists (d : ℕ) (hd : 0 < d) :
    ∃ r : ℕ, 0 < r ∧ d ^ 2 ≤ r ^ 3 :=
  ⟨d, hd, Nat.pow_le_pow_right hd (by decide)⟩

/-- The least positive `r` with `d ^ 2 ≤ r ^ 3`, or zero when `d = 0`. -/
def hashDimension (d : ℕ) : ℕ :=
  if hd : d = 0 then 0
  else Nat.find (hashDimension_exists d (Nat.pos_of_ne_zero hd))

@[simp] theorem hashDimension_zero : hashDimension 0 = 0 := by
  simp [hashDimension]

theorem hashDimension_spec {d : ℕ} (hd : 0 < d) :
    0 < hashDimension d ∧ d ^ 2 ≤ hashDimension d ^ 3 := by
  rw [hashDimension, dite_eq_right (Nat.ne_of_gt hd)]
  exact Nat.find_spec (hashDimension_exists d hd)

theorem hashDimension_pos {d : ℕ} (hd : 0 < d) : 0 < hashDimension d :=
  (hashDimension_spec hd).1

theorem hashDimension_cube_bound (d : ℕ) : d ^ 2 ≤ hashDimension d ^ 3 := by
  by_cases hd : d = 0
  · subst d
    simp
  · exact (hashDimension_spec (Nat.pos_of_ne_zero hd)).2

theorem hashDimension_minimal {d r : ℕ} (hd : 0 < d)
    (hr : 0 < r) (hcube : d ^ 2 ≤ r ^ 3) : hashDimension d ≤ r := by
  rw [hashDimension, dite_eq_right (Nat.ne_of_gt hd)]
  exact Nat.find_min' _ ⟨hr, hcube⟩

theorem hashDimension_le (d : ℕ) : hashDimension d ≤ d := by
  by_cases hd : d = 0
  · subst d
    simp
  · have hd' := Nat.pos_of_ne_zero hd
    exact hashDimension_minimal hd' hd' (Nat.pow_le_pow_right hd' (by decide))

theorem hashDimension_le_iff {d r : ℕ} (hd : 0 < d) :
    hashDimension d ≤ r ↔ 0 < r ∧ d ^ 2 ≤ r ^ 3 := by
  constructor
  · intro hr
    exact ⟨lt_of_lt_of_le (hashDimension_pos hd) hr,
      Nat.le_trans (hashDimension_cube_bound d) (Nat.pow_le_pow_left hr 3)⟩
  · rintro ⟨hr, hcube⟩
    exact hashDimension_minimal hd hr hcube

theorem nat_le_sixth_power (j : ℕ) : j ≤ j ^ 6 := by
  by_cases hj : j = 0
  · subst j
    simp
  · simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hj) (show 1 ≤ 6 by decide))

theorem sixth_power_le_implies_le {j d : ℕ} (hj : j ^ 6 ≤ d) : j ≤ d :=
  Nat.le_trans (nat_le_sixth_power j) hj

/-- The independence parameter chosen for the input dimension. -/
def independenceOrder (d : ℕ) : ℕ :=
  Nat.findGreatest (fun t => Even t ∧ t ^ 6 ≤ d) d

@[simp] theorem independenceOrder_zero : independenceOrder 0 = 0 := rfl

theorem independenceOrder_spec (d : ℕ) :
    Even (independenceOrder d) ∧ independenceOrder d ^ 6 ≤ d := by
  exact Nat.findGreatest_spec (P := fun t => Even t ∧ t ^ 6 ≤ d)
    (Nat.zero_le d) ⟨⟨0, rfl⟩, by simp⟩

theorem independenceOrder_even (d : ℕ) : Even (independenceOrder d) :=
  (independenceOrder_spec d).1

theorem independenceOrder_pow_le (d : ℕ) : independenceOrder d ^ 6 ≤ d :=
  (independenceOrder_spec d).2

theorem independenceOrder_le (d : ℕ) : independenceOrder d ≤ d :=
  Nat.findGreatest_le d

theorem independenceOrder_greatest {d j : ℕ} (hj : Even j) (hpow : j ^ 6 ≤ d) :
    j ≤ independenceOrder d :=
  Nat.le_findGreatest (sixth_power_le_implies_le hpow) ⟨hj, hpow⟩

theorem independenceOrder_two_le_iff (d : ℕ) :
    2 ≤ independenceOrder d ↔ 64 ≤ d := by
  constructor
  · intro ht
    calc
      64 = (2 : ℕ) ^ 6 := rfl
      _ ≤ independenceOrder d ^ 6 := Nat.pow_le_pow_left ht 6
      _ ≤ d := independenceOrder_pow_le d
  · intro hd
    exact independenceOrder_greatest ⟨1, rfl⟩ (show (2 : ℕ) ^ 6 ≤ d from hd)

theorem independenceOrder_eq_zero_iff (d : ℕ) :
    independenceOrder d = 0 ↔ d < 64 := by
  have ht := independenceOrder_two_le_iff d
  obtain ⟨k, hk⟩ := independenceOrder_even d
  constructor <;> intro h <;> omega

theorem independenceOrder_next_pow_gt (d : ℕ) :
    d < (independenceOrder d + 2) ^ 6 := by
  by_contra h
  have hpow : (independenceOrder d + 2) ^ 6 ≤ d := Nat.le_of_not_gt h
  have heven : Even (independenceOrder d + 2) := by
    obtain ⟨k, hk⟩ := independenceOrder_even d
    exact ⟨k + 1, by omega⟩
  have hle := independenceOrder_greatest heven hpow
  omega

theorem independenceOrder_eq_iff (d j : ℕ) :
    independenceOrder d = j ↔
      Even j ∧ j ^ 6 ≤ d ∧ ∀ k : ℕ, Even k → k ^ 6 ≤ d → k ≤ j := by
  constructor
  · intro h
    subst j
    exact ⟨independenceOrder_even d, independenceOrder_pow_le d,
      fun _ hk hp => independenceOrder_greatest hk hp⟩
  · rintro ⟨hj, hp, hmax⟩
    exact le_antisymm (hmax _ (independenceOrder_even d) (independenceOrder_pow_le d))
      (independenceOrder_greatest hj hp)

theorem independenceOrder_dataDimension_two_le_iff (n : ℕ) :
    2 ≤ independenceOrder (dataDimension n) ↔ 320 ≤ n := by
  rw [independenceOrder_two_le_iff]
  unfold dataDimension
  omega

/-- The number of seed bits used by the Toeplitz hash. -/
def hashBlockLength (d : ℕ) : ℕ := d + hashDimension d - 1

/-- The input position at which the hash-seed block starts. -/
def hashOffset (d : ℕ) : ℕ := d

/-- The input position at which the modulus block starts. -/
def polynomialOffset (d : ℕ) : ℕ := hashOffset d + hashBlockLength d

/-- The input position at which the coefficient blocks start. -/
def coefficientsOffset (d : ℕ) : ℕ := polynomialOffset d + hashDimension d

/-- The input position at which a selected coefficient block starts. -/
def coefficientOffset (d j : ℕ) : ℕ := coefficientsOffset d + j * hashDimension d

/-- Total length of the data and parameter blocks. -/
def blockLen (d : ℕ) : ℕ :=
  coefficientsOffset d + independenceOrder d * hashDimension d

theorem polynomialOffset_eq (d : ℕ) :
    polynomialOffset d = d + (d + hashDimension d - 1) := rfl

theorem coefficientsOffset_eq (d : ℕ) :
    coefficientsOffset d = d + (d + hashDimension d - 1) + hashDimension d := rfl

theorem blockLen_eq_sum (d : ℕ) :
    blockLen d = d + (d + hashDimension d - 1) + hashDimension d +
      independenceOrder d * hashDimension d := rfl

theorem blockLen_eq {d : ℕ} (hd : 0 < d) :
    blockLen d = 2 * d + (independenceOrder d + 2) * hashDimension d - 1 := by
  rw [blockLen_eq_sum]
  simp only [Nat.add_mul]
  omega

theorem hashBlockLength_pos {d : ℕ} (hd : 0 < d) : 0 < hashBlockLength d := by
  have hr := hashDimension_pos hd
  unfold hashBlockLength
  omega

theorem hashOffset_le_polynomialOffset (d : ℕ) : hashOffset d ≤ polynomialOffset d := by
  unfold polynomialOffset
  omega

theorem polynomialOffset_le_coefficientsOffset (d : ℕ) :
    polynomialOffset d ≤ coefficientsOffset d := by
  unfold coefficientsOffset
  omega

theorem coefficientsOffset_le_blockLen (d : ℕ) : coefficientsOffset d ≤ blockLen d := by
  unfold blockLen
  omega

@[simp] theorem coefficientOffset_zero (d : ℕ) :
    coefficientOffset d 0 = coefficientsOffset d := by
  simp [coefficientOffset]

theorem coefficientOffset_succ (d j : ℕ) :
    coefficientOffset d (j + 1) = coefficientOffset d j + hashDimension d := by
  simp only [coefficientOffset, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem coefficientOffset_last (d : ℕ) :
    coefficientOffset d (independenceOrder d) = blockLen d := rfl

theorem coefficientOffset_mono (d : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    coefficientOffset d j ≤ coefficientOffset d k :=
  Nat.add_le_add_left (Nat.mul_le_mul_right (hashDimension d) hjk) _

theorem hash_index_lt {d i s : ℕ} (hi : i < hashDimension d) (hs : s < d) :
    i + s < hashBlockLength d := by
  unfold hashBlockLength
  omega

theorem hash_absolute_index_lt {d i s : ℕ}
    (hi : i < hashDimension d) (hs : s < d) :
    hashOffset d + (i + s) < polynomialOffset d :=
  Nat.add_lt_add_left (hash_index_lt hi hs) _

theorem polynomial_index_lt {d i : ℕ} (hi : i < hashDimension d) :
    polynomialOffset d + i < coefficientsOffset d :=
  Nat.add_lt_add_left hi _

theorem coefficient_index_lt {d j i : ℕ}
    (hj : j < independenceOrder d) (hi : i < hashDimension d) :
    coefficientOffset d j + i < blockLen d := by
  have hmul := Nat.mul_le_mul_right (hashDimension d) (Nat.succ_le_of_lt hj)
  simp only [Nat.succ_mul] at hmul
  unfold coefficientOffset blockLen
  omega

theorem blockLen_le_quad (d : ℕ) : blockLen d ≤ d * d + 4 * d := by
  have hr := hashDimension_le d
  have hmul := Nat.mul_le_mul (independenceOrder_le d) hr
  rw [blockLen_eq_sum]
  omega

theorem blockLen_le_four_mul_sub_one {d : ℕ} (hd : 0 < d) (hlt : d < 64) :
    blockLen d ≤ 4 * d - 1 := by
  rw [blockLen_eq hd, (independenceOrder_eq_zero_iff d).mpr hlt]
  have hr := hashDimension_le d
  simp only [Nat.zero_add]
  omega

end DepthThreeLowerBound

end Complexity
