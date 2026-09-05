/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.NumEnc
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Numbering a tuple

A walk is a tuple of darts, and a coin sequence is a tuple of coins. This module
numbers such a tuple the way a numeral works: the `j`-th entry contributes its
own number times the base to the `j`-th power. Reading an entry back is dividing
by that power and taking the remainder, which is what an algorithm does.

## Main results

- `Complexity.NumEnc.instPi` — the `NumEnc` instance for `Fin n → α`
- `Complexity.NumEnc.digit_sum`, `Complexity.NumEnc.sum_digits` — reading a
  digit, and reassembling a number from its digits
-/

@[expose] public section

namespace Complexity

namespace NumEnc

open NumEnc (card enc dec)

variable {α : Type}

/-! ### Digits -/

theorem sum_lt_pow {c n : ℕ} (g : ℕ → ℕ) (hg : ∀ i < n, g i < c) :
    ∑ i ∈ Finset.range n, g i * c ^ i < c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h1 : ∑ i ∈ Finset.range n, g i * c ^ i < c ^ n := ih fun i hi => hg i (by omega)
      have h2 : g n < c := hg n (by omega)
      calc (∑ i ∈ Finset.range n, g i * c ^ i) + g n * c ^ n
          < c ^ n + g n * c ^ n := by omega
        _ = (g n + 1) * c ^ n := by ring
        _ ≤ c * c ^ n := Nat.mul_le_mul_right _ (by omega)
        _ = c ^ n * c := by ring

theorem digit_sum {c : ℕ} (hc : 0 < c) (g : ℕ → ℕ) :
    ∀ {n j : ℕ}, j < n → (∀ i < n, g i < c) →
      (∑ i ∈ Finset.range n, g i * c ^ i) / c ^ j % c = g j := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
      intro j hj hg
      rcases Nat.lt_or_ge j n with hjn | hjn
      · have hstep : (∑ i ∈ Finset.range (n + 1), g i * c ^ i) / c ^ j % c
            = (∑ i ∈ Finset.range n, g i * c ^ i) / c ^ j % c := by
          rw [Finset.sum_range_succ]
          have hpow : c ^ n = c ^ j * c ^ (n - j) := by
            rw [← pow_add]
            congr 1
            omega
          have hdvd : c ∣ c ^ (n - j) := dvd_pow_self c (by omega)
          obtain ⟨t, ht⟩ := hdvd
          rw [hpow, ht]
          rw [show g n * (c ^ j * (c * t)) = c ^ j * (g n * (c * t)) by ring,
            Nat.add_mul_div_left _ _ (Nat.pow_pos hc),
            show g n * (c * t) = (g n * t) * c by ring, Nat.add_mul_mod_self_right]
        rw [hstep]
        exact ih hjn fun i hi => hg i (by omega)
      · have hjeq : j = n := by omega
        subst hjeq
        rw [Finset.sum_range_succ]
        have hlt : ∑ i ∈ Finset.range j, g i * c ^ i < c ^ j :=
          sum_lt_pow g fun i hi => hg i (by omega)
        rw [show g j * c ^ j = c ^ j * g j by ring,
          Nat.add_mul_div_left _ _ (Nat.pow_pos hc), Nat.div_eq_of_lt hlt,
          Nat.zero_add, Nat.mod_eq_of_lt (hg j (by omega))]

theorem sum_digits {c : ℕ} :
    ∀ {n i : ℕ}, i < c ^ n → ∑ j ∈ Finset.range n, (i / c ^ j % c) * c ^ j = i := by
  intro n
  induction n with
  | zero =>
      intro i hi
      simp only [pow_zero] at hi
      simp
      omega
  | succ n ih =>
      intro i hi
      rw [Finset.sum_range_succ']
      have h1 : ∀ j, i / c ^ (j + 1) % c = (i / c) / c ^ j % c := by
        intro j
        rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
      have h2 : i / c < c ^ n := by
        refine Nat.div_lt_of_lt_mul ?_
        rw [Nat.mul_comm, ← pow_succ]
        exact hi
      have h3 : ∑ j ∈ Finset.range n, (i / c ^ (j + 1) % c) * c ^ (j + 1)
          = (∑ j ∈ Finset.range n, ((i / c) / c ^ j % c) * c ^ j) * c := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h1 j, pow_succ]
        ring
      rw [h3, ih h2]
      simp only [pow_zero, Nat.mul_one, Nat.div_one]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod i c

/-! ### The instance -/

theorem get_eq [NumEnc α] {i : ℕ} (hi : i < card α) {a : α} (h : i = enc a) :
    get hi = a := by
  have h1 : enc (get hi) = i := enc_get hi
  exact enc_injective (h1.trans h)

/-- The number of the `i`-th entry of a tuple, or zero past its end. -/
def encAt {n : ℕ} [NumEnc α] (f : Fin n → α) (i : ℕ) : ℕ :=
  if h : i < n then enc (f ⟨i, h⟩) else 0

theorem encAt_lt {n : ℕ} [NumEnc α] (f : Fin n → α) {i : ℕ} (hi : i < n) :
    encAt f i < card α := by
  rw [encAt, dite_eq_left hi]
  exact enc_lt _

/-- **A tuple is numbered like a numeral.** -/
instance instPi (n : ℕ) [NumEnc α] : NumEnc (Fin n → α) where
  card := card α ^ n
  enc f := ∑ i ∈ Finset.range n, encAt f i * card α ^ i
  dec i :=
    if h : i < card α ^ n then
      some fun j : Fin n =>
        get (show i / card α ^ j.val % card α < card α from by
          have hpos : 0 < card α ^ n := Nat.lt_of_le_of_lt (Nat.zero_le _) h
          have hc : 0 < card α := by
            by_contra hcon
            have hz : card α = 0 := by omega
            have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
            rw [hz, zero_pow (by omega)] at hpos
            omega
          exact Nat.mod_lt _ hc)
    else none
  enc_lt f := sum_lt_pow _ fun i hi => encAt_lt f hi
  dec_enc f := by
    have hlt : (∑ i ∈ Finset.range n, encAt f i * card α ^ i) < card α ^ n :=
      sum_lt_pow _ fun i hi => encAt_lt f hi
    rw [dite_eq_left hlt]
    congr 1
    funext j
    have hc : 0 < card α := Nat.lt_of_le_of_lt (Nat.zero_le _) (enc_lt (f j))
    have hdig := digit_sum (c := card α) hc (encAt f) j.isLt
      (fun i hi => encAt_lt f hi)
    have hval : encAt f j.val = enc (f j) := by
      rw [encAt, dite_eq_left j.isLt]
    exact get_eq _ (hdig.trans hval)
  enc_dec i f h := by
    by_cases hi : i < card α ^ n
    · rw [dite_eq_left hi] at h
      have hf := Option.some_injective _ h
      subst hf
      show ∑ j ∈ Finset.range n, encAt _ j * card α ^ j = i
      refine Eq.trans (Finset.sum_congr rfl fun j hj => ?_) (sum_digits hi)
      rw [encAt, dite_eq_left (Finset.mem_range.mp hj), enc_get]
    · rw [dite_eq_right hi] at h
      exact absurd h (by simp)
  dec_isSome i hi := by
    rw [dite_eq_left hi]
    rfl

end NumEnc

end Complexity
