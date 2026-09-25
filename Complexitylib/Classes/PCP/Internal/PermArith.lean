/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

/-!
# Arithmetic for the expander counting bound

Four elementary estimates, all in `ℕ`, which together turn the permutation
count of `PermCount` into a bound small enough to survive a union bound over
all vertex sets.

* A single binomial term is at most the whole binomial sum: `C(s,t) 2^{s-t} ≤ 3^s`.
* Descending factorials compare like powers: `descFactorial s k · n^k ≤ s^k ·
  descFactorial n k` when `s ≤ n` — this is `(s/n)^k` in disguise, and it is
  where the smallness of a set of at most half the vertices enters.
* `descFactorial n k · (n-k)! = n!`, so the count is a fraction of `n!`.
* `C(n,s) s^s ≤ 3^s n^s`, the usual `(e n / s)^s` bound with `e` replaced by
  the integer `3`. Its one analytic ingredient is `(1 + 1/m)^m ≤ e < 3`.

## Main results

- `Complexity.choose_mul_two_pow_le`
- `Complexity.descFactorial_mul_pow_le`
- `Complexity.descFactorial_mul_factorial_sub`
- `Complexity.choose_mul_pow_self_le`
-/

@[expose] public section

namespace Complexity

open Finset

/-- **One term of a binomial sum.** -/
theorem choose_mul_two_pow_le (s t : ℕ) (ht : t ≤ s) :
    s.choose t * 2 ^ (s - t) ≤ 3 ^ s := by
  have hexp : (3 : ℕ) ^ s = ∑ k ∈ range (s + 1), 1 ^ k * 2 ^ (s - k) * s.choose k := by
    have := add_pow (1 : ℕ) 2 s
    norm_num at this ⊢
    exact this
  rw [hexp]
  have hmem : t ∈ range (s + 1) := Finset.mem_range.2 (by omega)
  calc s.choose t * 2 ^ (s - t) = 1 ^ t * 2 ^ (s - t) * s.choose t := by ring
    _ ≤ _ := Finset.single_le_sum
        (f := fun k => 1 ^ k * 2 ^ (s - k) * s.choose k) (fun k _ => Nat.zero_le _) hmem

/-- **Descending factorials compare like powers.** -/
theorem descFactorial_mul_pow_le {s n : ℕ} (hsn : s ≤ n) (k : ℕ) :
    s.descFactorial k * n ^ k ≤ s ^ k * n.descFactorial k := by
  have hn : n ^ k = ∏ _i ∈ range k, n := by simp
  have hs : s ^ k = ∏ _i ∈ range k, s := by simp
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, hn, hs,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod fun i _ => ?_
  have h : (s - i) * n ≤ s * (n - i) := by
    rcases le_or_gt i s with hi | hi
    · have h1 : (s - i) * n = s * n - i * n := by
        rw [Nat.sub_mul]
      have h2 : s * (n - i) = s * n - s * i := by
        rw [Nat.mul_sub]
      rw [h1, h2]
      have : s * i ≤ i * n := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ hsn
      omega
    · have : s - i = 0 := by omega
      rw [this, zero_mul]
      exact Nat.zero_le _
  exact h

/-- **The descending factorial is a fraction of the factorial.** -/
theorem descFactorial_mul_factorial_sub {n k : ℕ} (hk : k ≤ n) :
    n.descFactorial k * Nat.factorial (n - k) = Nat.factorial n := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  calc Nat.factorial k * n.choose k * Nat.factorial (n - k)
      = n.choose k * Nat.factorial k * Nat.factorial (n - k) := by ring
    _ = Nat.factorial n := Nat.choose_mul_factorial_mul_factorial hk

/-! ### The `(3 n / s)^s` bound -/

private theorem succ_pow_le_three_mul (m : ℕ) : ((m : ℝ) + 1) ^ m ≤ 3 * (m : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 : ℝ) + 1 / m ≤ Real.exp (1 / m) := by
    have := Real.add_one_le_exp (1 / (m : ℝ))
    linarith
  have h2 : ((1 : ℝ) + 1 / m) ^ m ≤ Real.exp 1 := by
    calc ((1 : ℝ) + 1 / m) ^ m ≤ (Real.exp (1 / m)) ^ m :=
          pow_le_pow_left₀ (by positivity) h1 m
      _ = Real.exp ((m : ℝ) * (1 / m)) := by
          rw [← Real.exp_nat_mul]
      _ = Real.exp 1 := by
          rw [mul_one_div, div_self (ne_of_gt hm0)]
  have h3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hfac : ((m : ℝ) + 1) ^ m = (m : ℝ) ^ m * ((1 : ℝ) + 1 / m) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hfac]
  have hmm : (0 : ℝ) ≤ (m : ℝ) ^ m := by positivity
  nlinarith [h2, h3, hmm]

/-- **`s^s ≤ 3^s s!`**, the integer form of `s! ≥ (s/e)^s`. -/
theorem pow_self_le_three_pow_mul_factorial (s : ℕ) :
    s ^ s ≤ 3 ^ s * Nat.factorial s := by
  induction s with
  | zero => simp
  | succ m ih =>
      have hstep : (m + 1) ^ m ≤ 3 * m ^ m := by
        have := succ_pow_le_three_mul m
        exact_mod_cast this
      calc (m + 1) ^ (m + 1) = (m + 1) * (m + 1) ^ m := by ring
        _ ≤ (m + 1) * (3 * m ^ m) := Nat.mul_le_mul_left _ hstep
        _ ≤ (m + 1) * (3 * (3 ^ m * Nat.factorial m)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih)
        _ = 3 ^ (m + 1) * Nat.factorial (m + 1) := by
            rw [Nat.factorial_succ, pow_succ]
            ring

/-- **The `(3 n / s)^s` bound on a binomial coefficient.** -/
theorem choose_mul_pow_self_le (n s : ℕ) : n.choose s * s ^ s ≤ 3 ^ s * n ^ s := by
  calc n.choose s * s ^ s ≤ n.choose s * (3 ^ s * Nat.factorial s) :=
        Nat.mul_le_mul_left _ (pow_self_le_three_pow_mul_factorial s)
    _ = 3 ^ s * (Nat.factorial s * n.choose s) := by ring
    _ = 3 ^ s * n.descFactorial s := by rw [Nat.descFactorial_eq_factorial_mul_choose]
    _ ≤ 3 ^ s * n ^ s := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow n s)

/-! ### The per-set estimate -/

/-- The numeric heart: `2^{2s} 3^{31s} ≤ 2^{60k}` whenever `9 s ≤ 10 k`. -/
theorem two_pow_three_pow_le {s k : ℕ} (h9 : 9 * s ≤ 10 * k) :
    2 ^ (2 * s) * 3 ^ (31 * s) ≤ 2 ^ (60 * k) := by
  have hbase : (2 : ℕ) ^ 20 * 3 ^ 310 ≤ 2 ^ 540 := by
    have hb1 : (3 : ℕ) ^ 31 ≤ 2 ^ 52 := by norm_num
    have hb2 : (3 : ℕ) ^ 310 ≤ 2 ^ 520 := by
      calc (3 : ℕ) ^ 310 = ((3 : ℕ) ^ 31) ^ 10 := by rw [← pow_mul]
        _ ≤ ((2 : ℕ) ^ 52) ^ 10 := Nat.pow_le_pow_left hb1 10
        _ = 2 ^ 520 := by rw [← pow_mul]
    calc (2 : ℕ) ^ 20 * 3 ^ 310 ≤ 2 ^ 20 * 2 ^ 520 := Nat.mul_le_mul_left _ hb2
      _ = 2 ^ 540 := by rw [← pow_add]
  have hL : ((2 : ℕ) ^ (2 * s) * 3 ^ (31 * s)) ^ 10 = ((2 : ℕ) ^ 20 * 3 ^ 310) ^ s := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have hR : (((2 : ℕ) ^ (60 * k)) ^ 10) = 2 ^ (600 * k) := by
    rw [← pow_mul]
    congr 1
    ring
  have hstep : ((2 : ℕ) ^ 20 * 3 ^ 310) ^ s ≤ ((2 : ℕ) ^ 540) ^ s :=
    Nat.pow_le_pow_left hbase s
  have hR2 : ((2 : ℕ) ^ 540) ^ s ≤ 2 ^ (600 * k) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfin : ((2 : ℕ) ^ (2 * s) * 3 ^ (31 * s)) ^ 10 ≤ ((2 : ℕ) ^ (60 * k)) ^ 10 := by
    rw [hL, hR]
    exact le_trans hstep hR2
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hfin

/-- **The estimate for one vertex set**, with the permutation count abstracted.
The hypothesis is what `PermCount` supplies, in the form `descFactorial` and
`choose` bounds put it; the conclusion leaves a factor `2^s` of room for the
union bound over all sets of size `s`. -/
theorem key_estimate {n s k B : ℕ} (hs : 1 ≤ s) (hsn : 2 * s ≤ n) (h9 : 9 * s ≤ 10 * k)
    (hB : B * 2 ^ k * n ^ k ≤ 3 ^ s * s ^ k * Nat.factorial n) :
    2 ^ s * (n.choose s * B ^ 30) ≤ Nat.factorial n ^ 30 := by
  obtain ⟨m, hm⟩ : ∃ m, k * 30 = s + m := ⟨k * 30 - s, by omega⟩
  have hsspos : 0 < s ^ s := pow_pos (by omega) s
  have hnum := two_pow_three_pow_le h9
  have h2 : 2 ^ s * n.choose s * 3 ^ (s * 30) * s ^ (k * 30) ≤ (2 * n) ^ (k * 30) := by
    refine Nat.le_of_mul_le_mul_right ?_ hsspos
    have hD : n.choose s * s ^ s ≤ 3 ^ s * n ^ s := choose_mul_pow_self_le n s
    have hcancel : 2 ^ s * 3 ^ (31 * s) ≤ 2 ^ (30 * k + m) := by
      refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 ^ s by positivity)
      have hLl : 2 ^ s * (2 ^ s * 3 ^ (31 * s)) = 2 ^ (2 * s) * 3 ^ (31 * s) := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
      have hRr : 2 ^ s * 2 ^ (30 * k + m) = 2 ^ (60 * k) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hLl, hRr]
      exact hnum
    have hsm : 2 ^ s * 3 ^ (31 * s) * s ^ m ≤ 2 ^ (30 * k) * n ^ m := by
      calc 2 ^ s * 3 ^ (31 * s) * s ^ m ≤ 2 ^ (30 * k + m) * s ^ m :=
            Nat.mul_le_mul_right _ hcancel
        _ = 2 ^ (30 * k) * (2 ^ m * s ^ m) := by rw [pow_add]; ring
        _ = 2 ^ (30 * k) * (2 * s) ^ m := by rw [mul_pow]
        _ ≤ 2 ^ (30 * k) * n ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsn m)
    have hsk : s ^ (k * 30) = s ^ s * s ^ m := by rw [hm, pow_add]
    have hnk : (2 * n) ^ (k * 30) = 2 ^ (30 * k) * (n ^ s * n ^ m) := by
      have e1 : (2 : ℕ) ^ (k * 30) = 2 ^ (30 * k) := by congr 1; ring
      rw [mul_pow, e1, hm, pow_add]
    have h3 : (3 : ℕ) ^ (s * 30) * 3 ^ s = 3 ^ (31 * s) := by
      rw [← pow_add]
      congr 1
      ring
    calc 2 ^ s * n.choose s * 3 ^ (s * 30) * s ^ (k * 30) * s ^ s
        = (2 ^ s * 3 ^ (s * 30) * s ^ (k * 30)) * (n.choose s * s ^ s) := by ring
      _ ≤ (2 ^ s * 3 ^ (s * 30) * s ^ (k * 30)) * (3 ^ s * n ^ s) :=
          Nat.mul_le_mul_left _ hD
      _ = (2 ^ s * (3 ^ (s * 30) * 3 ^ s) * s ^ m) * (s ^ s * n ^ s) := by
          rw [hsk]; ring
      _ = (2 ^ s * 3 ^ (31 * s) * s ^ m) * (s ^ s * n ^ s) := by rw [h3]
      _ ≤ (2 ^ (30 * k) * n ^ m) * (s ^ s * n ^ s) := Nat.mul_le_mul_right _ hsm
      _ = (2 * n) ^ (k * 30) * s ^ s := by rw [hnk]; ring
  have h1' : B ^ 30 * (2 * n) ^ (k * 30)
      ≤ 3 ^ (s * 30) * s ^ (k * 30) * Nat.factorial n ^ 30 := by
    have hpow := Nat.pow_le_pow_left hB 30
    have hBpow : B ^ 30 * (2 * n) ^ (k * 30) = (B * 2 ^ k * n ^ k) ^ 30 := by
      simp only [mul_pow, ← pow_mul]
      ring
    have hRpow : (3 ^ s * s ^ k * Nat.factorial n) ^ 30
        = 3 ^ (s * 30) * s ^ (k * 30) * Nat.factorial n ^ 30 := by
      simp only [mul_pow, ← pow_mul]
    rw [hBpow, ← hRpow]
    exact hpow
  have hpos : 0 < (2 * n) ^ (k * 30) := pow_pos (by omega) _
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc 2 ^ s * (n.choose s * B ^ 30) * (2 * n) ^ (k * 30)
      = (2 ^ s * n.choose s) * (B ^ 30 * (2 * n) ^ (k * 30)) := by ring
    _ ≤ (2 ^ s * n.choose s) * (3 ^ (s * 30) * s ^ (k * 30) * Nat.factorial n ^ 30) :=
        Nat.mul_le_mul_left _ h1'
    _ = (2 ^ s * n.choose s * 3 ^ (s * 30) * s ^ (k * 30)) * Nat.factorial n ^ 30 := by ring
    _ ≤ (2 * n) ^ (k * 30) * Nat.factorial n ^ 30 := Nat.mul_le_mul_right _ h2
    _ = Nat.factorial n ^ 30 * (2 * n) ^ (k * 30) := by ring

/-- **The counting hypothesis of `key_estimate`,** as `PermCount` produces it. -/
theorem count_bound {n s t : ℕ} (hsn : s ≤ n) (hts : t ≤ s) (hkn : s - t ≤ n) :
    (s.choose t * s.descFactorial (s - t) * Nat.factorial (n - (s - t))) * 2 ^ (s - t) * n ^ (s - t)
      ≤ 3 ^ s * s ^ (s - t) * Nat.factorial n := by
  set k := s - t with hk
  have hA : s.choose t * 2 ^ k ≤ 3 ^ s := choose_mul_two_pow_le s t hts
  have hBb : s.descFactorial k * n ^ k ≤ s ^ k * n.descFactorial k :=
    descFactorial_mul_pow_le hsn k
  have hC : n.descFactorial k * Nat.factorial (n - k) = Nat.factorial n :=
    descFactorial_mul_factorial_sub hkn
  calc (s.choose t * s.descFactorial k * Nat.factorial (n - k)) * 2 ^ k * n ^ k
      = (s.choose t * 2 ^ k) * (s.descFactorial k * n ^ k) * Nat.factorial (n - k) := by ring
    _ ≤ 3 ^ s * (s ^ k * n.descFactorial k) * Nat.factorial (n - k) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hA hBb)
    _ = 3 ^ s * s ^ k * (n.descFactorial k * Nat.factorial (n - k)) := by ring
    _ = 3 ^ s * s ^ k * Nat.factorial n := by rw [hC]

end Complexity
