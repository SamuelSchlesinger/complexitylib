/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble
public import Complexitylib.Asymptotics
import Complexitylib.Tactic.PolyTime

/-!
# Counting out `2 ^ r n` in unary

A verifier using `r n` coins has `2 ^ r n` coin strings, and an algorithm that
has to look at all of them needs that many steps counted out somewhere. When
`r` is logarithmic the count is polynomial, so a polynomial-time function can
write it down — by starting from a single mark and doubling `r n` times.

The hypothesis is the one `Constructible` supplies: `r n` itself is available in
unary in polynomial time.

## Main definitions

- `Complexity.dbl` — doubling a string

## Main results

- `Complexity.exists_poly_two_pow_of_bigO_log` — `2 ^ O(log n)` is polynomial
- `Complexity.unaryExp_mem_FP` — `2 ^ r n` marks, in polynomial time
-/

@[expose] public section

namespace Complexity

/-- Doubling: the string followed by itself. -/
def dbl (s : List Bool) : List Bool := s ++ s

@[polytime] theorem dbl_mem_FP : dbl ∈ FP := by
  polytime [dbl]

theorem dbl_iterate (n : ℕ) : dbl^[n] [true] = List.replicate (2 ^ n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, dbl, ← List.replicate_add]
      congr 1
      rw [pow_succ]
      omega

open scoped Complexity in
/-- **A logarithmic exponent gives a polynomial.** This is what makes a
`O(log n)` randomness bound usable: the number of coin strings stays
polynomial. -/
theorem exists_poly_two_pow_of_bigO_log {r : ℕ → ℕ} (h : r =O fun n => Nat.log 2 n) :
    ∃ p : Polynomial ℕ, ∀ n, 2 ^ r n ≤ p.eval n := by
  rw [BigO, Asymptotics.isBigO_iff] at h
  obtain ⟨C, hC⟩ := h
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  refine ⟨Polynomial.X ^ ⌈C⌉₊ +
    Polynomial.C ((Finset.range (N + 1)).sup fun n => 2 ^ r n), ?_⟩
  intro n
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hn : n < N + 1
  · have : 2 ^ r n ≤ (Finset.range (N + 1)).sup fun n => 2 ^ r n :=
      Finset.le_sup (f := fun n => 2 ^ r n) (Finset.mem_range.mpr hn)
    omega
  · have hnN : N ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hb := hN n hnN
    simp only [Real.norm_natCast] at hb
    have hC_le : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
    have hlog_nonneg : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by positivity
    have h_real : (r n : ℝ) ≤ (⌈C⌉₊ : ℝ) * ((Nat.log 2 n : ℕ) : ℝ) :=
      le_trans hb (mul_le_mul_of_nonneg_right hC_le hlog_nonneg)
    have h_nat : r n ≤ ⌈C⌉₊ * Nat.log 2 n := by exact_mod_cast h_real
    have h1 : 2 ^ r n ≤ 2 ^ (⌈C⌉₊ * Nat.log 2 n) := Nat.pow_le_pow_right (by omega) h_nat
    have h2 : 2 ^ (⌈C⌉₊ * Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ ⌈C⌉₊ := by
      rw [← pow_mul, Nat.mul_comm]
    have h3 : (2 ^ Nat.log 2 n) ^ ⌈C⌉₊ ≤ n ^ ⌈C⌉₊ :=
      Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn0) _
    omega

/-- **Writing `2 ^ r n` marks.** If the number of coins is available in unary in
polynomial time and the number of coin strings is polynomially bounded, then
that many marks can be written in polynomial time. -/
@[polytime] theorem unaryExp_mem_FP {r : ℕ → ℕ}
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    (p : Polynomial ℕ) (hp : ∀ n, 2 ^ r n ≤ p.eval n) :
    (fun x : List Bool => List.replicate (2 ^ r x.length) true) ∈ FP := by
  have hwidth : (fun z : List Bool => polyRuler p (id z)) ∈ FP :=
    polyRulerFn_mem_FP p id_mem_FP
  have hbound : ∀ z : List Bool, ∀ n ≤ (List.replicate (r z.length) true).length,
      (dbl^[n] [true]).length ≤ (polyRuler p (id z)).length := by
    intro z n hn
    rw [List.length_replicate] at hn
    rw [dbl_iterate, List.length_replicate, polyRuler_length]
    exact le_trans (Nat.pow_le_pow_right (by omega) hn) (hp z.length)
  have hiter := Cobham.iterate_mem_FP dbl_mem_FP (constFn_mem_FP [true]) hr hwidth hbound
  refine mem_FP_of_eq hiter fun x => ?_
  rw [List.length_replicate, dbl_iterate]

open scoped Complexity in
/-- **The form the assembly uses.** A constructible logarithmic randomness bound
lets the number of coin strings be counted out in polynomial time. -/
@[polytime] theorem unaryExp_mem_FP_of_bigO_log {r : ℕ → ℕ}
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    (h : r =O fun n => Nat.log 2 n) :
    (fun x : List Bool => List.replicate (2 ^ r x.length) true) ∈ FP := by
  obtain ⟨p, hp⟩ := exists_poly_two_pow_of_bigO_log h
  exact unaryExp_mem_FP hr p hp

end Complexity
