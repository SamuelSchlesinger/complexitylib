/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Asymptotics

/-!
# Polynomial bounds on natural-number functions

`PolyBound f` says `f` is dominated pointwise (at every argument, not merely
eventually) by the evaluation of a natural polynomial. Resource bookkeeping
assembles time and space bounds by addition, multiplication, and monotonicity,
so an everywhere-bound closed under those operations is easier to carry through
a construction than a big-O statement; `PolyBound.bigO` converts to the big-O
form the complexity classes are stated in.

## Main results

- `PolyBound` — pointwise domination by a natural polynomial
- `PolyBound.const`, `.id`, `.add`, `.mul`, `.pow`, `.mono`, `.max`, `.eval` —
  the closure API
- `PolyBound.bigO` — a polynomial bound is a big-O power bound
- `PolyBound.exists_mul_pow_bound` — a polynomial bound is an `A * (n + 1) ^ B` bound
- `PolyBound.two_pow_of_bigO_log` — `2 ^ O(log n)` is polynomially bounded
-/


@[expose] public section

namespace Complexity

/-- Pointwise domination by the evaluation of a natural polynomial. -/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ inputLength, f inputLength ≤ p.eval inputLength

namespace PolyBound

theorem const (value : ℕ) : PolyBound (fun _ => value) :=
  ⟨Polynomial.C value, fun _ => by simp⟩

theorem id : PolyBound (fun inputLength => inputLength) :=
  ⟨Polynomial.X, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength + g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun inputLength => by
    rw [Polynomial.eval_add]
    exact Nat.add_le_add (hp inputLength) (hq inputLength)⟩

theorem mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength * g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun inputLength => by
    rw [Polynomial.eval_mul]
    exact Nat.mul_le_mul (hp inputLength) (hq inputLength)⟩

theorem mono {f g : ℕ → ℕ} (hg : PolyBound g)
    (hle : ∀ inputLength, f inputLength ≤ g inputLength) : PolyBound f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun inputLength => le_trans (hle inputLength) (hp inputLength)⟩

theorem max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => max (f inputLength) (g inputLength)) :=
  (hf.add hg).mono fun _ => Nat.max_le.mpr
    ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

theorem eval (p : Polynomial ℕ) :
    PolyBound (fun inputLength => p.eval inputLength) :=
  ⟨p, fun _ => le_rfl⟩

theorem pow {f : ℕ → ℕ} (hf : PolyBound f) (exponent : ℕ) :
    PolyBound (fun inputLength => f inputLength ^ exponent) := by
  induction exponent with
  | zero => simpa using const 1
  | succ exponent ih => simpa [pow_succ] using ih.mul hf

/-- A polynomial bound is a big-O bound by the polynomial's degree. -/
theorem bigO {f : ℕ → ℕ} (hf : PolyBound f) : ∃ d, f =O (· ^ d) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.natDegree, BigO.of_polynomial_bound p hp⟩

/-- A polynomial bound is a bound of the form `A * (n + 1) ^ B`: take `A` to be
the sum of the coefficients and `B` the degree. -/
theorem exists_mul_pow_bound {f : ℕ → ℕ} (hf : PolyBound f) :
    ∃ A B : ℕ, ∀ n, f n ≤ A * (n + 1) ^ B := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
  refine le_trans (hp n) ?_
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ p.natDegree := by
    rw [Finset.mem_range] at hi
    omega
  exact Nat.mul_le_mul_left _
    (le_trans (Nat.pow_le_pow_left (by omega) i) (Nat.pow_le_pow_right (by omega) hi'))

/-- **A logarithmic exponent gives a polynomial bound.** If `r n = O(log n)`,
then `2 ^ r n` is bounded by a polynomial at every `n`: eventually
`2 ^ r n ≤ 2 ^ (c log n) ≤ n ^ c`, and the finitely many values before that are
bounded by a constant. -/
theorem two_pow_of_bigO_log {r : ℕ → ℕ} (h : r =O fun n => Nat.log 2 n) :
    PolyBound fun n => 2 ^ r n := by
  obtain ⟨c, N, hN⟩ := BigO.exists_nat_bound h
  refine ⟨Polynomial.X ^ c + Polynomial.C ((Finset.range (N + 1)).sup fun n => 2 ^ r n),
    fun n => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hn : n < N + 1
  · have := Finset.le_sup (f := fun n => 2 ^ r n) (Finset.mem_range.mpr hn)
    omega
  · have h1 : 2 ^ r n ≤ 2 ^ (c * Nat.log 2 n) :=
      Nat.pow_le_pow_right (by omega) (hN n (by omega))
    have h2 : 2 ^ (c * Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ c := by
      rw [← pow_mul, Nat.mul_comm]
    have h3 : (2 ^ Nat.log 2 n) ^ c ≤ n ^ c :=
      Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) _
    omega

end PolyBound

end Complexity
