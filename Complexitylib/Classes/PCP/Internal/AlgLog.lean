/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P
public import Complexitylib.Mathlib.NatBits

/-!
# A ruler of logarithmic length

Amplification runs logarithmically many rounds, and the bounded-iteration rule
counts rounds by the *length* of a string. So an algorithm needs to write a
string whose length is the logarithm of its input's.

The length used is the binary length `Nat.size`: the number of bits of the input
length, which is the first `k` with `n < 2 ^ k`. Writing it in unary is
polynomial-time by `UnaryFn.size`, and it is logarithmic in any polynomially
bounded quantity by `BigO.natSize_of_polynomial_bound`.

## Main definitions

- `Complexity.rulerLen` — the binary length of a number
- `Complexity.logRuler` — that many marks, for the input length

## Main results

- `Complexity.lt_two_pow_rulerLen`, `Complexity.two_pow_rulerLen_le` — the ruler
  is the first `k` with `n < 2 ^ k`
- `Complexity.rulerLen_bigO_log` — over a polynomially bounded quantity it is
  logarithmic
- `Complexity.logRuler_mem_FP` — the ruler is an `FP` function
-/

@[expose] public section

namespace Complexity

/-- How long the ruler is for `n`: the binary length of `n`, the first `k` with
`n < 2 ^ k`. It is irreducible so that no tactic tries to evaluate it on the
large quantities it is applied to; `rulerLen_eq_size` unfolds it. -/
@[irreducible] def rulerLen (n : ℕ) : ℕ := Nat.size n

theorem rulerLen_eq_size (n : ℕ) : rulerLen n = Nat.size n := by
  unfold rulerLen
  rfl

theorem lt_two_pow_rulerLen (n : ℕ) : n < 2 ^ rulerLen n := by
  rw [rulerLen_eq_size]
  exact Nat.lt_size_self n

theorem two_pow_rulerLen_le (n : ℕ) : 2 ^ rulerLen n ≤ 2 * n + 1 := by
  rw [rulerLen_eq_size]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.size_eq_log_two_add_one hn.ne', pow_succ]
    have := Nat.pow_log_le_self 2 hn.ne'
    omega

theorem rulerLen_pos {n : ℕ} (hn : 0 < n) : 0 < rulerLen n := by
  rw [rulerLen_eq_size]
  exact Nat.size_pos.mpr hn

/-- **A ruler over a polynomially bounded quantity is logarithmic.** -/
theorem rulerLen_bigO_log {N : ℕ → ℕ} {A B : ℕ} (hN : ∀ n, N n ≤ A * (n + 1) ^ B) :
    (fun n => rulerLen (N n)) =O (fun n => Nat.log 2 n) := by
  simp only [rulerLen_eq_size]
  exact BigO.natSize_of_polynomial_bound (Polynomial.C A * (Polynomial.X + 1) ^ B) fun n => by
    simpa using hN n

/-- **A ruler of logarithmic length**: `rulerLen |z|` marks. -/
def logRuler (z : List Bool) : List Bool := List.replicate (rulerLen z.length) true

theorem logRuler_mem_FP : logRuler ∈ FP :=
  (UnaryFn.length id_mem_FP).size.of_eq fun _ => (rulerLen_eq_size _).symm

theorem logRuler_eq (z : List Bool) :
    logRuler z = List.replicate (rulerLen z.length) true := rfl

@[simp] theorem length_logRuler (z : List Bool) :
    (logRuler z).length = rulerLen z.length := by
  rw [logRuler_eq, List.length_replicate]

end Complexity
