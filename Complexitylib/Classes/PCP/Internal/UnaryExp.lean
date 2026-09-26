/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble

/-!
# Counting out `2 ^ r n` in unary

A verifier using `r n` coins has `2 ^ r n` coin strings, and an algorithm that
has to look at all of them needs that many steps counted out somewhere. When
`r` is logarithmic the count is polynomially bounded
(`PolyBound.two_pow_of_bigO_log`), so a polynomial-time function can write it
down (`UnaryFn.pow_of_le`).

The hypothesis is the one `Constructible` supplies: `r n` itself is available in
unary in polynomial time.

## Main results

- `Complexity.exists_poly_two_pow_of_bigO_log` — `2 ^ O(log n)` is polynomial
- `Complexity.unaryExp_mem_FP_of_bigO_log` — `2 ^ r n` marks, in polynomial time
-/

@[expose] public section

namespace Complexity

open scoped Complexity in
/-- **A logarithmic exponent gives a polynomial.** This is what makes a
`O(log n)` randomness bound usable: the number of coin strings stays
polynomial. -/
theorem exists_poly_two_pow_of_bigO_log {r : ℕ → ℕ} (h : r =O fun n => Nat.log 2 n) :
    ∃ p : Polynomial ℕ, ∀ n, 2 ^ r n ≤ p.eval n :=
  PolyBound.two_pow_of_bigO_log h

open scoped Complexity in
/-- **Writing `2 ^ r n` marks.** A constructible logarithmic randomness bound
lets the number of coin strings be counted out in polynomial time. -/
theorem unaryExp_mem_FP_of_bigO_log {r : ℕ → ℕ}
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    (h : r =O fun n => Nat.log 2 n) :
    (fun x : List Bool => List.replicate (2 ^ r x.length) true) ∈ FP := by
  obtain ⟨p, hp⟩ := PolyBound.two_pow_of_bigO_log h
  exact UnaryFn.pow_of_le (UnaryFn.const 2) hr (UnaryFn.polyEval p (UnaryFn.length id_mem_FP))
    fun x => hp x.length

end Complexity
