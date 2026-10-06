/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct
public import Complexitylib.Algebraic.Semantics
import Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.NegationLimited.Internal
import Mathlib.Tactic.Ring

/-!
# Boolean matrix product with few negations

Every monotone circuit for the Boolean product of two `n × n` matrices has at
least `n ^ 3` AND gates (`Algebraic.Monotone.MatrixProduct.cube_le_andCost`),
while circuits with negations compute it with `O(n ^ ω)` gates through integer
matrix multiplication. This file interpolates between the two by the number of
negations.

The circuit model is the imported library's De Morgan signature
(`DeMorgan.signature`: the constants, identity, NOT, and fan-in-two AND and OR,
with unbounded fan-out). NOT gates are counted by `DeMorgan.notCost` and AND
gates by `DeMorgan.andCost`; every gate of the program is counted, used or not,
and OR gates, constants and identities are free. With no NOT gate the model is
that of `Algebraic.Monotone.MatrixProduct.card_le_andCost` (monotone circuits
with constants), and it contains the AND/OR circuits of `cube_le_andCost`.

## Main results

* `div_mul_div_mul_le_andCost`: a circuit with at most `t` NOT gates computing
  the product of an `I × K` matrix and a `K × J` matrix has at least
  `⌊I / 2 ^ t⌋ * ⌊J / 2 ^ t⌋ * K` AND gates; for `t = 0` this is the monotone
  bound `I * J * K`.
* `mul_div_sq_le_andCost`: in the square case, `n * ⌊n / 2 ^ t⌋ ^ 2` AND gates.
* `cube_le_four_pow_mul_andCost`: if `2 ^ t ≤ n`, then
  `n ^ 3 ≤ 4 ^ (t + 1) * #AND`; so a circuit with fewer than `n ^ (3 - ε)` AND
  gates has more than `(ε / 2) * log₂ n - 1` NOT gates.
* `mul_mul_le_andCost_add`, `cube_sub_le_andCost`: if every NOT gate computes a
  function of the inputs in a fixed set `S`, the circuit has at least
  `I * J * K - |S| * max I J` AND gates, `n ^ 3 - |S| * n` in the square case.

## Proof

The first NOT gate reads a monotone function `h` of the inputs. Split the rows
of `x` and the columns of `y` into halves and evaluate `h` on the assignment
that is one exactly on the first halves. If it is zero, `h` vanishes once the
second halves are set to zero; if it is one, `h` is one once the first halves
are set to one. Either way the NOT gate becomes constant, and the product of
the remaining halves is still computed, since an entry of the product reads
only its own row and column. Replacing the NOT gate by its constant and the
fixed inputs by constants gives a circuit with one NOT gate fewer, the same AND
gates, and half the rows and columns. After `t` steps the monotone bound for
circuits with constants applies. If instead every NOT gate depends only on the
inputs in `S`, setting those to zero makes every NOT gate constant at once and
leaves a monotone circuit for the partial product over the triples that avoid
`S`. The proofs are in
`Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.NegationLimited.Internal`.

## Prior art

No lower bound for the Boolean matrix product by circuits with a bounded number
of NOT gates appears in the literature we know. The monotone bound `n ^ 3` is
due to Pratt (1975), Paterson (1975) and Mehlhorn--Galil (1976). Markov (1958)
and Fischer (1975) show that `⌈log₂ (N + 1)⌉` NOT gates suffice for every
function of `N` inputs, with polynomial overhead in Fischer's construction.
Jukna (*Information Processing Letters*, 2004) uses a similar direct-sum
restriction for an explicit multi-output function needing
`log n - O(log log n)` NOT gates.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace MatrixProduct
namespace NegationLimited

/-- **Boolean matrix product with few negations.** Place entry `(i, k)` of an
`I × K` matrix at input `x i k` and entry `(k, j)` of a `K × J` matrix at input
`y k j`, all at distinct inputs. A De Morgan circuit with at most `t` NOT gates
whose output `z i j` computes `⋁ k, x i k ∧ y k j` for every `i` and `j` has at
least `⌊I / 2 ^ t⌋ * ⌊J / 2 ^ t⌋ * K` AND gates. -/
theorem div_mul_div_mul_le_andCost {N M I J K : Nat} (t : Nat)
    (x : Fin I → Fin K → Fin N) (y : Fin K → Fin J → Fin N)
    (distinct : Function.Injective (Sum.elim (Function.uncurry x) (Function.uncurry y)))
    (z : Fin I → Fin J → Fin M) (circuit : Circuit DeMorgan.signature N M)
    (nots : circuit.cost DeMorgan.notCost ≤ t)
    (computes : ∀ (a : Fin N → Bool) i j,
      circuit.eval DeMorgan.interpretation a (z i j) =
        decide (∃ k, a (x i k) = true ∧ a (y k j) = true)) :
    I / 2 ^ t * (J / 2 ^ t) * K ≤ circuit.cost DeMorgan.andCost :=
  Internal.div_mul_div_mul_le_andCost t (.ofInjective x y distinct) z circuit nots computes

/-- **Square Boolean matrix product with few negations.** A De Morgan circuit
with at most `t` NOT gates computing the Boolean product of two `n × n`
matrices, in the row-major layout of `cube_le_andCost`, has at least
`n * ⌊n / 2 ^ t⌋ ^ 2` AND gates. -/
theorem mul_div_sq_le_andCost (n t : Nat)
    (circuit : Circuit DeMorgan.signature (n * n + n * n) (n * n))
    (nots : circuit.cost DeMorgan.notCost ≤ t)
    (computes : ∀ (a : Fin (n * n + n * n) → Bool) i j,
      circuit.eval DeMorgan.interpretation a (productEntry n i j) =
        decide (∃ k, a (leftEntry n i k) = true ∧ a (rightEntry n k j) = true)) :
    n * (n / 2 ^ t) ^ 2 ≤ circuit.cost DeMorgan.andCost := by
  have := div_mul_div_mul_le_andCost t (leftEntry n) (rightEntry n) (entry_injective n)
    (productEntry n) circuit nots computes
  calc n * (n / 2 ^ t) ^ 2 = n / 2 ^ t * (n / 2 ^ t) * n := by ring
    _ ≤ _ := this

/-- **Negations needed for a sub-cubic product.** If a De Morgan circuit with at
most `t` NOT gates computes the Boolean product of two `n × n` matrices and
`2 ^ t ≤ n`, then `n ^ 3 ≤ 4 ^ (t + 1) * #AND`. Equivalently, a circuit with
fewer than `n ^ 3 / 4 ^ (t + 1)` AND gates has more than `t` NOT gates, or
`n < 2 ^ t`. -/
theorem cube_le_four_pow_mul_andCost (n t : Nat)
    (circuit : Circuit DeMorgan.signature (n * n + n * n) (n * n))
    (nots : circuit.cost DeMorgan.notCost ≤ t)
    (computes : ∀ (a : Fin (n * n + n * n) → Bool) i j,
      circuit.eval DeMorgan.interpretation a (productEntry n i j) =
        decide (∃ k, a (leftEntry n i k) = true ∧ a (rightEntry n k j) = true))
    (large : 2 ^ t ≤ n) :
    n ^ 3 ≤ 4 ^ (t + 1) * circuit.cost DeMorgan.andCost := by
  have hbound := mul_div_sq_le_andCost n t circuit nots computes
  set q := n / 2 ^ t
  have hq : 1 ≤ q := (Nat.one_le_div_iff (Nat.two_pow_pos t)).2 large
  have hpq : 2 ^ t ≤ 2 ^ t * q := Nat.le_mul_of_pos_right _ hq
  have hn : n ≤ 2 ^ (t + 1) * q := by
    have hdiv := Nat.div_add_mod n (2 ^ t)
    have hmod := Nat.mod_lt n (Nat.two_pow_pos t)
    rw [Nat.pow_succ]
    calc n = 2 ^ t * q + n % 2 ^ t := hdiv.symm
      _ ≤ 2 ^ t * q + 2 ^ t * q := by omega
      _ = 2 ^ t * 2 * q := by ring
  calc n ^ 3 = n * n * n := by ring
    _ ≤ n * (2 ^ (t + 1) * q) * (2 ^ (t + 1) * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul le_rfl hn) hn
    _ = 4 ^ (t + 1) * (n * q ^ 2) := by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]
      ring
    _ ≤ 4 ^ (t + 1) * circuit.cost DeMorgan.andCost := Nat.mul_le_mul_left _ hbound

/-- **Boolean matrix product with negations of few variables.** Place the
entries of an `I × K` matrix and a `K × J` matrix at distinct inputs of a De
Morgan circuit whose output `z i j` computes `⋁ k, x i k ∧ y k j` for every `i`
and `j`. If every NOT gate computes a function of the inputs in `S`, the
circuit has at least `I * J * K - |S| * max I J` AND gates. -/
theorem mul_mul_le_andCost_add {N M I J K : Nat}
    (x : Fin I → Fin K → Fin N) (y : Fin K → Fin J → Fin N)
    (distinct : Function.Injective (Sum.elim (Function.uncurry x) (Function.uncurry y)))
    (z : Fin I → Fin J → Fin M) (circuit : Circuit DeMorgan.signature N M)
    (computes : ∀ (a : Fin N → Bool) i j,
      circuit.eval DeMorgan.interpretation a (z i j) =
        decide (∃ k, a (x i k) = true ∧ a (y k j) = true))
    (S : Finset (Fin N))
    (localized : ∀ G, (circuit.program.lines G).op = .not →
      DependsOnlyOn (circuit.program.gateFunction DeMorgan.interpretation G) S) :
    I * J * K ≤ circuit.cost DeMorgan.andCost + S.card * max I J :=
  Internal.mul_mul_le_andCost_add (.ofInjective x y distinct) z circuit computes S localized

/-- **Square Boolean matrix product with negations of few variables.** If every
NOT gate of a De Morgan circuit computing the Boolean product of two `n × n`
matrices, in the row-major layout of `cube_le_andCost`, computes a function of
the inputs in `S`, the circuit has at least `n ^ 3 - |S| * n` AND gates. -/
theorem cube_sub_le_andCost (n : Nat)
    (circuit : Circuit DeMorgan.signature (n * n + n * n) (n * n))
    (computes : ∀ (a : Fin (n * n + n * n) → Bool) i j,
      circuit.eval DeMorgan.interpretation a (productEntry n i j) =
        decide (∃ k, a (leftEntry n i k) = true ∧ a (rightEntry n k j) = true))
    (S : Finset (Fin (n * n + n * n)))
    (localized : ∀ G, (circuit.program.lines G).op = .not →
      DependsOnlyOn (circuit.program.gateFunction DeMorgan.interpretation G) S) :
    n ^ 3 - S.card * n ≤ circuit.cost DeMorgan.andCost := by
  have := mul_mul_le_andCost_add (leftEntry n) (rightEntry n) (entry_injective n)
    (productEntry n) circuit computes S localized
  rw [max_self, show n * n * n = n ^ 3 by ring] at this
  omega

end NegationLimited
end MatrixProduct
end Monotone
end Algebraic
