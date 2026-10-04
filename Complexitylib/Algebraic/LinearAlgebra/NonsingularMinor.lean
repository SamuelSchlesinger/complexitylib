/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Complexitylib.Algebraic.LinearAlgebra.NonsingularMinor.Internal

/-!
# Nonsingular minors: dominant weights and block-diagonal minors

Two certificates that a square matrix is nonsingular, or that a matrix has large rank.

* **Dominance.** A nonempty sum `∑ ±2^{E x}` with pairwise distinct exponents is nonzero
  (`Algebraic.sum_mul_two_pow_ne_zero`): the term with the least exponent is not divisible by
  the next power of `2`, while all the others are.
* **Doubly exponential weights.** Let `M` be a square matrix over a commutative ring of
  characteristic zero whose nonzero entries are `±2^{2^{L i j}}`, where the labels `L i j` of the
  nonzero entries are pairwise distinct, and suppose some permutation `σ` has `M (σ j) j ≠ 0`
  for every `j` (the support of `M` contains a perfect matching). Then `det M ≠ 0`
  (`Matrix.det_ne_zero_of_two_pow_two_pow`). Each permutation supported on the nonzero entries
  contributes `±2^{E σ}` to the Leibniz expansion with `E σ = ∑_j 2^{L (σ j) j}`, the binary
  number whose set bits are the labels used by `σ`; distinct labels make these exponents
  pairwise distinct, and dominance applies.
* **Block-diagonal minors.** If rows `f i b` and columns `g i b` of `A`, indexed by `i : ι` within
  each block `b : β`, give nonsingular square blocks and all entries between different blocks
  vanish, then `card ι * card β ≤ rank A`
  (`Matrix.card_mul_card_le_rank_of_det_blocks_ne_zero`).
-/

@[expose] public section

namespace Algebraic

/-- **Dominance.** A nonempty sum `∑ ε x * 2 ^ E x` with unit coefficients `ε x = ±1` and pairwise
distinct exponents `E x` is nonzero. -/
theorem sum_mul_two_pow_ne_zero {κ : Type*} {s : Finset κ} (hs : s.Nonempty) {ε : κ → ℤ}
    (hε : ∀ x ∈ s, IsUnit (ε x)) {E : κ → ℕ} (hE : Set.InjOn E s) :
    ∑ x ∈ s, ε x * 2 ^ E x ≠ 0 :=
  NonsingularMinor.Internal.sum_mul_two_pow_ne_zero hs hε hE

end Algebraic

namespace Matrix

/-- **Nonsingularity from doubly exponential weights.** Let `M` be a square matrix over a
commutative ring of characteristic zero whose nonzero entries are `±2^{2^{L i j}}`, with labels
`L i j` that are pairwise distinct on the nonzero entries. If some permutation `σ` has
`M (σ j) j ≠ 0` for every `j`, then `det M ≠ 0`. -/
theorem det_ne_zero_of_two_pow_two_pow {R : Type*} [CommRing R] [CharZero R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (L : ι → ι → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → M i j = 2 ^ 2 ^ L i j ∨ M i j = -2 ^ 2 ^ L i j)
    (hL : ∀ i j i' j', M i j ≠ 0 → M i' j' ≠ 0 → L i j = L i' j' → i = i' ∧ j = j')
    (σ : Equiv.Perm ι) (hσ : ∀ j, M (σ j) j ≠ 0) : M.det ≠ 0 :=
  Algebraic.NonsingularMinor.Internal.det_ne_zero_of_two_pow_two_pow M L hM hL σ hσ

/-- **Block-diagonal minors.** Choose, for each block `b : β`, rows `f i b` and columns `g i b` of
`A` indexed by `i : ι`. If every entry between different blocks vanishes and every block
`A.submatrix (f · b) (g · b)` is nonsingular, then `card ι * card β ≤ rank A`. -/
theorem card_mul_card_le_rank_of_det_blocks_ne_zero {K : Type*} [Field K] {m n : Type*}
    [Fintype n] {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (A : Matrix m n K) (f : ι → β → m) (g : ι → β → n)
    (hoff : ∀ i i' b b', b ≠ b' → A (f i b) (g i' b') = 0)
    (hdet : ∀ b, (A.submatrix (f · b) (g · b)).det ≠ 0) :
    Fintype.card ι * Fintype.card β ≤ A.rank :=
  Algebraic.NonsingularMinor.Internal.card_mul_card_le_rank_of_det_blocks_ne_zero A f g hoff
    hdet

end Matrix
