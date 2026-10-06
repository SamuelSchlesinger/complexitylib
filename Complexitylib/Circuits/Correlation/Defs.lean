/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Bias
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Pi

/-!
# Quadratic forms over `GF(2)` and their ranks -- definitions

The hard functions of the correlation bounds are quadratic forms over the field with two
elements. An input `x : ι → Bool` is read coordinatewise as a vector over `ZMod 2`
(`Correlation.bit`), and a square matrix `Q` defines the Boolean function
`x ↦ ∑ i, ∑ j, Q i j x_i x_j` (`Correlation.quadForm`). Only the polar matrix `Q + Qᵀ`
matters for correlation with circuits: cutting the coordinates into `U` and `Uᶜ`, the form
is a function of the `U`-part, plus a function of the `Uᶜ`-part, plus the bilinear pairing
of the two parts through the block of `Q + Qᵀ` with rows `U` and columns `Uᶜ`. The rank of
that block is the *cut rank* of `Q` at `U` (`Correlation.cutRank`).

Ranks of blocks are the dimension over `ZMod 2` of the span of their rows
(`Correlation.blockRank`); this needs no `Fintype` instance on the index sets. A matrix is
*submatrix-robust* with deficiency `t` (`Correlation.SubmatrixRobust`) when every square
block with `k` rows has rank at least `k - t`.

The explicit family is a bilinear form `xᵀ R y` (`Correlation.bilinForm`): on inputs of
length `n` the left half `x` consists of the first `⌊n/2⌋` coordinates, the right half `y`
of the next `⌊n/2⌋`, and for odd `n` the last coordinate is ignored.

## Main definitions

* `Correlation.bit`, `Correlation.quadForm`: a quadratic form as a Boolean function.
* `Correlation.blockRank`, `Correlation.cutRank`: ranks of blocks and cut ranks.
* `Correlation.SubmatrixRobust`: every square block is nearly of full rank.
* `Correlation.leftIdx`, `Correlation.rightIdx`, `Correlation.bilinForm`: the bilinear
  form `xᵀ R y` on inputs of length `n`.
-/

@[expose] public section

namespace Complexity.Correlation

variable {ι κ : Type*}

/-- The *correlation* of two Boolean functions on a finite domain:
`|Pr[f = g] - Pr[f ≠ g]| = |2 · agreement f g - 1|`. -/
noncomputable def correlation {α : Type*} (f g : α → Bool) : ℝ :=
  |2 * Frontier.agreement f g - 1|

/-- A bit read as `0` or `1` in `ZMod 2`. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The quadratic form of a square matrix `Q` over `GF(2)`, as a Boolean function: an input
`x` is mapped to `∑ i, ∑ j, Q i j x_i x_j`. -/
def quadForm [Fintype ι] (Q : Matrix ι ι (ZMod 2)) (x : ι → Bool) : Bool :=
  decide (∑ i, ∑ j, Q i j * bit (x i) * bit (x j) = 1)

/-- The rank over `GF(2)` of the block of `M` with rows `S` and columns `T`: the dimension of
the span of its rows, each a vector indexed by `T`. -/
noncomputable def blockRank (M : Matrix ι κ (ZMod 2)) (S : Set ι) (T : Set κ) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i : S => fun j : T => M i j))

/-- The *cut rank* of `Q` at `U`: the rank of the block of the polar matrix `Q + Qᵀ` with rows
`U` and columns `Uᶜ`. For a symmetric zero-diagonal matrix, the adjacency matrix of a graph,
this is the cut rank of `U` in the graph. -/
noncomputable def cutRank (Q : Matrix ι ι (ZMod 2)) (U : Set ι) : ℕ :=
  blockRank (Q + Q.transpose) U Uᶜ

/-- `R` is *submatrix-robust* with deficiency `t`: every square block of `R`, with `k` rows
and `k` columns, has rank at least `k - t`. -/
def SubmatrixRobust (R : Matrix ι κ (ZMod 2)) (t : ℕ) : Prop :=
  ∀ (S : Set ι) (T : Set κ), S.ncard = T.ncard → S.ncard ≤ blockRank R S T + t

/-- The deficiency `2 ⌊√m⌋ + 1`: submatrix-robust `m × m` matrices with this deficiency exist
(`Correlation.exists_submatrixRobust`). -/
def robustDeficiency (m : ℕ) : ℕ := 2 * Nat.sqrt m + 1

/-- The coordinate of an input of length `n` that holds the entry `a` of its left half. -/
def leftIdx (n : ℕ) (a : Fin (n / 2)) : Fin n :=
  ⟨a, by omega⟩

/-- The coordinate of an input of length `n` that holds the entry `b` of its right half. -/
def rightIdx (n : ℕ) (b : Fin (n / 2)) : Fin n :=
  ⟨n / 2 + b, by omega⟩

/-- The bilinear form `xᵀ R y` on inputs of length `n`, where `x` is the left half (the first
`⌊n/2⌋` coordinates) and `y` the right half (the next `⌊n/2⌋`). For odd `n` the last
coordinate is ignored. -/
def bilinForm {n : ℕ} (R : Matrix (Fin (n / 2)) (Fin (n / 2)) (ZMod 2)) (x : Fin n → Bool) :
    Bool :=
  decide (∑ a, ∑ b, R a b * bit (x (leftIdx n a)) * bit (x (rightIdx n b)) = 1)

/-- The `n × n` matrix with `R` in the block whose rows are the left half and whose columns are
the right half, and zeros elsewhere. -/
def bipartiteMatrix (n : ℕ) (R : Matrix (Fin (n / 2)) (Fin (n / 2)) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) := fun i j =>
  ∑ a, ∑ b, if leftIdx n a = i ∧ rightIdx n b = j then R a b else 0

end Complexity.Correlation
