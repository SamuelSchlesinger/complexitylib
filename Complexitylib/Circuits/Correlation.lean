/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Defs
public import Complexitylib.Circuits.Correlation.Internal.Classes

/-!
# Correlation of circuits with quadratic forms over `GF(2)`

For a quadratic form `f` over `GF(2)` and a cut `X` of the coordinates, Lindsey's lemma bounds
the signed sum of `(-1)^f` over every rectangle `R` for `X` by `√(|R| 2^{n - ρ(X)})`, where the
cut rank `ρ(X)` is the rank of the block of the polar matrix `Q + Qᵀ` with rows `X` and columns
`Xᶜ`. If the inputs are partitioned into `K` rectangle classes for one cut and a predictor is
constant on every class, Cauchy–Schwarz over the classes gives
`correlation² ≤ K · 2^{-ρ(X)}`. The frontier method's separator lemma supplies such partitions
for circuits.

## Main results

* `correlation_sq_mul_two_pow_cutRank_le`: correlation through rectangle classes.
-/

@[expose] public section

namespace Complexity.Correlation

open Complexity.Frontier

/-! ### Rectangle classes -/

/-- **Correlation through rectangle classes.** Let `g` be constant on the classes of `msg`, and
let every class be a rectangle for one cut `X` of the coordinates. Then the correlation of `g`
with the quadratic form of `Q` satisfies `correlation² · 2^{cutRank Q X} ≤ |M|`, where `M` is
the type of messages. This is Lindsey's lemma on each class and Cauchy–Schwarz over the
classes. -/
theorem correlation_sq_mul_two_pow_cutRank_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (ZMod 2)) (g : (ι → Bool) → Bool) {M : Type*} [Fintype M]
    [DecidableEq M] (msg : (ι → Bool) → M) (X : Set ι)
    (hg : ∀ x y, msg x = msg y → g x = g y)
    (hrect : ∀ x₀, ∃ (A : Set (X → Bool)) (B : Set (↥Xᶜ → Bool)),
      {x | msg x = msg x₀} = rectangle X A B) :
    correlation (quadForm Q) g ^ 2 * 2 ^ cutRank Q X ≤ Fintype.card M := by
  rw [correlation, sq_abs]
  exact sq_two_mul_agreement_sub_one_mul_le Q g msg X hg hrect

end Complexity.Correlation
