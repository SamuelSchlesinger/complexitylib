/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Basic.Real.Basic

/-!
# The deletion game: definitions

Definitions for the deletion game of
`Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame`, the global step of a border-rank
lower bound for tensors with `m = 2k + 1` slices `Fin (2 * k + 1)`, by border substitution
(`Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution`).

* `DeletionGame.offset k a = a - k ∈ [-k, k]` is the offset of the slice `a`.
* `DeletionGame.sideBlock f L i` is the set of slices `a` with `i L + 1 ≤ f a ≤ (i + 1) L`.
  The positive blocks `DeletionGame.posBlock k L i` (offsets in `[i L + 1, (i + 1) L]`) and the
  negative blocks `DeletionGame.negBlock k L i` (offsets in `[-(i + 1) L, -(i L + 1)]`) split
  the offsets `1, …, k` and `-1, …, -k` into consecutive runs of length `L`, the last one
  possibly shorter. A block `B` is *good* for a set `S` of surviving slices if
  `R ≤ card (S ∩ B)`.
* `DeletionGame.phi n r s = max (max (n - r) (n - s)) (max (r + s) (2 * min (r + s) (n - r - s)))`
  is the width function `Φ_n(r, s)` of a positive cluster at offset `r` paired with a negative
  cluster at offset `-s`.
* `DeletionGame.PairedClusterBound k L R D E LB` is the paired-cluster hypothesis on a
  function `LB` on sets of slices: whenever a positive block `B⁺` and a negative block `B⁻` are
  both good for `S`, some offsets `r` in `B⁺` and `-s` in `B⁻` satisfy
  `D * (Φ_{2k+1}(r, s) - E) ≤ LB S`. For the Koszul certificate of paired clusters of
  `2p + 1` slices, `D = (2p + 1) / (p + 1)` and `E = O(p L)`.
-/

@[expose] public section

namespace Algebraic.Tensor3.DeletionGame

open Finset

/-- The offset `a - k ∈ [-k, k]` of the slice `a` among the `2k + 1` slices `Fin (2 * k + 1)`. -/
def offset (k : ℕ) (a : Fin (2 * k + 1)) : ℤ :=
  (a : ℤ) - k

/-- The block of index `i` and length `L` on the side described by `f`: the elements `a` with
`i L + 1 ≤ f a ≤ (i + 1) L`. -/
def sideBlock {α : Type*} [Fintype α] (f : α → ℤ) (L i : ℕ) : Finset α :=
  univ.filter fun a => (i * L + 1 : ℤ) ≤ f a ∧ f a ≤ (i + 1) * L

/-- The positive block of index `i`: the slices with offset in `[i L + 1, (i + 1) L]`. -/
def posBlock (k L i : ℕ) : Finset (Fin (2 * k + 1)) :=
  sideBlock (offset k) L i

/-- The negative block of index `i`: the slices with offset in `[-(i + 1) L, -(i L + 1)]`. -/
def negBlock (k L i : ℕ) : Finset (Fin (2 * k + 1)) :=
  sideBlock (fun a => -offset k a) L i

/-- The width function `Φ_n(r, s) = max {n - r, n - s, r + s, 2 min (r + s, n - r - s)}` of a
positive cluster at offset `r` paired with a negative cluster at offset `-s`, in an `n × n`
square. -/
def phi (n r s : ℤ) : ℤ :=
  max (max (n - r) (n - s)) (max (r + s) (2 * min (r + s) (n - r - s)))

/-- **The paired-cluster hypothesis.** For every set `S` of slices and every positive block
`posBlock k L i` and negative block `negBlock k L j` that are both good for `S` (at least `R`
of their slices lie in `S`), some slice `a` of the positive block and some slice `b` of the
negative block satisfy `D * (Φ_{2k+1}(offset a, -offset b) - E) ≤ LB S`. -/
def PairedClusterBound (k L R : ℕ) (D E : ℝ) (LB : Finset (Fin (2 * k + 1)) → ℕ) : Prop :=
  ∀ (S : Finset (Fin (2 * k + 1))) (i j : ℕ), R ≤ (S ∩ posBlock k L i).card →
    R ≤ (S ∩ negBlock k L j).card →
      ∃ a ∈ posBlock k L i, ∃ b ∈ negBlock k L j,
        D * ((phi (2 * k + 1) (offset k a) (-offset k b) : ℝ) - E) ≤ LB S

end Algebraic.Tensor3.DeletionGame
