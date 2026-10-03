/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction.Internal

/-!
# Strong extraction by a finite recursive block program

An initial condenser, the supplied sequence of lossless condensers and
entropy budgets, and a final strong extractor give a strong extractor for
the actual deterministic recursive composition. Its tests retain every
initial, level, and final seed, once each. No initial ideal witness is a
premise: the initial condenser supplies that witness for every source.

The error is the initial error, the explicit internal block-error sum, and
one final extraction error per leaf. Giving every local error exponent
`e+n+2` bounds the total by `2^(-e)`. These are finite statistical statements
for supplied components in the recursion of Chattopadhyay--Goodman--Liao,
Theorem 5.6 of *Affine Extractors for Almost Logarithmic Entropy*,
<https://eccc.weizmann.ac.il/report/2021/075/>. A concrete short-seed schedule
and a uniform encoded evaluator remain separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u v w z r

/-- The actual recursive map extracts strongly from the initial input threshold,
with all internal and leaf errors included in its retained-seed test bound. -/
theorem WeightedStrongSeededCondenser.recursiveExtractor
    {X : Type v} {Earlier : Type u} {Fresh : Nat → Type u} {α : Nat → Type w}
    {Last : Type z} {Ω : Type r}
    [Fintype X] [Fintype Earlier] [Nonempty Earlier]
    [∀ i, Fintype (Fresh i)] [∀ i, Nonempty (Fresh i)] [∀ i, Fintype (α i)]
    [Fintype Last] [Nonempty Last] [Fintype Ω] [Nonempty Ω]
    {initial : X → Earlier → α 0} {Kin : Nat} {k m e : Nat → Nat}
    {ε : Nat → ℝ} {ε₀ εL : ℝ} {n : Nat}
    (initial_cond : WeightedStrongSeededCondenser initial Kin (2 ^ k 0) ε₀)
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1))
    (condensers : ∀ i < n, WeightedStrongSeededCondenser (C i) (2 ^ k i) (2 ^ k i) (ε i))
    (cards : ∀ i < n, Fintype.card (α (i + 1)) = 2 ^ m i)
    (widths : ∀ i < n, k (i + 1) ≤ m i)
    (entropies : ∀ i < n, m i + k (i + 1) + e i ≤ k i)
    {E : α n → Last → Ω} (final_extract : WeightedStrongSeededExtractor E (2 ^ k n) εL) :
    WeightedStrongSeededExtractor (recursiveBlockExtractor initial C n E) Kin
      (ε₀ + recursiveBlockError 1 ε e n + (recursiveBlockCount 1 n : ℝ) * εL) :=
  Internal.weightedStrongSeededCondenser_recursiveExtractor
    initial_cond C condensers cards widths entropies final_extract

/-- Uniform local error exponent `e+n+2` pays for the initial, internal, and leaf stages. -/
theorem WeightedStrongSeededCondenser.recursiveExtractor_dyadic
    {X : Type v} {Earlier : Type u} {Fresh : Nat → Type u} {α : Nat → Type w}
    {Last : Type z} {Ω : Type r}
    [Fintype X] [Fintype Earlier] [Nonempty Earlier]
    [∀ i, Fintype (Fresh i)] [∀ i, Nonempty (Fresh i)] [∀ i, Fintype (α i)]
    [Fintype Last] [Nonempty Last] [Fintype Ω] [Nonempty Ω]
    {initial : X → Earlier → α 0} {Kin : Nat} {k m : Nat → Nat} {n e : Nat}
    (initial_cond : WeightedStrongSeededCondenser initial Kin (2 ^ k 0)
      (((2 : ℝ) ^ (e + n + 2))⁻¹))
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1))
    (condensers : ∀ i < n, WeightedStrongSeededCondenser (C i) (2 ^ k i) (2 ^ k i)
      (((2 : ℝ) ^ (e + n + 2))⁻¹))
    (cards : ∀ i < n, Fintype.card (α (i + 1)) = 2 ^ m i)
    (widths : ∀ i < n, k (i + 1) ≤ m i)
    (entropies : ∀ i < n, m i + k (i + 1) + (e + n + 2) ≤ k i)
    {E : α n → Last → Ω}
    (final_extract : WeightedStrongSeededExtractor E (2 ^ k n)
      (((2 : ℝ) ^ (e + n + 2))⁻¹)) :
    WeightedStrongSeededExtractor (recursiveBlockExtractor initial C n E) Kin
      (((2 : ℝ) ^ e)⁻¹) :=
  Internal.weightedStrongSeededCondenser_recursiveExtractor_dyadic
    initial_cond C condensers cards widths entropies final_extract

end Algebraic.Cutwidth.Extractor
