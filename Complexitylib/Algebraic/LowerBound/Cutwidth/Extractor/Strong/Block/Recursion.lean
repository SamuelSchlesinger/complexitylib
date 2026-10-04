/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Internal.Bounds

/-!
# Finite recursive block-source guarantee

The deterministic `recursiveBlockMap` carries an initial retained-seed
approximation through any finite number of condense-and-split levels.
The alphabets, seed types, entropy thresholds, and errors may vary by level.
The output has `2^n*t` blocks, and the previous joint error increases by
the explicit sum `recursiveBlockError`. No bound for each individual seed
is assumed. All local condenser and entropy hypotheses concern only levels
strictly below `n`.

The seed-cardinality formula counts each level's seed once. `Recursion.Scheduled`
supplies a concrete short-seed parameter schedule (`eventually_polylogBlockExtractor`)
and a uniform encoded evaluator (`scheduledBlockExtractorEval_mem_FP`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u v w

/-- The number of blocks doubles at every completed level. -/
theorem recursiveBlockCount_eq (t n : Nat) : recursiveBlockCount t n = 2 ^ n * t :=
  Internal.recursiveBlockCount_eq t n

/-- Each fresh seed is counted once, regardless of the number of blocks using it. -/
theorem recursiveSeeds_card (Earlier : Type u) (Fresh : Nat → Type u)
    [Fintype Earlier] [∀ i, Fintype (Fresh i)] (n : Nat) :
    Fintype.card (RecursiveSeeds Earlier Fresh n) =
      Fintype.card Earlier * ∏ i ∈ Finset.range n, Fintype.card (Fresh i) :=
  Internal.recursiveSeeds_card Earlier Fresh n

/-- For power-of-two seed alphabets, seed widths add over the completed levels. -/
theorem recursiveSeeds_card_pow_two (Earlier : Type u) (Fresh : Nat → Type u)
    [Fintype Earlier] [∀ i, Fintype (Fresh i)] (n b₀ : Nat) (b : Nat → Nat)
    (first : Fintype.card Earlier = 2 ^ b₀)
    (fresh : ∀ i < n, Fintype.card (Fresh i) = 2 ^ b i) :
    Fintype.card (RecursiveSeeds Earlier Fresh n) = 2 ^ (b₀ + ∑ i ∈ Finset.range n, b i) :=
  Internal.recursiveSeeds_card_pow_two Earlier Fresh n b₀ b first fresh

/-- Constant local errors have an exact finite geometric sum. -/
theorem recursiveBlockError_const (t n e : Nat) (ε : ℝ) :
    recursiveBlockError t (fun _ => ε) (fun _ => e) n =
      (t : ℝ) * ((2 : ℝ) ^ n - 1) * (ε + ((2 : ℝ) ^ e)⁻¹) :=
  Internal.recursiveBlockError_const t n e ε

/-- One initial error, two local errors per internal block, and one per leaf
give the finite coefficient `3*2^h-1`. -/
theorem recursiveBlockError_dyadic_total (h E : Nat) :
    ((2 : ℝ) ^ E)⁻¹ +
        recursiveBlockError 1 (fun _ => ((2 : ℝ) ^ E)⁻¹) (fun _ => E) h +
        (recursiveBlockCount 1 h : ℝ) * ((2 : ℝ) ^ E)⁻¹ =
      (3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹ :=
  Internal.recursiveBlockError_dyadic_total h E

/-- Increasing each error exponent by `h+2` pays for all `h` recursive levels. -/
theorem recursiveBlockError_dyadic_budget (h e : Nat) :
    (3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ (e + h + 2))⁻¹ ≤ ((2 : ℝ) ^ e)⁻¹ :=
  Internal.recursiveBlockError_dyadic_budget h e

/-- The actual recursive map has a nearby conditional block-source witness,
with the initial joint error and all local errors accounted for explicitly. -/
theorem exists_recursiveBlockSource {X : Type v} {Earlier : Type u}
    {Fresh : Nat → Type u} {α : Nat → Type w}
    [Fintype X] [Fintype Earlier] [Nonempty Earlier]
    [∀ i, Fintype (Fresh i)] [∀ i, Nonempty (Fresh i)] [∀ i, Fintype (α i)]
    {t : Nat} (initial : X → Earlier → (Fin t → α 0))
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1))
    (k m e : Nat → Nat) (ε : Nat → ℝ) (n : Nat)
    (p : X → ℝ) (q₀ : Earlier → (Fin t → α 0) → ℝ) {η : ℝ}
    (sources : ∀ y, IsBlockSource (q₀ y) (2 ^ k 0))
    (close : weightDist (weightedSeededOutput p initial) (seedFamilyWeight q₀) ≤ η)
    (condensers : ∀ i < n, WeightedStrongSeededCondenser (C i) (2 ^ k i) (2 ^ k i) (ε i))
    (cards : ∀ i < n, Fintype.card (α (i + 1)) = 2 ^ m i)
    (widths : ∀ i < n, k (i + 1) ≤ m i)
    (entropies : ∀ i < n, m i + k (i + 1) + e i ≤ k i) :
    ∃ q : RecursiveSeeds Earlier Fresh n → (Fin (recursiveBlockCount t n) → α n) → ℝ,
      (∀ y, IsBlockSource (q y) (2 ^ k n)) ∧
        weightDist (weightedSeededOutput p (recursiveBlockMap initial C n))
          (seedFamilyWeight q) ≤ η + recursiveBlockError t ε e n :=
  Internal.exists_recursiveBlockSource initial C k m e ε n p q₀ sources close
    condensers cards widths entropies

end Algebraic.Cutwidth.Extractor
