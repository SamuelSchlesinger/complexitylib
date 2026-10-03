/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Initial
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Extraction
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep

/-!
# Closing the finite recursive extraction argument

The initial condenser supplies its own one-block witnesses. Recursive
condensation and splitting propagate their joint approximation, and final
retained-seed extraction compares all leaf outputs with uniform. The
dyadic specialization sums every initial, internal, and leaf error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u v w z r

theorem weightedStrongSeededCondenser_recursiveExtractor
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
      (ε₀ + recursiveBlockError 1 ε e n + (recursiveBlockCount 1 n : ℝ) * εL) := by
  intro p probability cap T
  obtain ⟨q₀, sources₀, close₀⟩ := initial_cond.singleton p probability cap
  obtain ⟨q, sources, close⟩ := exists_recursiveBlockSource
    (fun x y (_ : Fin 1) => initial x y) C k m e ε n p q₀ sources₀ close₀
    condensers cards widths entropies
  have result := final_extract.retained_block_tests q
    (weightedSeededOutput p (recursiveBlockMap (fun x y (_ : Fin 1) => initial x y) C n))
    (probability.weightedSeededOutput _) sources close T
  rw [retainedSeedStep_weightedSeededOutput, weightTestProb_weightedSeededOutput] at result
  convert result using 1
  rfl

theorem weightedStrongSeededCondenser_recursiveExtractor_dyadic
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
      (((2 : ℝ) ^ e)⁻¹) := by
  have full := weightedStrongSeededCondenser_recursiveExtractor
    (e := fun _ => e + n + 2) (ε := fun _ => ((2 : ℝ) ^ (e + n + 2))⁻¹)
    initial_cond C condensers cards widths entropies final_extract
  intro p probability cap T
  refine (full p probability cap T).trans ?_
  rw [recursiveBlockError_dyadic_total]
  exact recursiveBlockError_dyadic_budget n e

end Algebraic.Cutwidth.Extractor.Internal
