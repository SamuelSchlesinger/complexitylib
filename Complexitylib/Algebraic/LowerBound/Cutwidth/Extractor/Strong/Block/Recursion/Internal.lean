/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Internal.Bounds
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep
import Mathlib.Tactic.Convert

/-!
# Induction over all retained-seed condense-and-split levels

The actual deterministic recursive map stays close to a conditional block
source after every level. Each new seed is independent of the complete old
joint law, and old approximation errors remain joint errors. The hypotheses
are required only for the finitely many levels that the program runs.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u v w

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
          (seedFamilyWeight q) ≤ η + recursiveBlockError t ε e n := by
  induction n with
  | zero =>
    refine ⟨q₀, sources, ?_⟩
    convert close using 1
    · rfl
    · simp [recursiveBlockError]
  | succ n ih =>
    obtain ⟨q, hq, error⟩ := ih
      (fun i hi => condensers i (Nat.lt_succ_of_lt hi))
      (fun i hi => cards i (Nat.lt_succ_of_lt hi))
      (fun i hi => widths i (Nat.lt_succ_of_lt hi))
      (fun i hi => entropies i (Nat.lt_succ_of_lt hi))
    obtain ⟨r, hr, bound⟩ := (condensers n (Nat.lt_succ_self n)).condenseSplit q
      (weightedSeededOutput p (recursiveBlockMap initial C n)) hq error
      (cards n (Nat.lt_succ_self n)) (widths n (Nat.lt_succ_self n))
      (entropies n (Nat.lt_succ_self n))
    refine ⟨r, hr, ?_⟩
    rw [retainedSeedStep_weightedSeededOutput] at bound
    rw [recursiveBlockError_succ]
    convert bound using 1
    · rfl
    · exact (add_assoc _ _ _).symm

end Algebraic.Cutwidth.Extractor.Internal
