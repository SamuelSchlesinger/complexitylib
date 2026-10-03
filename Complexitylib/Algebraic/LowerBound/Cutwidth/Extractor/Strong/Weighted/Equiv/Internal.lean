/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs

/-!
# Reindexing retained-seed extractor tests

Pull back each test along the product of the seed equivalence and inverse
output equivalence. The filtered seed counts and both finite alphabet
cardinalities are unchanged. No normalization by a positive denominator
is needed, so empty alphabets retain the existing zero-division convention.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_equiv {α Seed Seed' Ω Ω' : Type*}
    [Fintype α] [Fintype Seed] [Fintype Seed'] [Fintype Ω] [Fintype Ω']
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    (seed : Seed' ≃ Seed) (output : Ω ≃ Ω') :
    WeightedStrongSeededExtractor (fun a y => output (E a (seed y))) K ε := by
  classical
  intro p probability cap T
  let pull := seed.prodCongr output.symm
  have counts (a : α) :
      (Finset.univ.filter fun y : Seed' => (y, output (E a (seed y))) ∈ T).card =
        (Finset.univ.filter fun y : Seed => (y, E a y) ∈ T.map pull.toEmbedding).card := by
    apply Finset.card_equiv seed
    intro y
    simp [pull]
  have actual : weightedSeededTestProb p (fun a y => output (E a (seed y))) T =
      weightedSeededTestProb p E (T.map pull.toEmbedding) := by
    simp only [weightedSeededTestProb, counts, Fintype.card_congr seed]
  have uniform : uniformSeededTestProb (T.map pull.toEmbedding) = uniformSeededTestProb T := by
    simp only [uniformSeededTestProb, Finset.card_map,
      Fintype.card_congr seed, Fintype.card_congr output]
  rw [actual, ← uniform]
  exact extract p probability cap (T.map pull.toEmbedding)

end Algebraic.Cutwidth.Extractor.Internal
