/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Extraction
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Internal
import Mathlib.Data.List.OfFn

/-!
# Weighted-source correctness of the actual one-shot program

An injective fixed-length encoding sends every flat source support to a
support of the same size. The checked flat program theorem therefore
applies, and the weighted-source extension keeps exactly the same error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem decodedOneShotExtractor_weightedStrongSeededExtractor (n ell e : Nat)
    {α : Type*} [Fintype α]
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))]
    (input : α ↪ List Bool) (source : ∀ x, (input x).length = n) :
    WeightedStrongSeededExtractor
      (fun x => decodedOneShotExtractor n ell e (input x))
      (2 ^ (ell + 2 * e)) (((2 : ℝ) ^ e)⁻¹) := by
  apply FlatStrongSeededExtractor.weightedStrongSeededExtractor _ (by positivity)
  intro P _ size T
  have length : ∀ bits ∈ P.map input, bits.length = n := by
    intro bits member
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp member
    exact source x
  have bound := decodedOneShotExtractor_flat n ell e (P.map input) length
    (by simpa only [Finset.card_map] using size) T
  rw [seededTestProb_support_eq_sum] at bound
  rw [seededTestProb_support_eq_sum
    (fun x => decodedOneShotExtractor n ell e (input x)) P T]
  simpa only [Finset.card_map, Finset.sum_map] using bound

theorem decodedOneShotExtractor_ofFn_weighted (n ell e : Nat)
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))] :
    WeightedStrongSeededExtractor
      (fun x : Fin n → Bool => decodedOneShotExtractor n ell e (List.ofFn x))
      (2 ^ (ell + 2 * e)) (((2 : ℝ) ^ e)⁻¹) :=
  decodedOneShotExtractor_weightedStrongSeededExtractor n ell e
    ⟨List.ofFn, List.ofFn_injective⟩ (fun _ => List.length_ofFn)

end Algebraic.Cutwidth.Extractor.Internal
