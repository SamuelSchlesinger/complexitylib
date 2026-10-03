/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program
import Complexitylib.Tactic.PolyTime

/-!
# Exact evaluation and uniform complexity of the first affine phase

The canonical equation composes the checked component equations, including
false completion of short initial seeds. Polynomial time holds on arbitrary
strings and unary parameters, without component guards. The last component
also bounds every output length independently of the preceding outputs.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem affinePhaseOneFirstSeedWord_length (L₀ : Nat) (y : List Bool) :
    (affinePhaseOneFirstSeedWord L₀ y).length = matchedBlockSeedBits L₀ := by
  simp only [affinePhaseOneFirstSeedWord, List.length_take, List.length_append,
    List.length_replicate]
  exact min_eq_left (by lia)

theorem affinePhaseOneFirstSeed_ofFn (d L₀ : Nat) (y : Fin d → Bool) :
    List.ofFn (affinePhaseOneFirstSeed d L₀ y) =
      affinePhaseOneFirstSeedWord L₀ (List.ofFn y) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, affinePhaseOneFirstSeedWord_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, affinePhaseOneFirstSeed,
      affinePhaseOneFirstSeedWord, List.getElem_take]
    by_cases inside : i < (List.ofFn y).length
    · rw [List.getElem?_eq_getElem inside, Option.getD_some,
        List.getElem_append_left inside]
    · rw [List.getElem?_eq_none (by lia), Option.getD_none,
        List.getElem_append_right (by lia), List.getElem_replicate]

theorem affinePhaseOneRuntime_eq_affinePhaseOneOutput (n d t L₀ e₀ L₁ e₁ er : Nat)
    (first : MatchedBlockRuntimeValid n 64 L₀ e₀)
    (adviceGuard : FlipFlopSizeGuard d (matchedBlockOutputBits 64 L₀) L₁ e₁)
    (last : GrowingMatchedBlockRuntimeValid n t L₁ er)
    (x : Fin n → Bool) (y : Fin d → Bool) (advice : List Bool) :
    affinePhaseOneRuntime t L₀ e₀ L₁ e₁ er (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (affinePhaseOneOutput n d (growingMatchedBlockDepth t)
        L₀ e₀ L₁ e₁ er x y advice) := by
  dsimp only [affinePhaseOneRuntime]
  rw [← affinePhaseOneFirstSeed_ofFn,
    matchedBlockExtractorRuntime_eq_matchedBlockExtractor n 64 L₀ e₀ first,
    adviceCorrelationBreakerRuntime_eq d (matchedBlockOutputBits 64 L₀) L₁ e₁ adviceGuard,
    growingMatchedBlockExtractorRuntime_eq_matchedBlockExtractor n t L₁ er last]
  rfl

theorem affinePhaseOneRuntime_length (t L₀ e₀ L₁ e₁ er : Nat) (x y advice : List Bool) :
    (affinePhaseOneRuntime t L₀ e₀ L₁ e₁ er x y advice).length =
      if GrowingMatchedBlockRuntimeValid x.length t L₁ er then
        2 ^ growingMatchedBlockDepth t * L₁ else 0 :=
  growingMatchedBlockExtractorRuntime_length _ _ _ _ _

theorem affinePhaseOneRuntime_length_le (t L₀ e₀ L₁ e₁ er : Nat) (x y advice : List Bool) :
    (affinePhaseOneRuntime t L₀ e₀ L₁ e₁ er x y advice).length ≤ 2 ^ 65 * (t + 1) * L₁ :=
  growingMatchedBlockExtractorRuntime_length_le _ _ _ _ _

theorem affinePhaseOneFirstSeedWord_mem_FP {L₀ : List Bool → Nat}
    {y : List Bool → List Bool} (hL₀ : UnaryFn L₀) (hy : y ∈ FP) :
    (fun z => affinePhaseOneFirstSeedWord (L₀ z) (y z)) ∈ FP := by
  polytime [affinePhaseOneFirstSeedWord, matchedBlockSeedBits]

theorem affinePhaseOneRuntime_mem_FP {t L₀ e₀ L₁ e₁ er : List Bool → Nat}
    {x y advice : List Bool → List Bool}
    (ht : UnaryFn t) (hL₀ : UnaryFn L₀) (he₀ : UnaryFn e₀)
    (hL₁ : UnaryFn L₁) (he₁ : UnaryFn e₁) (her : UnaryFn er)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affinePhaseOneRuntime (t z) (L₀ z) (e₀ z) (L₁ z) (e₁ z) (er z)
      (x z) (y z) (advice z)) ∈ FP := by
  have seed := affinePhaseOneFirstSeedWord_mem_FP hL₀ hy
  polytime [affinePhaseOneRuntime]

theorem affinePhaseOneEval_pair (x y advice parameter firstScale firstError
    secondScale secondError finalError : List Bool) :
    affinePhaseOneEval (pair (pair x (pair y advice))
      (pair parameter (pair (pair firstScale firstError)
        (pair secondScale (pair secondError finalError))))) =
      affinePhaseOneRuntime parameter.length firstScale.length firstError.length
        secondScale.length secondError.length finalError.length x y advice := by
  simp only [affinePhaseOneEval, pairFst_pair, pairSnd_pair]

theorem affinePhaseOneEval_mem_FP : affinePhaseOneEval ∈ FP := by
  unfold affinePhaseOneEval
  apply affinePhaseOneRuntime_mem_FP <;> polytime

theorem affinePhaseOneEval_length_le (z : List Bool) :
    (affinePhaseOneEval z).length ≤ 2 ^ 65 * (z.length + 1) ^ 2 := by
  have parameter := (pairFst_length_le (pairSnd z)).trans (pairSnd_length_le z)
  have scale := (pairFst_length_le (pairSnd (pairSnd (pairSnd z)))).trans
    ((pairSnd_length_le (pairSnd (pairSnd z))).trans
      ((pairSnd_length_le (pairSnd z)).trans (pairSnd_length_le z)))
  calc
    (affinePhaseOneEval z).length ≤
        2 ^ 65 * ((pairFst (pairSnd z)).length + 1) *
          (pairFst (pairSnd (pairSnd (pairSnd z)))).length :=
      affinePhaseOneRuntime_length_le _ _ _ _ _ _ _ _ _
    _ ≤ 2 ^ 65 * (z.length + 1) * (z.length + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right parameter 1))
        (scale.trans (Nat.le_succ _))
    _ = 2 ^ 65 * (z.length + 1) ^ 2 := by ring

end Algebraic.Cutwidth.Extractor.Internal
