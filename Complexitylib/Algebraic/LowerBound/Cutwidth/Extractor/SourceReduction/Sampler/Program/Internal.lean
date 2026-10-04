/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.Linarith

/-!
# Correctness and uniform computation of the amplified sampler

The two component evaluator equalities compose on canonical words. Only
the growing matched guard is needed for this identity; Gamma agrees with
its own total Boolean map on every size. Prefix completion preserves the
exact requested output length even when the component returns no bits.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

private theorem prefix_ofFn (d : Nat) (bits : List Bool) :
    List.ofFn (fun i : Fin d => bits[i.val]?.getD false) =
      (bits ++ List.replicate d false).take d := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_append, List.length_replicate]
    exact (min_eq_left (by lia)).symm
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_take]
    by_cases inside : i < bits.length
    · rw [List.getElem?_eq_getElem inside, Option.getD_some, List.getElem_append_left inside]
    · rw [List.getElem?_eq_none (by lia), Option.getD_none,
        List.getElem_append_right (by lia), List.getElem_replicate]

theorem amplifiedMatchedSamplerRuntime_length (L d : Nat) (source outer candidate : List Bool) :
    (amplifiedMatchedSamplerRuntime L d source outer candidate).length = d := by
  simp only [amplifiedMatchedSamplerRuntime, List.length_take, List.length_append,
    List.length_replicate]
  exact min_eq_left (by lia)

theorem amplifiedMatchedSamplerRuntime_eq_amplifiedMatchedSampler (n L d : Nat)
    (base : GrowingMatchedBlockRuntimeValid n d L 4) (x : Fin n → Bool)
    (outer : Fin (8 * matchedBlockSeedBits L) → Bool)
    (candidate : Fin (gammaBlockSeedBudget (matchedBlockSeedBits L)) → Bool) :
    amplifiedMatchedSamplerRuntime L d (List.ofFn x) (List.ofFn outer) (List.ofFn candidate) =
      List.ofFn (amplifiedMatchedSampler n L d x outer candidate) := by
  unfold amplifiedMatchedSamplerRuntime
  dsimp only
  rw [← gammaBlockPaddedExtractor_ofFn,
    growingMatchedBlockExtractorRuntime_eq_matchedBlockExtractor n d L 4 base]
  exact (prefix_ofFn d _).symm

theorem amplifiedMatchedSamplerRuntime_mem_FP {L d : List Bool → Nat}
    {source outer candidate : List Bool → List Bool} (hL : UnaryFn L) (hd : UnaryFn d)
    (hsource : source ∈ FP) (houter : outer ∈ FP) (hcandidate : candidate ∈ FP) :
    (fun z => amplifiedMatchedSamplerRuntime (L z) (d z)
      (source z) (outer z) (candidate z)) ∈ FP := by
  polytime [amplifiedMatchedSamplerRuntime, matchedBlockSeedBits]

theorem amplifiedMatchedSamplerEval_pair (source outer candidate scale outputWidth : List Bool) :
    amplifiedMatchedSamplerEval
      (pair (pair source (pair outer candidate)) (pair scale outputWidth)) =
      amplifiedMatchedSamplerRuntime scale.length outputWidth.length source outer candidate := by
  simp only [amplifiedMatchedSamplerEval, pairFst_pair, pairSnd_pair]

theorem amplifiedMatchedSamplerEval_length (z : List Bool) :
    (amplifiedMatchedSamplerEval z).length = (pairSnd (pairSnd z)).length :=
  amplifiedMatchedSamplerRuntime_length _ _ _ _ _

theorem amplifiedMatchedSamplerEval_length_le (z : List Bool) :
    (amplifiedMatchedSamplerEval z).length ≤ z.length := by
  rw [amplifiedMatchedSamplerEval_length]
  exact (pairSnd_length_le _).trans (pairSnd_length_le _)

theorem amplifiedMatchedSamplerEval_mem_FP : amplifiedMatchedSamplerEval ∈ FP := by
  unfold amplifiedMatchedSamplerEval
  apply amplifiedMatchedSamplerRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
