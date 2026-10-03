/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Unary
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.Linarith

/-!
# Total polynomial-time evaluation of the Gamma runtime

The size guard selects a certified full run or a zero-step run. Both branches
therefore satisfy the loop's resource contract before the final conditional
output is selected. Unconditional parameter generation and bounded powering
give one FP program; the statistical size guard is not an FP premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem gammaBlockExtractorRuntime_of_guard (b : Nat) (source seeds : List Bool)
    (guard : GammaBlockSizeGuard b) :
    gammaBlockExtractorRuntime b source seeds =
      (nearHalvingBlockExtractorBits (8 * b) (gammaBlockDepth b) (gammaBlockReserve b)
        (gammaBlockErrorExponent b) (gammaBlockLeafLength b) (gammaBlockDepth b)
        source seeds).take b := by
  simp only [gammaBlockExtractorRuntime, ite_eq_left guard]

theorem gammaBlockExtractorRuntime_of_not_guard (b : Nat) (source seeds : List Bool)
    (guard : ¬ GammaBlockSizeGuard b) :
    gammaBlockExtractorRuntime b source seeds = List.replicate b false := by
  simp only [gammaBlockExtractorRuntime, ite_eq_right guard]

theorem gammaBlockExtractorRuntime_length (b : Nat) (source seeds : List Bool) :
    (gammaBlockExtractorRuntime b source seeds).length = b := by
  by_cases guard : GammaBlockSizeGuard b
  · rw [gammaBlockExtractorRuntime_of_guard b source seeds guard, List.length_take,
      nearHalvingBlockExtractorBits_length, min_eq_left (gammaBlock_output_ge b)]
  · rw [gammaBlockExtractorRuntime_of_not_guard b source seeds guard, List.length_replicate]

theorem gammaBlockExtractorEval_pair (source seeds : List Bool) :
    gammaBlockExtractorEval (pair source seeds) =
      gammaBlockExtractorRuntime (source.length / 8) source seeds := by
  simp only [gammaBlockExtractorEval, pairFst_pair, pairSnd_pair]

theorem gammaBlockExtractorEval_length (z : List Bool) :
    (gammaBlockExtractorEval z).length = (pairFst z).length / 8 :=
  gammaBlockExtractorRuntime_length _ _ _

private theorem gammaBlock_run_valid (b : Nat) (guard : GammaBlockSizeGuard b) :
    nearHalvingBlockEntropy (gammaBlockDepth b) (gammaBlockReserve b) 0 ≤ 8 * b ∧
      2 * (6 * (nearHalvingBlockRate (gammaBlockDepth b) + 1) *
        explicitCondenserBudget (8 * b)
          (nearHalvingBlockEntropy (gammaBlockDepth b) (gammaBlockReserve b) 0)
          (gammaBlockErrorExponent b) + 2 * gammaBlockErrorExponent b) ≤
            gammaBlockReserve b := by
  rw [← gammaBlockInputEntropy_eq]
  have entropy := gammaBlockInputEntropy_le guard
  have budget := gammaBlock_split_budget guard
  exact ⟨by lia, by nlinarith only [budget]⟩

theorem gammaBlockExtractorRuntime_mem_FP {b : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hb : UnaryFn b)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => gammaBlockExtractorRuntime (b z) (source z) (seeds z)) ∈ FP := by
  classical
  let count := fun z => if GammaBlockSizeGuard (b z) then gammaBlockDepth (b z) else 0
  have compiled : (fun z => nearHalvingBlockExtractorBits (8 * b z) (gammaBlockDepth (b z))
      (gammaBlockReserve (b z)) (gammaBlockErrorExponent (b z)) (gammaBlockLeafLength (b z))
      (count z) (source z) (seeds z)) ∈ FP := by
    apply nearHalvingBlockExtractorBits_mem_FP
      ((UnaryFn.const 8).mul hb) (gammaBlockDepth_unaryFn hb)
      (gammaBlockReserve_unaryFn hb) (gammaBlockErrorExponent_unaryFn hb)
      (gammaBlockLeafLength_unaryFn hb)
      (UnaryFn.ite (gammaBlockSizeGuard_fpPred hb) (gammaBlockDepth_unaryFn hb)
        (UnaryFn.const 0)) (gammaBlockDepth_pow_unaryFn hb) hsource hseeds
    · intro z
      split_ifs <;> lia
    · intro z
      by_cases guard : GammaBlockSizeGuard (b z)
      · exact Or.inr (gammaBlock_run_valid (b z) guard)
      · left
        simp only [ite_eq_right guard]
  have selected := (gammaBlockSizeGuard_fpPred hb).ite_mem_FP
    (take_mem_FP compiled hb) (hb.replicate_mem_FP false)
  refine mem_FP_of_eq selected fun z => ?_
  by_cases guard : GammaBlockSizeGuard (b z)
  · rw [ite_eq_left guard, gammaBlockExtractorRuntime_of_guard _ _ _ guard]
    simp only [count, ite_eq_left guard]
  · rw [ite_eq_right guard, gammaBlockExtractorRuntime_of_not_guard _ _ _ guard]

theorem gammaBlockExtractorEval_mem_FP : gammaBlockExtractorEval ∈ FP := by
  unfold gammaBlockExtractorEval
  apply gammaBlockExtractorRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
