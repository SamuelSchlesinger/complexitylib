/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Unary
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority
import Complexitylib.Classes.P.Iterate
import Complexitylib.Classes.P.Range
import Complexitylib.Tactic.PolyTime

/-!
# Uniform computation with two bounded enumeration loops

Both loop counts are supplied as polynomial-time unary numbers. Every
call uses the actual sampler and selected affine algorithms. XOR is a
one-bit-state fold; the outer list then feeds the checked majority program.
No source distribution, extractor guard, or exponential count-generation
claim enters these computation theorems.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

private theorem xorWord_mem_FP :
    (fun bits : List Bool => [bits.foldr Bool.xor false]) ∈ FP := by
  refine recFold_mem_FP_of_bound
    (g := fun _ bits => [bits.foldr Bool.xor false])
    (w := fun _ => []) (s := id) (E := fun _ => [false])
    (A := fun z => pairSnd (pairFst z))
    (B := fun z => notBit (pairSnd (pairFst z)))
    (by polytime) (by polytime) (by polytime) (by polytime) id_mem_FP
    (by intro z; rfl) ?_ ?_ (PolyBound.const 1) ?_
  · intro z bits
    simp only [List.foldr_cons, Bool.false_xor, pairFst_pair, pairSnd_pair]
  · intro z bits
    simp only [List.foldr_cons, Bool.true_xor, pairFst_pair, pairSnd_pair]
    cases bits.foldr Bool.xor false <;> rfl
  · intro z bits _
    simp

theorem sourceReductionCallRuntime_mem_FP {L C i j : List Bool → Nat}
    {source : List Bool → List Bool} (hL : UnaryFn L) (hC : UnaryFn C)
    (hi : UnaryFn i) (hj : UnaryFn j) (hsource : source ∈ FP) :
    (fun z => [sourceReductionCallRuntime (L z) (C z) (source z) (i z) (j z)]) ∈ FP := by
  polytime [sourceReductionCallRuntime, affineTestSeedBits, affineIterationTarget,
    affineIterationRounds, sourceReductionAdviceLength, sourceReductionTarget,
    sourceReductionOuterBits, sourceReductionCandidateBits, matchedBlockSeedBits]

theorem sourceReductionCandidatesRuntime_mem_FP {L C i : List Bool → Nat}
    {source : List Bool → List Bool} (hL : UnaryFn L) (hC : UnaryFn C)
    (hi : UnaryFn i) (hsource : source ∈ FP) :
    (fun z => sourceReductionCandidatesRuntime (L z) (C z) (source z) (i z)) ∈ FP := by
  have call : (fun z => [sourceReductionCallRuntime (L (pairFst z)) (C (pairFst z))
      (source (pairFst z)) (i (pairFst z)) (pairSnd z).length]) ∈ FP := by
    apply sourceReductionCallRuntime_mem_FP <;> polytime
  exact bitwise_mem_FP hC.mem_FP call (by
    intro z j
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate])

theorem sourceReductionRowsRuntime_mem_FP {L N C : List Bool → Nat}
    {source : List Bool → List Bool} (hL : UnaryFn L) (hN : UnaryFn N)
    (hC : UnaryFn C) (hsource : source ∈ FP) :
    (fun z => sourceReductionRowsRuntime (L z) (N z) (C z) (source z)) ∈ FP := by
  have candidates : (fun z => sourceReductionCandidatesRuntime (L (pairFst z))
      (C (pairFst z)) (source (pairFst z)) (pairSnd z).length) ∈ FP := by
    apply sourceReductionCandidatesRuntime_mem_FP <;> polytime
  have row := mem_FP_comp candidates xorWord_mem_FP
  exact bitwise_mem_FP hN.mem_FP row (by
    intro z i
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate])

theorem sourceReductionRuntime_mem_FP {L N C : List Bool → Nat}
    {source : List Bool → List Bool} (hL : UnaryFn L) (hN : UnaryFn N)
    (hC : UnaryFn C) (hsource : source ∈ FP) :
    (fun z => sourceReductionRuntime (L z) (N z) (C z) (source z)) ∈ FP :=
  mem_FP_comp (sourceReductionRowsRuntime_mem_FP hL hN hC hsource) majorityEval_mem_FP

theorem sourceReductionRuntime_length (L N C : Nat) (source : List Bool) :
    (sourceReductionRuntime L N C source).length = 1 := rfl

theorem sourceReductionRuntime_zero_outer (L C : Nat) (source : List Bool) :
    sourceReductionRuntime L 0 C source = [false] := by
  simp [sourceReductionRuntime, sourceReductionRowsRuntime, majorityEval,
    Complexity.majority, Complexity.popCount]
  ext i
  exact i.elim0

theorem sourceReductionRuntime_zero_candidates (L N : Nat) (source : List Bool) :
    sourceReductionRuntime L N 0 source = [false] := by
  simp [sourceReductionRuntime, sourceReductionRowsRuntime, sourceReductionCandidatesRuntime,
    majorityEval, Complexity.majority, Complexity.popCount]

theorem sourceReductionRowsRuntime_length (L N C : Nat) (source : List Bool) :
    (sourceReductionRowsRuntime L N C source).length = N := by
  simp only [sourceReductionRowsRuntime, List.length_map, List.length_range]

theorem sourceReductionCandidatesRuntime_length (L C : Nat) (source : List Bool) (i : Nat) :
    (sourceReductionCandidatesRuntime L C source i).length = C := by
  simp only [sourceReductionCandidatesRuntime, List.length_map, List.length_range]

theorem sourceReductionEval_pair (source scale outerCount candidateCount : List Bool) :
    sourceReductionEval (pair source (pair scale (pair outerCount candidateCount))) =
      sourceReductionRuntime scale.length outerCount.length candidateCount.length source := by
  simp only [sourceReductionEval, pairFst_pair, pairSnd_pair]

theorem sourceReductionEval_mem_FP : sourceReductionEval ∈ FP := by
  unfold sourceReductionEval
  apply sourceReductionRuntime_mem_FP <;> polytime

theorem sourceReductionEval_length (input : List Bool) :
    (sourceReductionEval input).length = 1 := rfl

end Algebraic.Cutwidth.Extractor.Internal
