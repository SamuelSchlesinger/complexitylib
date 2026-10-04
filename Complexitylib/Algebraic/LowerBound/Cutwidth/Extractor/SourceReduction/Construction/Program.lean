/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Program.Internal.Computation
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Program.Internal.Correctness

/-!
# Uniform bounded evaluation of the complete finite source reduction

Two supplied unary counts bound the actual outer and candidate loops.
Each call composes the sampler and selected affine program on the same
original source. The two reductions then compute candidate XOR and strict
majority, producing one bit on every input. The FP certificate includes
parameter generation, binary advice encoding, and both bounded loops.

When the supplied counts equal the semantic counts and the growing sampler
guard holds, the program computes `sourceReductionExtractor` exactly. The
evaluator does not generate unrestricted exponential counts from their
widths; choosing bounded counts for an eventual family is a separate layer.
The construction follows Chattopadhyay--Liao, *Extractors for Sum of Two
Sources*, Lemma 5.4 and the proof of Theorem 2:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The runtime preserves the supplied number of outer rows. -/
theorem sourceReductionRowsRuntime_length (L N C : Nat) (source : List Bool) :
    (sourceReductionRowsRuntime L N C source).length = N :=
  Internal.sourceReductionRowsRuntime_length L N C source

/-- Every parameter choice and source word produces one verdict bit. -/
theorem sourceReductionRuntime_length (L N C : Nat) (source : List Bool) :
    (sourceReductionRuntime L N C source).length = 1 :=
  Internal.sourceReductionRuntime_length L N C source

/-- The majority of no outer rows follows the false tie convention. -/
theorem sourceReductionRuntime_zero_outer (L C : Nat) (source : List Bool) :
    sourceReductionRuntime L 0 C source = [false] :=
  Internal.sourceReductionRuntime_zero_outer L C source

/-- Empty candidate rows all have false XOR, hence the verdict is false. -/
theorem sourceReductionRuntime_zero_candidates (L N : Nat) (source : List Bool) :
    sourceReductionRuntime L N 0 source = [false] :=
  Internal.sourceReductionRuntime_zero_candidates L N source

/-- Exact binary enumeration computes every semantic XOR coordinate in its original order. -/
theorem sourceReductionRowsRuntime_eq (n L : Nat)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool) :
    sourceReductionRowsRuntime L (sourceReductionOuterCount (matchedBlockSeedBits L))
        (sourceReductionCandidateCount (matchedBlockSeedBits L)) (List.ofFn x) =
      List.ofFn (sourceReductionOutput n L x) :=
  Internal.sourceReductionRowsRuntime_eq n L base x

/-- Exact supplied counts and the sampler guard identify the actual finite construction. -/
theorem sourceReductionRuntime_eq (n L N C : Nat)
    (outer : N = sourceReductionOuterCount (matchedBlockSeedBits L))
    (candidates : C = sourceReductionCandidateCount (matchedBlockSeedBits L))
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool) :
    sourceReductionRuntime L N C (List.ofFn x) = [sourceReductionExtractor n L x] :=
  Internal.sourceReductionRuntime_eq n L N C outer candidates base x

open Complexity in
/-- Supplied polynomial-time unary counts make both actual enumeration loops polynomial-time. -/
@[polytime] theorem sourceReductionRuntime_mem_FP {L N C : List Bool → Nat}
    {source : List Bool → List Bool} (hL : UnaryFn L) (hN : UnaryFn N)
    (hC : UnaryFn C) (hsource : source ∈ FP) :
    (fun z => sourceReductionRuntime (L z) (N z) (C z) (source z)) ∈ FP :=
  Internal.sourceReductionRuntime_mem_FP hL hN hC hsource

open Complexity in
/-- Decode the source word and all three supplied unary parameters. -/
theorem sourceReductionEval_pair (source scale outerCount candidateCount : List Bool) :
    sourceReductionEval (pair source (pair scale (pair outerCount candidateCount))) =
      sourceReductionRuntime scale.length outerCount.length candidateCount.length source :=
  Internal.sourceReductionEval_pair source scale outerCount candidateCount

/-- Malformed paired words also produce exactly one bit. -/
theorem sourceReductionEval_length (input : List Bool) :
    (sourceReductionEval input).length = 1 :=
  Internal.sourceReductionEval_length input

open Complexity in
/-- The canonical paired evaluator computes the exact semantic Boolean output. -/
theorem sourceReductionEval_eq (n L N C : Nat)
    (outer : N = sourceReductionOuterCount (matchedBlockSeedBits L))
    (candidates : C = sourceReductionCandidateCount (matchedBlockSeedBits L))
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool) :
    sourceReductionEval (pair (List.ofFn x) (pair (List.replicate L true)
      (pair (List.replicate N true) (List.replicate C true)))) =
      [sourceReductionExtractor n L x] :=
  Internal.sourceReductionEval_eq n L N C outer candidates base x

open Complexity in
/-- One total paired program includes all parameter, call, XOR, and majority computations. -/
@[polytime] theorem sourceReductionEval_mem_FP : sourceReductionEval ∈ FP :=
  Internal.sourceReductionEval_mem_FP

end Algebraic.Cutwidth.Extractor
