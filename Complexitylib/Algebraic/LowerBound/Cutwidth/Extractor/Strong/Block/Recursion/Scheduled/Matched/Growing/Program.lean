/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Internal

/-!
# One uniform evaluator for growing-depth matched extraction

The unary input `t` selects depth `clog 2 (t+1) + 64`. Its leaf count is
at most `2^65 * (t+1)`, allowing polynomial-time parameter generation and
bounded numerical and payload iteration. This certificate concerns that
logarithmic depth selection; it does not permit an arbitrary unary depth
with exponentially many output blocks.

The actual paired string evaluator is total on every input. Under the
explicit growing-depth guard it equals the existing matched Boolean
extractor, with the complete padded seed accepted and any extra suffix
ignored. Invalid parameters return an empty word. The statistical guarantee
is supplied by `Scheduled.Matched.Growing`; this layer supplies its uniform
runtime without changing the earlier fixed-depth evaluator.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The number of leaves is linear in the unary depth-selection parameter. -/
theorem growingMatchedBlockDepth_pow_le (t : Nat) :
    2 ^ growingMatchedBlockDepth t ≤ 2 ^ 65 * (t + 1) :=
  Internal.growingMatchedBlockDepth_pow_le t

/-- The initial entropy's depth factor is quadratic in the unary parameter. -/
theorem growingMatchedBlockDepth_pow_four_le (t : Nat) :
    4 ^ growingMatchedBlockDepth t ≤ (2 ^ 65 * (t + 1)) ^ 2 :=
  Internal.growingMatchedBlockDepth_pow_four_le t

open Complexity in
/-- The logarithmic recursion depth is uniformly computable in unary. -/
@[polytime] theorem growingMatchedBlockDepth_unaryFn {t : List Bool → Nat} (ht : UnaryFn t) :
    UnaryFn fun z => growingMatchedBlockDepth (t z) :=
  Internal.growingMatchedBlockDepth_unaryFn ht

open Complexity in
/-- Generating the leaf count is polynomial-time on all inputs, including `t = 0`. -/
@[polytime] theorem growingMatchedBlockDepth_pow_unaryFn {t : List Bool → Nat} (ht : UnaryFn t) :
    UnaryFn fun z => 2 ^ growingMatchedBlockDepth (t z) :=
  Internal.growingMatchedBlockDepth_pow_unaryFn ht

/-- Valid parameters run the scheduled bit program after taking its exact seed prefix. -/
theorem growingMatchedBlockExtractorRuntime_of_valid (t L e : Nat) (source seeds : List Bool)
    (valid : GrowingMatchedBlockRuntimeValid source.length t L e) :
    growingMatchedBlockExtractorRuntime t L e source seeds =
      let h := growingMatchedBlockDepth t
      scheduledBlockExtractorBits source.length h (recursiveBlockReserve L (e + h + 2))
        (e + h + 2) L source (seeds.take (scheduledBlockSeedBits source.length h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)) :=
  Internal.growingMatchedBlockExtractorRuntime_of_valid t L e source seeds valid

/-- Invalid parameters return the empty word. -/
theorem growingMatchedBlockExtractorRuntime_of_not_valid (t L e : Nat) (source seeds : List Bool)
    (invalid : ¬ GrowingMatchedBlockRuntimeValid source.length t L e) :
    growingMatchedBlockExtractorRuntime t L e source seeds = [] :=
  Internal.growingMatchedBlockExtractorRuntime_of_not_valid t L e source seeds invalid

/-- The exact output width is one scale-sized word per leaf whenever the guard holds. -/
theorem growingMatchedBlockExtractorRuntime_length (t L e : Nat) (source seeds : List Bool) :
    (growingMatchedBlockExtractorRuntime t L e source seeds).length =
      if GrowingMatchedBlockRuntimeValid source.length t L e then
        2 ^ growingMatchedBlockDepth t * L else 0 :=
  Internal.growingMatchedBlockExtractorRuntime_length t L e source seeds

/-- Every runtime output has polynomially bounded length, including malformed inputs. -/
theorem growingMatchedBlockExtractorRuntime_length_le (t L e : Nat) (source seeds : List Bool) :
    (growingMatchedBlockExtractorRuntime t L e source seeds).length ≤ 2 ^ 65 * (t + 1) * L :=
  Internal.growingMatchedBlockExtractorRuntime_length_le t L e source seeds

open Complexity in
/-- The full finite validity condition is polynomial-time on unary numerical inputs. -/
@[polytime] theorem growingMatchedBlockRuntimeValid_fpPred {n t L e : List Bool → Nat}
    (hn : UnaryFn n) (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e) :
    FPPred fun z => GrowingMatchedBlockRuntimeValid (n z) (t z) (L z) (e z) :=
  Internal.growingMatchedBlockRuntimeValid_fpPred hn ht hL he

open Complexity in
/-- The total runtime includes all parameter, exact seed-width, and payload computations. -/
@[polytime] theorem growingMatchedBlockExtractorRuntime_mem_FP {t L e : List Bool → Nat}
    {source seeds : List Bool → List Bool} (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => growingMatchedBlockExtractorRuntime (t z) (L z) (e z) (source z) (seeds z)) ∈ FP :=
  Internal.growingMatchedBlockExtractorRuntime_mem_FP ht hL he hsource hseeds

open Complexity in
/-- The paired interface reads two words and three unary numbers. -/
theorem growingMatchedBlockExtractorEval_pair (source seeds parameter scale error : List Bool) :
    growingMatchedBlockExtractorEval
      (pair (pair source seeds) (pair parameter (pair scale error))) =
      growingMatchedBlockExtractorRuntime parameter.length scale.length error.length source seeds :=
  Internal.growingMatchedBlockExtractorEval_pair source seeds parameter scale error

open Complexity in
/-- One paired evaluator is polynomial-time on every string. -/
@[polytime] theorem growingMatchedBlockExtractorEval_mem_FP : growingMatchedBlockExtractorEval ∈ FP :=
  Internal.growingMatchedBlockExtractorEval_mem_FP

/-- The complete encoded evaluator's output length is quadratic in its encoded input length. -/
theorem growingMatchedBlockExtractorEval_length_le (z : List Bool) :
    (growingMatchedBlockExtractorEval z).length ≤ 2 ^ 65 * (z.length + 1) ^ 2 :=
  Internal.growingMatchedBlockExtractorEval_length_le z

/-- Canonical Boolean inputs evaluate to exactly the actual growing-depth matched map. -/
theorem growingMatchedBlockExtractorRuntime_eq_matchedBlockExtractor (n t L e : Nat)
    (valid : GrowingMatchedBlockRuntimeValid n t L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    growingMatchedBlockExtractorRuntime t L e (List.ofFn x) (List.ofFn seed) =
      List.ofFn (matchedBlockExtractor n (growingMatchedBlockDepth t) L e x seed) :=
  Internal.growingMatchedBlockExtractorRuntime_eq_matchedBlockExtractor n t L e valid x seed

/-- The full padded seed has the same meaning even when an arbitrary suffix is appended. -/
theorem growingMatchedBlockExtractorRuntime_append_eq_matchedBlockExtractor (n t L e : Nat)
    (valid : GrowingMatchedBlockRuntimeValid n t L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) (tail : List Bool) :
    growingMatchedBlockExtractorRuntime t L e (List.ofFn x) (List.ofFn seed ++ tail) =
      List.ofFn (matchedBlockExtractor n (growingMatchedBlockDepth t) L e x seed) :=
  Internal.growingMatchedBlockExtractorRuntime_append_eq_matchedBlockExtractor n t L e
    valid x seed tail

end Algebraic.Cutwidth.Extractor
