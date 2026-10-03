/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program.Internal

/-!
# Uniform evaluation of an actual affine extraction round

A single total string evaluator performs all four matched calls, rereading
both original source words. Under the component guards its output equals
the actual semantic round at depth `clog 2 (t+1)+64`. The growing arithmetic
budget also pays the old row's short-call guard.

All numerical inputs are unary. Polynomial time is unconditional, including
malformed words and invalid parameters, and the complete encoded output
has a quadratic length bound. No unrestricted unary exponential depth,
statistical independence, or round extraction guarantee is asserted here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The initial prefix word always has the common short width. -/
theorem affineRoundPrefixWord_length (L : Nat) (row : List Bool) :
    (affineRoundPrefixWord L row).length = matchedBlockSeedBits L :=
  Internal.affineRoundPrefixWord_length L row

/-- The total vector prefix and false-completed string prefix agree at every semantic depth. -/
theorem affineRoundPrefix_ofFn (h L : Nat) (row : Fin (matchedBlockOutputBits h L) → Bool) :
    List.ofFn (affineRoundPrefix h L row) = affineRoundPrefixWord L (List.ofFn row) :=
  Internal.affineRoundPrefix_ofFn h L row

/-- A valid growing schedule supplies every short-call guard except its source-length bound. -/
theorem affineRoundRuntime_short_guard (n d t L e : Nat)
    (growing : GrowingMatchedBlockRuntimeValid n t L e) (length : Nat.clog 2 (d + 1) ≤ L) :
    MatchedBlockRuntimeValid d 24 L e :=
  Internal.affineRoundRuntime_short_guard n d t L e growing length

/-- The growing seed budget also makes the complete old row a valid short-extraction source. -/
theorem affineRoundRuntime_row_guard (n t L e : Nat)
    (growing : GrowingMatchedBlockRuntimeValid n t L e) :
    MatchedBlockRuntimeValid (matchedBlockOutputBits (growingMatchedBlockDepth t) L) 24 L e :=
  Internal.affineRoundRuntime_row_guard n t L e growing

/-- Canonical source and row words follow exactly the four actual semantic calls. -/
theorem affineRoundRuntime_eq_affineRoundOutput (n d t L e : Nat)
    (right : MatchedBlockRuntimeValid d 24 L e)
    (rowGuard : MatchedBlockRuntimeValid
      (matchedBlockOutputBits (growingMatchedBlockDepth t) L) 24 L e)
    (last : GrowingMatchedBlockRuntimeValid n t L e)
    (x : Fin n → Bool) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits (growingMatchedBlockDepth t) L) → Bool) :
    affineRoundRuntime t L e (List.ofFn x) (List.ofFn y) (List.ofFn row) =
      List.ofFn (affineRoundOutput n d (growingMatchedBlockDepth t) L e x y row) :=
  Internal.affineRoundRuntime_eq_affineRoundOutput n d t L e right rowGuard last x y row

/-- Each of the three short intermediate words is bounded even on invalid inputs. -/
theorem affineRoundRuntime_short_length_le (L e : Nat) (source seeds : List Bool) :
    (matchedBlockExtractorRuntime 24 L e source seeds).length ≤ matchedBlockSeedBits L :=
  Internal.affineRoundRuntime_short_length_le L e source seeds

/-- The final growing call determines the exact runtime output length. -/
theorem affineRoundRuntime_length (t L e : Nat) (x y row : List Bool) :
    (affineRoundRuntime t L e x y row).length =
      if GrowingMatchedBlockRuntimeValid x.length t L e then
        2 ^ growingMatchedBlockDepth t * L else 0 :=
  Internal.affineRoundRuntime_length t L e x y row

/-- Every runtime output has polynomially bounded length in the unary parameters. -/
theorem affineRoundRuntime_length_le (t L e : Nat) (x y row : List Bool) :
    (affineRoundRuntime t L e x y row).length ≤ 2 ^ 65 * (t + 1) * L :=
  Internal.affineRoundRuntime_length_le t L e x y row

open Complexity in
/-- Generating the false-completed row prefix is uniformly polynomial-time. -/
@[polytime] theorem affineRoundPrefixWord_mem_FP {L : List Bool → Nat} {row : List Bool → List Bool}
    (hL : UnaryFn L) (hrow : row ∈ FP) : (fun z => affineRoundPrefixWord (L z) (row z)) ∈ FP :=
  Internal.affineRoundPrefixWord_mem_FP hL hrow

open Complexity in
/-- All four calls compose into a total uniform polynomial-time runtime. -/
@[polytime] theorem affineRoundRuntime_mem_FP {t L e : List Bool → Nat} {x y row : List Bool → List Bool}
    (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) (hrow : row ∈ FP) :
    (fun z => affineRoundRuntime (t z) (L z) (e z) (x z) (y z) (row z)) ∈ FP :=
  Internal.affineRoundRuntime_mem_FP ht hL he hx hy hrow

open Complexity in
/-- The paired evaluator decodes three data words and three unary parameter words. -/
theorem affineRoundEval_pair (x y row parameter scale error : List Bool) :
    affineRoundEval (pair (pair x (pair y row)) (pair parameter (pair scale error))) =
      affineRoundRuntime parameter.length scale.length error.length x y row :=
  Internal.affineRoundEval_pair x y row parameter scale error

open Complexity in
/-- One total string evaluator computes the complete round on every encoded input. -/
@[polytime] theorem affineRoundEval_mem_FP : affineRoundEval ∈ FP :=
  Internal.affineRoundEval_mem_FP

/-- The complete encoded evaluator has a quadratic output-length bound. -/
theorem affineRoundEval_length_le (z : List Bool) :
    (affineRoundEval z).length ≤ 2 ^ 65 * (z.length + 1) ^ 2 :=
  Internal.affineRoundEval_length_le z

end Algebraic.Cutwidth.Extractor
