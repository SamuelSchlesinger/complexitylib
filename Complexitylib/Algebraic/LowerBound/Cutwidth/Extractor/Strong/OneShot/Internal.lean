/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary
import Complexitylib.Tactic.PolyTime

/-!
# Output length and uniform polynomial time for one-shot extraction

The selected hash field covers the requested output length. Unary parameter
generation composes with the existing condenser and hash certificates to
give a single polynomial-time program for all parameters.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem oneShotExtractorBits_length (n ell e : Nat) (source condenserSeed hashSeed : List Bool) :
    (oneShotExtractorBits n ell e source condenserSeed hashSeed).length = ell := by
  unfold oneShotExtractorBits
  rw [binaryHashBits_length (oneShotHashExponent n ell e) _ _ _ _ (by simp)]
  simpa only [List.length_replicate] using
    Nat.min_eq_left (oneShotHashBits_output_capacity n ell e)

theorem oneShotExtractorEval_pair (source condenserSeed hashSeed n ell e : List Bool) :
    oneShotExtractorEval (pair (pair source (pair condenserSeed hashSeed))
      (pair n (pair ell e))) =
      oneShotExtractorBits n.length ell.length e.length source condenserSeed hashSeed := by
  simp only [oneShotExtractorEval, pairFst_pair, pairSnd_pair]

theorem oneShotExtractorEval_length_le (z : List Bool) :
    (oneShotExtractorEval z).length ≤ z.length := by
  rw [oneShotExtractorEval, oneShotExtractorBits_length]
  exact (pairFst_length_le _).trans ((pairSnd_length_le _).trans (pairSnd_length_le z))

theorem oneShotExtractorBits_mem_FP {n ell e : List Bool → Nat}
    {source condenserSeed hashSeed : List Bool → List Bool}
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e)
    (hsource : source ∈ FP) (hcondenser : condenserSeed ∈ FP) (hhash : hashSeed ∈ FP) :
    (fun z => oneShotExtractorBits (n z) (ell z) (e z)
      (source z) (condenserSeed z) (hashSeed z)) ∈ FP := by
  polytime [oneShotExtractorBits]

theorem oneShotExtractorEval_mem_FP : oneShotExtractorEval ∈ FP := by
  unfold oneShotExtractorEval
  apply oneShotExtractorBits_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
