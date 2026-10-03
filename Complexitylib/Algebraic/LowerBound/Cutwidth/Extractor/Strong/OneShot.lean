/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Correctness
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Internal

/-!
# Uniform polynomial-time condense-then-hash extraction

The total program emits exactly `ell` bits for every input and every pair of
seed words. Its parameter generation and runtime belong to FP uniformly in
unary `n`, `ell`, and `e`. Correctness identifies the program with the linear
statistical map; `OneShot.Extraction` supplies the retained-seed error bound
on fixed-length flat sources.

This is one round of condensation and hashing. Its finite seed bound depends
on the output length as well as source length and error; it does not yet
provide the recursive seed reuse needed for the final hard family.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- The selected field always produces exactly the requested number of output bits. -/
theorem oneShotExtractorBits_length (n ell e : Nat) (source condenserSeed hashSeed : List Bool) :
    (oneShotExtractorBits n ell e source condenserSeed hashSeed).length = ell :=
  Internal.oneShotExtractorBits_length n ell e source condenserSeed hashSeed

/-- The paired evaluator reads source, seeds, and three unary parameters. -/
theorem oneShotExtractorEval_pair (source condenserSeed hashSeed n ell e : List Bool) :
    oneShotExtractorEval (pair (pair source (pair condenserSeed hashSeed))
      (pair n (pair ell e))) =
      oneShotExtractorBits n.length ell.length e.length source condenserSeed hashSeed :=
  Internal.oneShotExtractorEval_pair source condenserSeed hashSeed n ell e

/-- Every paired input, including malformed encodings, bounds its output length. -/
theorem oneShotExtractorEval_length_le (z : List Bool) :
    (oneShotExtractorEval z).length ≤ z.length :=
  Internal.oneShotExtractorEval_length_le z

/-- Condensation and hashing are uniformly polynomial-time with unary parameters. -/
@[polytime] theorem oneShotExtractorBits_mem_FP {n ell e : List Bool → Nat}
    {source condenserSeed hashSeed : List Bool → List Bool}
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e)
    (hsource : source ∈ FP) (hcondenser : condenserSeed ∈ FP) (hhash : hashSeed ∈ FP) :
    (fun z => oneShotExtractorBits (n z) (ell z) (e z)
      (source z) (condenserSeed z) (hashSeed z)) ∈ FP :=
  Internal.oneShotExtractorBits_mem_FP hn hell he hsource hcondenser hhash

/-- A single polynomial-time evaluator computes the extractor at all unary parameters. -/
@[polytime] theorem oneShotExtractorEval_mem_FP : oneShotExtractorEval ∈ FP :=
  Internal.oneShotExtractorEval_mem_FP

end Algebraic.Cutwidth.Extractor
