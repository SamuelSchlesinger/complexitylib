/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Asymptotics.Defs

/-!
# One string program for each polylogarithmic-output extractor family

Fix the output exponent parameter and error exponent. The program reads a
paired source and seed word, computes its requested logarithmic depth, and
uses the total scheduled evaluator. Clipping affects only lengths where
the raw requested depth exceeds the finite logarithmic budget; the checked
asymptotic depth estimate shows that it is eventually inactive.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Uniform bit program for the fixed family, on `pair source seedWord`. -/
def polylogBlockExtractorProgram (a e : Nat) (z : List Bool) : List Bool :=
  scheduledBlockExtractorRuntime (polylogBlockDepth a (pairFst z).length) e
    (pairFst z) (pairSnd z)

end Algebraic.Cutwidth.Extractor
