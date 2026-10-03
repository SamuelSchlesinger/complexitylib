/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Program.Defs

/-!
# Selecting and executing the first affine phase on strings

The original left-word length, advice length, unary tampering parameter,
and unary target exponent select every scale and local error. The right
word is cut or false-completed to the chosen uniform-source width before
the actual three-stage program runs. Parameter selection is total and does
not test an entropy or source-capacity condition.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Compute all selected parameters, normalize the right word, and run the actual first phase. -/
def affinePhaseOneSelectedRuntime (t target : Nat) (x y advice : List Bool) : List Bool :=
  let n := x.length
  let a := advice.length
  let localError := affinePhaseOneLocalError target
  affinePhaseOneRuntime t (affinePhaseOneInitialScale n t a target) localError
    (affinePhaseOneScale n t a target) (adviceErrorExponent a localError) localError
    x (adviceSelectedRightWord (affinePhaseOneRightBits n t a target) y) advice

/-- Codec: three data words, followed by unary tampering and target words. -/
def affinePhaseOneSelectedEval (z : List Bool) : List Bool :=
  affinePhaseOneSelectedRuntime (pairFst (pairSnd z)).length (pairSnd (pairSnd z)).length
    (pairFst (pairFst z)) (pairFst (pairSnd (pairFst z)))
    (pairSnd (pairSnd (pairFst z)))

end Algebraic.Cutwidth.Extractor
