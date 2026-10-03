/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation.Defs

/-!
# Total selected-parameter advice evaluation

The original left word and advice determine `n` and `a`. The requested
error exponent and output width determine the remaining chooser inputs.
The right word is cut or completed with false bits to the selected length
`m`. Run the existing complete advice program at the selected `L,e`, then
return its first `out` bits. Zero output width returns immediately.

The input codec is
`pair (pair x y) (pair advice (pair targetWord outWord))`.
Only the lengths of the last two words are used. Projections and right-word
normalization are total, including malformed pairings. Canonical right
words already have the selected length and are therefore unchanged.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Normalize a right word to the selected width by a prefix and false completion. -/
def adviceSelectedRightWord (m : Nat) (y : List Bool) : List Bool :=
  (y ++ List.replicate m false).take m

/-- Compute the chosen parameters and execute the actual requested output prefix. -/
def adviceSelectedCorrelationBreakerRuntime (target out : Nat)
    (x y advice : List Bool) : List Bool :=
  if out = 0 then [] else
    let L := adviceScale x.length advice.length target out
    let e := adviceErrorExponent advice.length target
    let m := adviceSourceEntropy x.length advice.length target out
    (adviceCorrelationBreakerRuntime L e x (adviceSelectedRightWord m y) advice).take out

/-- One total evaluator with source/advice words and unary target/output parameters. -/
def adviceSelectedCorrelationBreakerEval (z : List Bool) : List Bool :=
  adviceSelectedCorrelationBreakerRuntime
    (pairFst (pairSnd (pairSnd z))).length
    (pairSnd (pairSnd (pairSnd z))).length
    (pairFst (pairFst z)) (pairSnd (pairFst z)) (pairFst (pairSnd z))

end Algebraic.Cutwidth.Extractor
