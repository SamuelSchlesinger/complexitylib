/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program.Defs
public import Mathlib.Logic.Function.Iterate

/-!
# A total program for repeated actual affine rounds

The row evolves through the actual four-call round. Both original source
words and the three unary round parameters remain in the encoded state
throughout the iteration. All inputs, including malformed words and invalid
parameters, retain the component programs' total behavior.

The program follows the repeated round in Chattopadhyay--Liao, *Extractors
for Sum of Two Sources*, Theorem 6.1, printed pp.23--25:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Repeat the actual round with the same original source words on every call. -/
def affineRoundsRuntime (t L e i : Nat) (x y row : List Bool) : List Bool :=
  (affineRoundRuntime t L e x y)^[i] row

/-- Encode the immutable original sources and unary round parameters. -/
def affineRoundsContextWord (t L e : Nat) (x y : List Bool) : List Bool :=
  pair x (pair y (pair (List.replicate t false)
    (pair (List.replicate L false) (List.replicate e false))))

/-- A total encoded round step: retain the entire context and replace only the row. -/
def affineRoundsStepEval (z : List Bool) : List Bool :=
  let context := pairFst z
  let rest := pairSnd context
  let parameters := pairSnd rest
  pair context (affineRoundRuntime (pairFst parameters).length
    (pairFst (pairSnd parameters)).length (pairSnd (pairSnd parameters)).length
    (pairFst context) (pairFst rest) (pairSnd z))

/-- Codec: `pair (pair context row) rounds`, with unary context parameters and round count. -/
def affineRoundsEval (z : List Bool) : List Bool :=
  let state := pairFst z
  let context := pairFst state
  let rest := pairSnd context
  let parameters := pairSnd rest
  affineRoundsRuntime (pairFst parameters).length (pairFst (pairSnd parameters)).length
    (pairSnd (pairSnd parameters)).length (pairSnd z).length
    (pairFst context) (pairFst rest) (pairSnd state)

end Algebraic.Cutwidth.Extractor
