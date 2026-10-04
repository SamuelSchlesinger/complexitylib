/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs

/-!
# Total string evaluation of the complete affine construction

The selected evaluator computes the boosted target and all finite chooser
values, normalizes the right word once, and reuses both original words in
the first phase and every subsequent round. The unary tampering and target
parameters are ordinary inputs. The program is total, including malformed
encodings and source lengths that cannot satisfy the statistical reserve.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Execute the actual first phase and all rounds with explicit unary parameters. -/
def affineCorrelationBreakerRuntime (t L₀ e₀ L₁ e₁ er rounds : Nat)
    (x y advice : List Bool) : List Bool :=
  affineRoundsRuntime t L₁ er rounds x y
    (affinePhaseOneRuntime t L₀ e₀ L₁ e₁ er x y advice)

/-- Select all parameters and run the complete construction with the normalized original right word. -/
def affineCorrelationBreakerSelectedRuntime (t target : Nat) (x y advice : List Bool) : List Bool :=
  let n := x.length
  let a := advice.length
  let σ := affineIterationTarget t target
  let e := affinePhaseOneLocalError σ
  affineCorrelationBreakerRuntime t (affinePhaseOneInitialScale n t a σ) e
    (affinePhaseOneScale n t a σ) (adviceErrorExponent a e) e (affineIterationRounds t)
    x (adviceSelectedRightWord (affinePhaseOneRightBits n t a σ) y) advice

/-- Codec: three data words, followed by unary tampering and target words. -/
def affineCorrelationBreakerSelectedEval (z : List Bool) : List Bool :=
  affineCorrelationBreakerSelectedRuntime (pairFst (pairSnd z)).length
    (pairSnd (pairSnd z)).length (pairFst (pairFst z))
    (pairFst (pairSnd (pairFst z))) (pairSnd (pairSnd (pairFst z)))

end Algebraic.Cutwidth.Extractor
