/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs

/-!
# The complete actual affine correlation-breaker construction

Run the first affine phase, then repeatedly execute the four-call merging
round with the same original source words. The selected construction uses
enough rounds to cover all tamperings, and boosts the first-phase target to
pay the accumulated error. These are deterministic programs; their source
and advice hypotheses belong to the extraction theorems.

The construction follows Chattopadhyay--Liao, *Extractors for Sum of Two
Sources*, Theorem 6.1, printed pp.23--25:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The first affine phase followed by actual rounds on the unchanged original sources. -/
def affineCorrelationBreaker (n d h L₀ e₀ L₁ e₁ er rounds : Nat)
    (x : Fin n → Bool) (y : Fin d → Bool) (advice : List Bool) :
    Fin (matchedBlockOutputBits h L₁) → Bool :=
  affineRoundsOutput n d h L₁ er rounds x y
    (affinePhaseOneOutput n d h L₀ e₀ L₁ e₁ er x y advice)

/-- Select every scale, local error, and round count from the original input dimensions. -/
def affineCorrelationBreakerSelected (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool)
    (y : Fin (affinePhaseOneRightBits n t advice.length (affineIterationTarget t target)) → Bool) :
    Fin (matchedBlockOutputBits (growingMatchedBlockDepth t)
      (affinePhaseOneScale n t advice.length (affineIterationTarget t target))) → Bool :=
  let σ := affineIterationTarget t target
  let e := affinePhaseOneLocalError σ
  affineCorrelationBreaker n (affinePhaseOneRightBits n t advice.length σ)
    (growingMatchedBlockDepth t) (affinePhaseOneInitialScale n t advice.length σ) e
    (affinePhaseOneScale n t advice.length σ) (adviceErrorExponent advice.length e) e
    (affineIterationRounds t) x y advice

end Algebraic.Cutwidth.Extractor
