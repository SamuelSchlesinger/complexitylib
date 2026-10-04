/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parameters.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Reduction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.BadSeeds.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
import Mathlib.Tactic.Positivity

/-!
# One actual affine breaker for every fourth-order parity test

With `C` candidates per coordinate, every test uses the same selected
affine breaker with `4 * C - 1` tampered slots. Its seed and output widths
therefore do not depend on the tested coordinate subset. The Boolean
component is the first bit of this fixed full-output construction.

This is the fixed-family indexing in Chattopadhyay--Liao, *Extractors for
Sum of Two Sources*, Lemma 5.4, equation (5):
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The common seed width for all coordinate tests with `C` candidates. -/
def affineTestSeedBits (n C a target : Nat) : Nat :=
  affinePhaseOneRightBits n (4 * C - 1) a (affineIterationTarget (4 * C - 1) target)

/-- The common full-output width for the fixed test breaker. -/
def affineTestOutputBits (n C a target : Nat) : Nat :=
  matchedBlockOutputBits (growingMatchedBlockDepth (4 * C - 1))
    (affinePhaseOneScale n (4 * C - 1) a (affineIterationTarget (4 * C - 1) target))

/-- The same actual selected affine breaker is used for every test and candidate. -/
def affineTestBreaker (n C a target : Nat) (x : Fin n → Bool)
    (y : Fin (affineTestSeedBits n C a target) → Bool) (advice : List Bool) :
    Fin (affineTestOutputBits n C a target) → Bool :=
  let t := 4 * C - 1
  let σ := affineIterationTarget t target
  let e := affinePhaseOneLocalError σ
  affineCorrelationBreaker n (affineTestSeedBits n C a target) (growingMatchedBlockDepth t)
    (affinePhaseOneInitialScale n t a σ) e (affinePhaseOneScale n t a σ)
    (adviceErrorExponent a e) e (affineIterationRounds t) x y advice

/-- The canonical first output coordinate of the fixed test breaker. -/
def affineTestFirst (n C a target : Nat) : Fin (affineTestOutputBits n C a target) :=
  ⟨0, by
    unfold affineTestOutputBits matchedBlockOutputBits affinePhaseOneScale affinePhaseOneBase
    positivity⟩

/-- The actual Boolean component used by the XOR source reduction. -/
def affineTestBit (n C a target : Nat) (x : Fin n → Bool)
    (y : Fin (affineTestSeedBits n C a target) → Bool) (advice : List Bool) : Bool :=
  affineTestBreaker n C a target x y advice (affineTestFirst n C a target)

end Algebraic.Cutwidth.Extractor
