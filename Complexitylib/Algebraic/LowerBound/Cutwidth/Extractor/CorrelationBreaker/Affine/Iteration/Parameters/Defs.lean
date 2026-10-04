/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs

/-!
# Explicit finite reserves for repeated affine rounds

Use the existing first-phase chooser at a boosted error target. The
original left-source reserve is doubled; the original right width and all
actual extractor scales remain unchanged. The two initial transcript
losses and the subsequent per-round message losses are recorded in bits.

This is a conservative finite schedule for the subset-doubling step of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Theorem 6.1:
<https://arxiv.org/abs/2110.12652>. Definitions do not assert a repeated-round
security theorem or source feasibility in every input width.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Enough doubling rounds to cover every one of the tampered indices. -/
def affineIterationRounds (t : Nat) : Nat := Nat.clog 2 (t + 1)

/-- The first-phase error target also pays the growth of error through all rounds. -/
def affineIterationTarget (t target : Nat) : Nat := target + affineIterationRounds t + 1

/-- Explicit original-left entropy reserve for the first phase and every subsequent round. -/
def affineIterationSourceEntropy (n t a target : Nat) : Nat :=
  2 * affinePhaseOneSourceEntropy n t a (affineIterationTarget t target)

/-- Original-left bits revealed by the complete first-phase transcript. -/
def affineIterationInitialLeftLoss (n t a target : Nat) : Nat :=
  (t + 1) * matchedBlockOutputBits 64
    (affinePhaseOneInitialScale n t a (affineIterationTarget t target))

/-- Original-right bits revealed by both first-phase right messages. -/
def affineIterationInitialRightLoss (n t a target : Nat) : Nat :=
  let σ := affineIterationTarget t target
  let L₀ := affinePhaseOneInitialScale n t a σ
  let L := affinePhaseOneScale n t a σ
  (t + 1) * (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀ + matchedBlockSeedBits L)

/-- Logarithm of the alphabet of one complete honest/tampered short-message family. -/
def affineIterationMessageBits (n t a target : Nat) : Nat :=
  (t + 1) * matchedBlockSeedBits (affinePhaseOneScale n t a (affineIterationTarget t target))

/-- The remaining original-left entropy after the first phase and `i` rounds. -/
def affineIterationLeftEntropy (n t a target i : Nat) : Nat :=
  affineIterationSourceEntropy n t a target -
    (affineIterationInitialLeftLoss n t a target + 2 * i * affineIterationMessageBits n t a target)

/-- The remaining original-right entropy after the first phase and `i` rounds. -/
def affineIterationRightEntropy (n t a target i : Nat) : Nat :=
  affinePhaseOneRightBits n t a (affineIterationTarget t target) -
    (affineIterationInitialRightLoss n t a target + 4 * i * affineIterationMessageBits n t a target)

end Algebraic.Cutwidth.Extractor
