/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs

/-!
# Explicit finite parameters for the first affine phase

The input width, tampering count, advice length, and target error determine
all three actual extractor calls. Fixed polynomial slack pays the initial
transcript, advice construction, and final growing-depth seed budget. The
right width includes an extra base factor for later accounting, without
asserting any guarantee for the subsequent merging rounds.

These conservative parameters instantiate the first-phase pattern of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1,
<https://arxiv.org/pdf/2110.12652>. They do not claim the paper's sharp
parameters. Feasibility of the selected left entropy in the input width
remains a separate source-capacity condition.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The common logarithmic and advice budget, with fixed arithmetic slack. -/
def affinePhaseOneBase (n t a target : Nat) : Nat :=
  a + target + Nat.clog 2 (n + 1) + Nat.clog 2 (t + 1) + 256

/-- Common scale for the advice call and growing-depth final extraction. -/
def affinePhaseOneScale (n t a target : Nat) : Nat :=
  2 ^ 20 * affinePhaseOneBase n t a target ^ 2

/-- Larger scale for the first depth-sixty-four extraction. -/
def affinePhaseOneInitialScale (n t a target : Nat) : Nat :=
  2 ^ 90 * (a + 1) * affinePhaseOneScale n t a target

/-- Width of the original uniform right source. -/
def affinePhaseOneRightBits (n t a target : Nat) : Nat :=
  2 ^ 160 * (t + 1) * (a + 1) * affinePhaseOneBase n t a target *
    affinePhaseOneScale n t a target

/-- Each of the three calls and two source-mass terms receives this dyadic budget. -/
def affinePhaseOneLocalError (target : Nat) : Nat := target + 3

/-- Left-source entropy paying the initial threshold and final observed-output losses. -/
def affinePhaseOneSourceEntropy (n t a target : Nat) : Nat :=
  let L₀ := affinePhaseOneInitialScale n t a target
  let L₁ := affinePhaseOneScale n t a target
  let h := growingMatchedBlockDepth t
  2 ^ 142 * L₀ + (2 ^ (2 * h + 14) * L₁ + matchedBlockOutputBits h L₁ +
    (t + 1) * matchedBlockOutputBits 64 L₀) + affinePhaseOneLocalError target

end Algebraic.Cutwidth.Extractor
