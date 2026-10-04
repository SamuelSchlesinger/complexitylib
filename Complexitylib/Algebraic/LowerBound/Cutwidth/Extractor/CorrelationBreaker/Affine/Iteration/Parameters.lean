/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Reserves
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Round
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Mass
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Error
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Polynomial

/-!
# Concrete global reserves for repeated affine rounds

The unchanged first-phase chooser, at target `target + clog₂(t+1) + 1`,
pays every round after doubling its original-left entropy reserve. The
theorems account for the full initial transcript and two left/four right
short-message families per round. All four worst-case subset reserves
hold without additional numerical hypotheses.

These are finite parameter deductions for the subset-doubling construction
of Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Theorem
6.1, <https://arxiv.org/abs/2110.12652>. They do not assert source capacity
for every input width or replace the actual statistical iteration proof.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The number of rounds is no larger than the number of tampered copies. -/
theorem affineIterationRounds_le (t : Nat) : affineIterationRounds t ≤ t :=
  Internal.affineIterationRounds_le t

/-- The doubled subset capacity covers every tampered index, including the zero-copy case. -/
theorem affineIterationRounds_cover (t : Nat) : t + 1 ≤ 2 ^ affineIterationRounds t :=
  Internal.affineIterationRounds_cover t

/-- A single original-left budget includes the complete initial and repeated observations. -/
theorem affineIterationParameters_left_budget (n t a target : Nat) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    let h := growingMatchedBlockDepth t
    affineIterationInitialLeftLoss n t a target +
      2 * affineIterationRounds t * affineIterationMessageBits n t a target +
      2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L + affinePhaseOneLocalError σ ≤
        affineIterationSourceEntropy n t a target :=
  Internal.affineIterationParameters_left_budget n t a target

/-- The existing right-source width pays the complete initial and repeated observations. -/
theorem affineIterationParameters_right_budget (n t a target : Nat) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    affineIterationInitialRightLoss n t a target +
      4 * affineIterationRounds t * affineIterationMessageBits n t a target +
      2 ^ 62 * L + affinePhaseOneLocalError σ ≤ affinePhaseOneRightBits n t a σ :=
  Internal.affineIterationParameters_right_budget n t a target

/-- Cumulative left transcript losses never exhaust the original source reserve. -/
theorem affineIterationParameters_left_capacity (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    affineIterationInitialLeftLoss n t a target +
      2 * i * affineIterationMessageBits n t a target ≤
        affineIterationSourceEntropy n t a target :=
  Internal.affineIterationParameters_left_capacity n t a target index

/-- Cumulative right transcript losses never exceed the original uniform width. -/
theorem affineIterationParameters_right_capacity (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    affineIterationInitialRightLoss n t a target +
      4 * i * affineIterationMessageBits n t a target ≤
        affinePhaseOneRightBits n t a (affineIterationTarget t target) :=
  Internal.affineIterationParameters_right_capacity n t a target index

/-- The first short extraction has enough remaining original-right entropy in every round. -/
theorem affineIterationParameters_first_reserve (n t a target : Nat) {i : Nat}
    (index : i < affineIterationRounds t) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
      affineIterationRightEntropy n t a target i :=
  Internal.affineIterationParameters_first_reserve n t a target index

/-- The actual long row pays the middle extraction and every selected short output. -/
theorem affineIterationParameters_merge_reserve (n t a target : Nat) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
      matchedBlockOutputBits (growingMatchedBlockDepth t) L :=
  Internal.affineIterationParameters_merge_reserve n t a target

/-- The recovery call pays all three right-message families and the selected outputs. -/
theorem affineIterationParameters_recover_reserve (n t a target : Nat) {i : Nat}
    (index : i < affineIterationRounds t) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    2 ^ 62 * L + (t + 3 * (t + 1)) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
      affineIterationRightEntropy n t a target i :=
  Internal.affineIterationParameters_recover_reserve n t a target index

/-- The final extraction pays the current selected long outputs and both left observations. -/
theorem affineIterationParameters_final_reserve (n t a target : Nat) {i : Nat}
    (index : i < affineIterationRounds t) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    let h := growingMatchedBlockDepth t
    2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
        affineIterationLeftEntropy n t a target i :=
  Internal.affineIterationParameters_final_reserve n t a target index

/-- Exact dyadic mass after the initial left transcript and two message families per round. -/
theorem affineIterationParameters_left_mass (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    ((2 : ℝ) ^ affineIterationMessageBits n t a target) ^ (2 * i) *
      ((2 : ℝ) ^ affineIterationInitialLeftLoss n t a target *
        ((2 : ℝ) ^ affineIterationSourceEntropy n t a target)⁻¹) =
      ((2 : ℝ) ^ affineIterationLeftEntropy n t a target i)⁻¹ :=
  Internal.affineIterationParameters_left_mass n t a target index

/-- Exact dyadic mass after the initial right transcript and four message families per round. -/
theorem affineIterationParameters_right_mass (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    ((2 : ℝ) ^ affineIterationMessageBits n t a target) ^ (4 * i) *
      ((2 : ℝ) ^ affineIterationInitialRightLoss n t a target *
        ((2 : ℝ) ^ affinePhaseOneRightBits n t a (affineIterationTarget t target))⁻¹) =
      ((2 : ℝ) ^ affineIterationRightEntropy n t a target i)⁻¹ :=
  Internal.affineIterationParameters_right_mass n t a target index

/-- The complete `ρ ↦ 2ρ + 8 * 2⁻ᵉ` recurrence fits the requested final error. -/
theorem affineIterationParameters_error_budget (t target : Nat) :
    let R := affineIterationRounds t
    let σ := affineIterationTarget t target
    (2 : ℝ) ^ R * ((2 : ℝ) ^ σ)⁻¹ +
      8 * ((2 : ℝ) ^ R - 1) * ((2 : ℝ) ^ affinePhaseOneLocalError σ)⁻¹ ≤
        ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affineIterationParameters_error_budget t target

/-- The doubled source reserve also satisfies the original first-phase entropy hypothesis. -/
theorem affineIterationParameters_phase_one_reserve (n t a target : Nat) :
    affinePhaseOneSourceEntropy n t a (affineIterationTarget t target) ≤
      affineIterationSourceEntropy n t a target :=
  Internal.affineIterationParameters_phase_one_reserve n t a target

/-- The full original-left entropy reserve remains a fixed polynomial in the chooser base. -/
theorem affineIterationParameters_entropy_le (n t a target : Nat) :
    affineIterationSourceEntropy n t a target ≤
      2 ^ 257 * (t + 1) ^ 2 * (a + 1) *
        affinePhaseOneBase n t a (affineIterationTarget t target) ^ 2 :=
  Internal.affineIterationParameters_entropy_le n t a target

end Algebraic.Cutwidth.Extractor
