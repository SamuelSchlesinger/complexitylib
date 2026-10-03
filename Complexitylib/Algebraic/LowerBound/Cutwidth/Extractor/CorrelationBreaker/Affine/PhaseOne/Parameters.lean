/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Internal

/-!
# Checked finite parameters for the actual first affine phase

The chosen scales and right-source width satisfy every numerical guard
of the initial extraction, advice call, and final growing-depth extraction.
The original left-source entropy pays both threshold charges and the
retained output alphabet. These are unconditional finite arithmetic facts
about the named chooser, not assumptions supplied by its clients.

The actual normalized source must still satisfy the entropy bound; its
capacity in the left width is not asserted for every input size. The
construction follows the first-phase pattern of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1,
<https://arxiv.org/pdf/2110.12652>, with deliberately conservative parameters.
No later independence-merging guarantee or asymptotic capacity is claimed.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The enlarged right source has a controlled logarithm despite its self-contained choice. -/
theorem affinePhaseOneParameters_right_log (n t a target : Nat) :
    Nat.clog 2 (affinePhaseOneRightBits n t a target + 1) ≤
      4 * affinePhaseOneBase n t a target :=
  Internal.affinePhaseOneParameters_right_log n t a target

/-- The final scale has a linear logarithmic bound in the common base. -/
theorem affinePhaseOneParameters_scale_log (n t a target : Nat) :
    Nat.clog 2 (affinePhaseOneScale n t a target + 1) ≤
      2 * affinePhaseOneBase n t a target + 21 :=
  Internal.affinePhaseOneParameters_scale_log n t a target

/-- The initial extractor can read the full original left input at the chosen scale. -/
theorem affinePhaseOneParameters_initial_length (n t a target : Nat) :
    Nat.clog 2 (n + 1) ≤ affinePhaseOneInitialScale n t a target :=
  Internal.affinePhaseOneParameters_initial_length n t a target

/-- The first depth-sixty-four call has the required scale. -/
theorem affinePhaseOneParameters_initial_room (n t a target : Nat) :
    64 ≤ affinePhaseOneInitialScale n t a target :=
  Internal.affinePhaseOneParameters_initial_room n t a target

/-- The initial call has room for its local error exponent. -/
theorem affinePhaseOneParameters_initial_error (n t a target : Nat) :
    affinePhaseOneLocalError target + 64 + 2 ≤ affinePhaseOneInitialScale n t a target :=
  Internal.affinePhaseOneParameters_initial_error n t a target

/-- All finite growing-depth runtime and statistical conditions hold for the final call. -/
theorem affinePhaseOneParameters_growing_guard (n t a target : Nat) :
    GrowingMatchedBlockRuntimeValid n t (affinePhaseOneScale n t a target)
      (affinePhaseOneLocalError target) :=
  Internal.affinePhaseOneParameters_growing_guard n t a target

/-- All source-length and local-error conditions of the actual advice construction hold. -/
theorem affinePhaseOneParameters_advice_guard (n t a target : Nat) :
    FlipFlopSizeGuard (affinePhaseOneRightBits n t a target)
      (matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target))
      (affinePhaseOneScale n t a target) (adviceErrorExponent a (affinePhaseOneLocalError target)) :=
  Internal.affinePhaseOneParameters_advice_guard n t a target

/-- The first extraction output contains the complete advice construction right state. -/
theorem affinePhaseOneParameters_output_size (n t a target : Nat) :
    matchedBlockOutputBits 64 (affinePhaseOneScale n t a target) ≤
      matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target) :=
  Internal.affinePhaseOneParameters_output_size n t a target

/-- The first extraction output pays the advice source entropy reserve. -/
theorem affinePhaseOneParameters_seed_width (n t a target : Nat) :
    2 ^ 150 * (a + 1) * affinePhaseOneScale n t a target ≤
      matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target) :=
  Internal.affinePhaseOneParameters_seed_width n t a target

/-- The uniform right source pays the complete first observation and advice source reserve. -/
theorem affinePhaseOneParameters_source_budget (n t a target : Nat) :
    2 ^ 150 * (a + 1) * affinePhaseOneScale n t a target +
      (t + 1) * (matchedBlockSeedBits (affinePhaseOneInitialScale n t a target) +
        matchedBlockOutputBits 64 (affinePhaseOneInitialScale n t a target)) ≤
      affinePhaseOneRightBits n t a target :=
  Internal.affinePhaseOneParameters_source_budget n t a target

/-- The original right source contains the first extraction seed prefix. -/
theorem affinePhaseOneParameters_prefix_size (n t a target : Nat) :
    matchedBlockSeedBits (affinePhaseOneInitialScale n t a target) ≤
      affinePhaseOneRightBits n t a target :=
  Internal.affinePhaseOneParameters_prefix_size n t a target

/-- The left entropy reserve pays the first threshold and a full local error budget. -/
theorem affinePhaseOneParameters_initial_reserve (n t a target : Nat) :
    2 ^ 142 * affinePhaseOneInitialScale n t a target + affinePhaseOneLocalError target ≤
      affinePhaseOneSourceEntropy n t a target :=
  Internal.affinePhaseOneParameters_initial_reserve n t a target

/-- The left entropy reserve pays the final threshold, retained outputs, and local error. -/
theorem affinePhaseOneParameters_final_reserve (n t a target : Nat) :
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a target
    let L₁ := affinePhaseOneScale n t a target
    2 ^ (2 * h + 14) * L₁ + matchedBlockOutputBits h L₁ +
      (t + 1) * matchedBlockOutputBits 64 L₀ + affinePhaseOneLocalError target ≤
        affinePhaseOneSourceEntropy n t a target :=
  Internal.affinePhaseOneParameters_final_reserve n t a target

/-- The full entropy reserve is bounded by a fixed polynomial in the actual chooser inputs. -/
theorem affinePhaseOneParameters_entropy_le (n t a target : Nat) :
    affinePhaseOneSourceEntropy n t a target ≤
      2 ^ 256 * (t + 1) ^ 2 * (a + 1) * affinePhaseOneBase n t a target ^ 2 :=
  Internal.affinePhaseOneParameters_entropy_le n t a target

end Algebraic.Cutwidth.Extractor
