/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RuntimeComposition
public import Complexitylib.Algebraic.MassProduction.LupanovSynthesis

/-!
# Complete finite bound with synthesized resource functions

Use the already-proved coefficient-one Lupanov synthesis for every shorter
Boolean resource function. This discharges resource-circuit existence and
correctness; the remaining finite hypotheses describe only the chosen code,
its source-bit placement, index widths, and the geometric direction budget.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.LupanovRuntime

open Sorting HighRate RuntimePipeline
open scoped LinearAlgebra.Projectivization

/-- Explicit finite cost bound for one shorter Boolean resource function. -/
def resourceCost (suffixWidth : Nat) : Nat :=
  LupanovSynthesis.costBound (LupanovSynthesis.lupanovAddressWidth suffixWidth)
    (LupanovSynthesis.lupanovDataWidth suffixWidth) (LupanovSynthesis.lupanovBlockSize suffixWidth)

/-- Sharp one-copy synthesis supplies an eventual integral resource-cost
bound, uniformly over every Boolean function of the shorter suffix. -/
theorem normalizedResourceBound (precision : Nat) (precisionPositive : 0 < precision) :
    ∃ cutoff, ∀ suffixWidth, cutoff ≤ suffixWidth → ∀ function : ScalarFunction Bool suffixWidth,
      (LupanovSynthesis.lupanovCircuit suffixWidth function).cost DeMorgan.standardCost ≤
        ((precision + 1) * 2 ^ suffixWidth) / (precision * suffixWidth) := by
  obtain ⟨cutoff, sharp⟩ := LupanovSynthesis.lupanovFamily_hasSharpOneCopyCost precision precisionPositive
  refine ⟨max 1 cutoff, ?_⟩
  intro suffixWidth large function
  have suffixPositive : 0 < suffixWidth := by have := (le_max_left 1 cutoff).trans large; omega
  have scaled := sharp suffixWidth ((le_max_right 1 cutoff).trans large) function
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos precisionPositive suffixPositive)).mpr
  calc
    _ = precision * (LupanovSynthesis.lupanovCircuit suffixWidth function).cost DeMorgan.standardCost * suffixWidth := by ring
    _ ≤ _ := scaled

/-- Any uniform bound on the actual Lupanov resource circuits can replace
the explicit finite envelope in the complete runtime construction. -/
theorem booleanMassComplexity_le_of_resourceBound
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Fin (2 ^ prefixWidth) ↪ InformationBit code copies)
    (function : Fin (2 ^ prefixWidth) → (Fin suffixWidth → Bool) → Bool)
    (copyFits : copies ≤ 2 ^ copyBits) (selectorFits : width ≤ 2 ^ selectorBits)
    (bounded : ∀ resourceFunction : ScalarFunction Bool suffixWidth,
      (LupanovSynthesis.lupanovCircuit suffixWidth resourceFunction).cost DeMorgan.standardCost ≤ bound) :
    booleanMassComplexity (requestFunction function) (networkRecords depth) ≤
      (RuntimeComposition.overhead depth copies prefixWidth dimension width suffixWidth copyBits selectorBits +
        ResourceLayout.count copies dimension width * bound : Nat) := by
  exact RuntimeComposition.booleanMassComplexity_le positive dimensionPositive budget code placement function
    copyFits selectorFits
    (fun resource => LupanovSynthesis.lupanovCircuit suffixWidth
      (ResourceLayout.function positive code placement function resource))
    (fun resource suffix => LupanovSynthesis.lupanovCircuit_eval suffixWidth
      (ResourceLayout.function positive code placement function resource) suffix)
    (fun resource => bounded (ResourceLayout.function positive code placement function resource))

/-- Concrete high-rate mass-production bound with every resource function
synthesized, rather than supplied as an additional circuit premise. -/
theorem booleanMassComplexity_le
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Fin (2 ^ prefixWidth) ↪ InformationBit code copies)
    (function : Fin (2 ^ prefixWidth) → (Fin suffixWidth → Bool) → Bool)
    (copyFits : copies ≤ 2 ^ copyBits) (selectorFits : width ≤ 2 ^ selectorBits) :
    booleanMassComplexity (requestFunction function) (networkRecords depth) ≤
      (RuntimeComposition.overhead depth copies prefixWidth dimension width suffixWidth copyBits selectorBits +
        ResourceLayout.count copies dimension width * resourceCost suffixWidth : Nat) := by
  exact RuntimeComposition.booleanMassComplexity_le positive dimensionPositive budget code placement function
    copyFits selectorFits
    (fun resource => LupanovSynthesis.lupanovCircuit suffixWidth
      (ResourceLayout.function positive code placement function resource))
    (fun resource suffix => LupanovSynthesis.lupanovCircuit_eval suffixWidth
      (ResourceLayout.function positive code placement function resource) suffix)
    (fun resource => LupanovSynthesis.lupanovCircuit_cost_le suffixWidth
      (ResourceLayout.function positive code placement function resource))

end Algebraic.MassProduction.Nonuniform.LupanovRuntime
