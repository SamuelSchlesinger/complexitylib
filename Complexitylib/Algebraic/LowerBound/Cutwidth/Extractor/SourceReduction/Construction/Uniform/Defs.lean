/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs
public import Complexitylib.Classes.P.Defs

/-!
# Bounded parameters for one uniform source-reduction family

The scale is the ceiling logarithm of the original input length plus one.
The outer count is then a fixed power of a rounded input length. The Gamma
candidate count is capped by the original input length plus one, ensuring
polynomial-time enumeration on every input. The asymptotic theorem will
show that this cap is eventually inactive.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The scale shared by every component at input length `n`. -/
def sourceReductionFamilyScale (n : Nat) : Nat := Nat.clog 2 (n + 1)

/-- A uniformly bounded candidate count, agreeing eventually with the actual Gamma count. -/
def sourceReductionBoundedCandidates (n : Nat) : Nat :=
  min (sourceReductionCandidateCount (matchedBlockSeedBits (sourceReductionFamilyScale n))) (n + 1)

/-- One total evaluator with all enumeration counts generated from the input length. -/
def sourceReductionFamilyEval (source : List Bool) : List Bool :=
  let L := sourceReductionFamilyScale source.length
  sourceReductionRuntime L (sourceReductionOuterCount (matchedBlockSeedBits L))
    (sourceReductionBoundedCandidates source.length) source

/-- The Boolean family computed by the bounded total evaluator. -/
def sourceReductionFamily (n : Nat) (x : Fin n → Bool) : Bool :=
  (sourceReductionFamilyEval (List.ofFn x)).headD false

/-- Add a fresh XOR bit to balance the actual uniform evaluator. -/
def sourceReductionHardEval : List Bool → List Bool := balancePadEval sourceReductionFamilyEval

/-- The single explicit family used for the coefficient-four circuit lower bound. -/
def sourceReductionHardFamily (n : Nat) (x : Fin n → Bool) : Bool :=
  (sourceReductionHardEval (List.ofFn x)).headD false

/-- The language decided by the single balanced hard-family evaluator. -/
def sourceReductionHardLanguage : Complexity.Language :=
  {source | (sourceReductionHardEval source).headD false = true}

end Algebraic.Cutwidth.Extractor
