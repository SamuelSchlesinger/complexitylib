/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Parameters.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Defs
public import Complexitylib.Mathlib.NatBits

/-!
# Bounded enumeration of the actual sumset-extractor calls

The supplied unary counts bound both enumeration loops. Each position
uses its concrete fixed-width binary code as a sampler index and in its
advice. The actual sampler supplies the seed to the actual selected affine
program on the same original source word. XOR within each outer coordinate
and strict majority produce one final bit, including at zero counts.

The counts are runtime inputs rather than unrestricted powers generated
from their bit widths. Agreement with the finite semantic construction
uses separate exact-count hypotheses. Eventual bounds allowing those
counts to be selected uniformly belong to the parameter-family layer.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- One actual call at the two supplied binary enumeration indices. -/
def sourceReductionCallRuntime (L C : Nat) (source : List Bool) (i z : Nat) : Bool :=
  let b := matchedBlockSeedBits L
  let outer := Nat.toBitsLE (sourceReductionOuterBits b) i
  let candidate := Nat.toBitsLE (sourceReductionCandidateBits b) z
  let advice := outer ++ candidate
  let target := sourceReductionTarget b
  let d := affineTestSeedBits source.length C (sourceReductionAdviceLength b) target
  let seed := amplifiedMatchedSamplerRuntime L d source outer candidate
  (affineCorrelationBreakerSelectedRuntime (4 * C - 1) target source seed advice)[0]?.getD false

/-- The candidate calls at one outer coordinate, in increasing binary-index order. -/
def sourceReductionCandidatesRuntime (L C : Nat) (source : List Bool) (i : Nat) : List Bool :=
  (List.range C).map (sourceReductionCallRuntime L C source i)

/-- XOR each actual candidate row, retaining outer-coordinate order. -/
def sourceReductionRowsRuntime (L N C : Nat) (source : List Bool) : List Bool :=
  (List.range N).map fun i =>
    (sourceReductionCandidatesRuntime L C source i).foldr Bool.xor false

/-- Strict majority of the actual XOR rows, always serialized as one Boolean bit. -/
def sourceReductionRuntime (L N C : Nat) (source : List Bool) : List Bool :=
  majorityEval (sourceReductionRowsRuntime L N C source)

/-- Codec: `pair source (pair scale (pair outerCount candidateCount))`, unary parameters. -/
def sourceReductionEval (input : List Bool) : List Bool :=
  sourceReductionRuntime (pairFst (pairSnd input)).length
    (pairFst (pairSnd (pairSnd input))).length (pairSnd (pairSnd (pairSnd input))).length
    (pairFst input)

end Algebraic.Cutwidth.Extractor
