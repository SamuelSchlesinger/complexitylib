/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs

/-!
# The recursive extractor with a near-halving entropy schedule

Start with the original Boolean input as a single block, with a trivial
initial seed. Every internal level uses the actual paired condenser at
rate `16*(h+1)`, its scheduled entropy, and its current rounded width.
The final one-shot extractor is shared by all leaves. The complete tuple
retains every fresh field seed and the final independent seed pair once.

This specifies the semantic construction. Its numerical budgets, extraction
guarantee, Boolean seed representation, and evaluator are separate layers.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The fresh field seed at one internal level of the near-halving recursion. -/
abbrev NearHalvingBlockLevelSeed (n h Q E i : Nat) :=
  AdjoinRoot (binaryModulus (sparseFieldExponent (nearHalvingBlockRate h)
    (explicitCondenserBudget (nearHalvingBlockWidth n h Q E i)
      (nearHalvingBlockEntropy h Q i) E)))

/-- The final condenser and hash seeds, shared across every leaf. -/
abbrev NearHalvingBlockFinalSeed (n h Q E : Nat) :=
  let width := nearHalvingBlockWidth n h Q E h
  let ell := nearHalvingBlockLeafLength h Q
  AdjoinRoot (binaryModulus (oneShotCondenserExponent width ell E)) ×
    AdjoinRoot (binaryModulus (oneShotHashExponent width ell E))

/-- All retained seeds, with no random bits spent on the identity initialization. -/
abbrev NearHalvingBlockSeeds (n h Q E : Nat) :=
  RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) h ×
    NearHalvingBlockFinalSeed n h Q E

/-- The actual paired condenser for one near-halving level. -/
noncomputable def nearHalvingBlockStep (n h Q E i : Nat)
    (x : Fin (nearHalvingBlockWidth n h Q E i) → Bool)
    (seed : NearHalvingBlockLevelSeed n h Q E i) :
    (Fin (nearHalvingBlockWidth n h Q E (i + 1)) → Bool) ×
      (Fin (nearHalvingBlockWidth n h Q E (i + 1)) → Bool) :=
  explicitCondenserPair (nearHalvingBlockWidth n h Q E i)
    (nearHalvingBlockEntropy h Q i) E (nearHalvingBlockRate h) x seed

/-- The actual near-halving recursion followed by shared extraction at its leaves. -/
noncomputable def nearHalvingBlockExtractor (n h Q E : Nat) (x : Fin n → Bool)
    (seeds : NearHalvingBlockSeeds n h Q E) :
    Fin (recursiveBlockCount 1 h) → Fin (nearHalvingBlockLeafLength h Q) → ZMod 2 :=
  recursiveBlockExtractor (fun x (_ : Unit) => x) (nearHalvingBlockStep n h Q E) h
    (fun block seed => decodedOneShotExtractor (nearHalvingBlockWidth n h Q E h)
      (nearHalvingBlockLeafLength h Q) E (List.ofFn block) seed) x seeds

end Algebraic.Cutwidth.Extractor
