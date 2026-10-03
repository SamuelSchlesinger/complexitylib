/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs

/-!
# The scheduled finite recursive extractor

The initial rate-one condenser compresses the source to one Boolean block.
Each executed level uses the rate-three paired condenser at the prescribed
entropy and the actual current width. A shared one-shot extractor finishes
all leaves. The complete semantic map retains its initial, level, and final
field seeds exactly once. Its uniform bit evaluator is a separate construction.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Exact width of the initial compressed block. -/
def scheduledBlockInitialWidth (n h Q E : Nat) : Nat :=
  explicitCondenserHalfWidth n (recursiveBlockEntropy h Q 0) E 1 +
    explicitCondenserHalfWidth n (recursiveBlockEntropy h Q 0) E 1

/-- Field seed for the initial compression. -/
abbrev ScheduledInitialSeed (n h Q E : Nat) :=
  AdjoinRoot (binaryModulus (sparseFieldExponent 1
    (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E)))

/-- One fresh field seed for an internal level. -/
abbrev ScheduledLevelSeed (n h Q E i : Nat) :=
  AdjoinRoot (binaryModulus (sparseFieldExponent 3 (explicitCondenserBudget
    (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
    (recursiveBlockEntropy h Q i) E)))

/-- The pair of independent field seeds shared by all final leaf extractors. -/
abbrev ScheduledFinalSeed (n h Q E ell : Nat) :=
  let width := recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h
  AdjoinRoot (binaryModulus (oneShotCondenserExponent width ell E)) ×
    AdjoinRoot (binaryModulus (oneShotHashExponent width ell E))

/-- Total number of bits in the initial, internal, and final field seeds. -/
def scheduledBlockSeedBits (n h Q E ell : Nat) : Nat :=
  let initial := scheduledBlockInitialWidth n h Q E
  let width := recursiveBlockWidth initial h Q E h
  sparseFieldBits 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E) +
    (Finset.range h).sum (recursiveBlockSeedWidth initial h Q E) +
    (2 * 3 ^ oneShotCondenserExponent width ell E + 2 * 3 ^ oneShotHashExponent width ell E)

/-- Recombine both initial condenser halves into its full compressed Boolean block. -/
noncomputable def scheduledBlockInitial (n h Q E : Nat) (x : Fin n → Bool)
    (seed : ScheduledInitialSeed n h Q E) : Fin (scheduledBlockInitialWidth n h Q E) → Bool :=
  (Fin.appendEquiv _ _) (explicitCondenserPair n (recursiveBlockEntropy h Q 0) E 1 x seed)

/-- The actual paired condenser used at each internal level. -/
noncomputable def scheduledBlockStep (n h Q E i : Nat)
    (x : Fin (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i) → Bool)
    (seed : ScheduledLevelSeed n h Q E i) :
    (Fin (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E (i + 1)) → Bool) ×
      (Fin (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E (i + 1)) → Bool) :=
  explicitCondenserPair (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
    (recursiveBlockEntropy h Q i) E 3 x seed

/-- The complete finite semantic extractor, with every component and seed type specified. -/
noncomputable def scheduledBlockExtractor (n h Q E ell : Nat) (x : Fin n → Bool)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) : Fin (recursiveBlockCount 1 h) → Fin ell → ZMod 2 :=
  recursiveBlockExtractor (scheduledBlockInitial n h Q E) (scheduledBlockStep n h Q E) h
    (fun block seed => decodedOneShotExtractor
      (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h) ell E
      (List.ofFn block) seed) x seeds

end Algebraic.Cutwidth.Extractor
