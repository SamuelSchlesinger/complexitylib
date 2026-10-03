/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs

/-!
# A fixed family of recursive extractors with polylogarithmic output

For fixed natural parameters `a,e`, the leaf length is `L=clog 2 (n+1)`
and the depth is exactly `a*clog 2 (L+1)`. The local error exponent is
`e+h+2`, and the reserve is the existing explicit finite reserve. These
definitions instantiate the specified recursive map and its actual seeds.
The depth is not truncated at small input lengths.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The number of output bits extracted from each leaf. -/
def polylogBlockLength (n : Nat) : Nat := Nat.clog 2 (n + 1)

/-- The raw recursion depth, with fixed multiplier `a`. -/
def polylogBlockDepth (a n : Nat) : Nat := a * Nat.clog 2 (polylogBlockLength n + 1)

/-- The local exponent paying for total error `2^(-e)` at the chosen depth. -/
def polylogBlockErrorExponent (a e n : Nat) : Nat := e + polylogBlockDepth a n + 2

/-- The explicit reserve used at every leaf of the family. -/
def polylogBlockReserve (a e n : Nat) : Nat :=
  recursiveBlockReserve (polylogBlockLength n) (polylogBlockErrorExponent a e n)

/-- The actual initial entropy in bits; the source cap is `2` raised to this number. -/
def polylogBlockEntropy (a e n : Nat) : Nat :=
  recursiveBlockEntropy (polylogBlockDepth a n) (polylogBlockReserve a e n) 0

/-- The exact total number of bits in all retained seeds. -/
def polylogBlockSeedBits (a e n : Nat) : Nat :=
  scheduledBlockSeedBits n (polylogBlockDepth a n) (polylogBlockReserve a e n)
    (polylogBlockErrorExponent a e n) (polylogBlockLength n)

/-- The actual number of Boolean output coordinates across all leaves. -/
def polylogBlockOutputBits (a n : Nat) : Nat :=
  recursiveBlockCount 1 (polylogBlockDepth a n) * polylogBlockLength n

/-- All field seeds retained by the specified member of the family. -/
abbrev PolylogBlockSeeds (a e n : Nat) :=
  RecursiveSeeds
    (ScheduledInitialSeed n (polylogBlockDepth a n) (polylogBlockReserve a e n)
      (polylogBlockErrorExponent a e n))
    (ScheduledLevelSeed n (polylogBlockDepth a n) (polylogBlockReserve a e n)
      (polylogBlockErrorExponent a e n)) (polylogBlockDepth a n) ×
    ScheduledFinalSeed n (polylogBlockDepth a n) (polylogBlockReserve a e n)
      (polylogBlockErrorExponent a e n) (polylogBlockLength n)

/-- The specified recursive extractor at length `n`, for fixed family parameters `a,e`. -/
noncomputable def polylogBlockExtractor (a e n : Nat) (x : Fin n → Bool)
    (seeds : PolylogBlockSeeds a e n) :
    Fin (recursiveBlockCount 1 (polylogBlockDepth a n)) → Fin (polylogBlockLength n) → ZMod 2 :=
  scheduledBlockExtractor n (polylogBlockDepth a n) (polylogBlockReserve a e n)
    (polylogBlockErrorExponent a e n) (polylogBlockLength n) x seeds

end Algebraic.Cutwidth.Extractor
