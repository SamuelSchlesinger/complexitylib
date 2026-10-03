/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run.Correctness.Internal

/-!
# The encoded block loop computes the scheduled recursive map

Canonical field words make the runtime loop agree exactly with every
intermediate semantic block tuple. Each completed level consumes its one
fresh shared seed; an arbitrary trailing word remains untouched. The
endpoint therefore preserves the final condenser/hash seed pair for leaf
extraction. Every payload bit and its block order are retained.

These are exact representation identities, including zero-depth schedules
and zero-width payloads. They need no entropy reserve or field enumeration.
Runtime bounds are proved separately in `Scheduled.Run`, and the final leaf
program is a subsequent layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The canonical initial seed produces the scheduled full block and leaves the suffix intact. -/
theorem scheduledBlockRunInitial_eq (n h Q E : Nat) (x : Fin n → Bool)
    (seed : ScheduledInitialSeed n h Q E) (tail : List Bool) :
    scheduledBlockRunInitial n h Q E (List.ofFn x)
        (encodeScheduledBlockSeedPrefix n h Q E 0 seed ++ tail) =
      { dimensions := (scheduledBlockInitialWidth n h Q E, recursiveBlockEntropy h Q 0)
        count := 1
        payload := List.ofFn (scheduledBlockInitial n h Q E x seed)
        seeds := tail } :=
  Internal.scheduledBlockRunInitial_eq n h Q E x seed tail

/-- Through any scheduled level, the actual loop serializes exactly the recursive block tuple
and consumes precisely its encoded initial and fresh seeds. -/
theorem scheduledBlockRun_iterate_eq_recursiveBlockMap (n h Q E : Nat) {i : Nat}
    (level : i ≤ h) (x : Fin n → Bool)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i)
    (tail : List Bool) :
    (scheduledBlockRunStep E)^[i] (scheduledBlockRunInitial n h Q E (List.ofFn x)
        (encodeScheduledBlockSeedPrefix n h Q E i seeds ++ tail)) =
      { dimensions := (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i,
          recursiveBlockEntropy h Q i)
        count := recursiveBlockCount 1 i
        payload := (List.ofFn fun j => List.ofFn
          (recursiveBlockMap (fun x seed (_ : Fin 1) => scheduledBlockInitial n h Q E x seed)
            (scheduledBlockStep n h Q E) i x seeds j)).flatten
        seeds := tail } :=
  Internal.scheduledBlockRun_iterate_eq_recursiveBlockMap n h Q E level x seeds tail

/-- The complete internal loop reaches the semantic leaf tuple and the exact leaf entropy,
leaving all supplied final seed bits for the finishing extractor. -/
theorem scheduledBlockRun_eq_recursiveBlockMap (n h Q E : Nat) (x : Fin n → Bool)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h)
    (tail : List Bool) :
    scheduledBlockRun n h Q E (List.ofFn x)
        (encodeScheduledBlockSeedPrefix n h Q E h seeds ++ tail) =
      { dimensions := (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h, Q)
        count := recursiveBlockCount 1 h
        payload := (List.ofFn fun j => List.ofFn
          (recursiveBlockMap (fun x seed (_ : Fin 1) => scheduledBlockInitial n h Q E x seed)
            (scheduledBlockStep n h Q E) h x seeds j)).flatten
        seeds := tail } :=
  Internal.scheduledBlockRun_eq_recursiveBlockMap n h Q E x seeds tail

end Algebraic.Cutwidth.Extractor
