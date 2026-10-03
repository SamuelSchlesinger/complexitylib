/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Correctness.Internal

/-!
# The runtime block loop computes the near-halving recursive map

Identity initialization consumes no seed. At every completed level the
actual payload is exactly the serialized semantic block tuple, in the same
order. The loop consumes precisely the canonical field-seed prefix and
leaves an arbitrary trailing word untouched, including the final one-shot
seed pair. Its remaining depth and stored power follow the exact schedule.

The identities cover zero depth and zero-width payloads. No entropy reserve,
field enumeration, or runtime bound is a premise. Polynomial-time bounds
are proved separately in `NearHalving.Run`; final leaf extraction is a
subsequent layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Identity initialization keeps the input and the entire suffix after the empty seed prefix. -/
theorem nearHalvingBlockRunInitial_eq (n h Q E : Nat) (x : Fin n → Bool)
    (seed : Unit) (tail : List Bool) :
    nearHalvingBlockRunInitial n h (List.ofFn x)
        (encodeNearHalvingBlockSeedPrefix n h Q E 0 seed ++ tail) =
      { width := n
        remaining := h
        remainingPower := 2 ^ h
        count := 1
        payload := List.ofFn x
        seeds := tail } :=
  Internal.nearHalvingBlockRunInitial_eq n h Q E x seed tail

/-- Through any scheduled level, the actual loop serializes the exact recursive block tuple,
consumes its canonical fresh seeds, and preserves the supplied trailing word. -/
theorem nearHalvingBlockRun_iterate_eq_recursiveBlockMap (n h Q E : Nat) {i : Nat}
    (level : i ≤ h) (x : Fin n → Bool)
    (seeds : RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i)
    (tail : List Bool) :
    (nearHalvingBlockRunStep h Q E)^[i] (nearHalvingBlockRunInitial n h (List.ofFn x)
        (encodeNearHalvingBlockSeedPrefix n h Q E i seeds ++ tail)) =
      { width := nearHalvingBlockWidth n h Q E i
        remaining := h - i
        remainingPower := 2 ^ (h - i)
        count := recursiveBlockCount 1 i
        payload := (List.ofFn fun j => List.ofFn
          (recursiveBlockMap (fun (x : Fin n → Bool) (_ : Unit) (_ : Fin 1) => x)
            (nearHalvingBlockStep n h Q E) i x seeds j)).flatten
        seeds := tail } :=
  Internal.nearHalvingBlockRun_iterate_eq_recursiveBlockMap n h Q E level x seeds tail

/-- The complete internal loop reaches the semantic leaves with no levels remaining,
leaving every trailing seed bit available to the final extractor. -/
theorem nearHalvingBlockRun_eq_recursiveBlockMap (n h Q E : Nat) (x : Fin n → Bool)
    (seeds : RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) h)
    (tail : List Bool) :
    nearHalvingBlockRun n h Q E h (List.ofFn x)
        (encodeNearHalvingBlockSeedPrefix n h Q E h seeds ++ tail) =
      { width := nearHalvingBlockWidth n h Q E h
        remaining := 0
        remainingPower := 1
        count := recursiveBlockCount 1 h
        payload := (List.ofFn fun j => List.ofFn
          (recursiveBlockMap (fun (x : Fin n → Bool) (_ : Unit) (_ : Fin 1) => x)
            (nearHalvingBlockStep n h Q E) h x seeds j)).flatten
        seeds := tail } :=
  Internal.nearHalvingBlockRun_eq_recursiveBlockMap n h Q E x seeds tail

end Algebraic.Cutwidth.Extractor
