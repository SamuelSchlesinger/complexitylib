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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Correctness
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Mathlib.Data.List.OfFn

/-!
# Canonical-seed execution of the near-halving block loop

Identity initialization leaves the source and every seed bit unchanged.
At each level the actual block program consumes the next canonical field
word and serializes exactly the semantic condense-then-split tuple. The
induction keeps an arbitrary trailing word and tracks the remaining depth
and its stored power explicitly, with no entropy or runtime budget premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem nearHalvingBlockRunInitial_eq (n h Q E : Nat) (x : Fin n → Bool)
    (seed : Unit) (tail : List Bool) :
    nearHalvingBlockRunInitial n h (List.ofFn x)
        (encodeNearHalvingBlockSeedPrefix n h Q E 0 seed ++ tail) =
      { width := n
        remaining := h
        remainingPower := 2 ^ h
        count := 1
        payload := List.ofFn x
        seeds := tail } := by
  rw [encodeNearHalvingBlockSeedPrefix_zero, List.nil_append]
  rfl

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
        seeds := tail } := by
  induction i generalizing tail with
  | zero =>
    simpa only [Function.iterate_zero_apply, nearHalvingBlockWidth, Nat.sub_zero,
      recursiveBlockCount, recursiveBlockMap, List.ofFn_succ, List.ofFn_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil] using
      nearHalvingBlockRunInitial_eq n h Q E x seeds tail
  | succ i ih =>
    rcases seeds with ⟨prior, fresh⟩
    rw [encodeNearHalvingBlockSeedPrefix_succ, List.append_assoc,
      Function.iterate_succ_apply', ih (by lia)]
    dsimp only [nearHalvingBlockRunStep]
    rw [← nearHalvingBlockEntropy]
    rw [show sparseFieldBits (nearHalvingBlockRate h) (explicitCondenserBudget
        (nearHalvingBlockWidth n h Q E i) (nearHalvingBlockEntropy h Q i) E) =
        (BinaryFieldCodec.encode (sparseFieldExponent (nearHalvingBlockRate h)
          (explicitCondenserBudget (nearHalvingBlockWidth n h Q E i)
            (nearHalvingBlockEntropy h Q i) E)) fresh).length from
        (BinaryFieldCodec.length_encode _ fresh).symm,
      List.take_left, List.drop_left,
      explicitBlockCondenserBits_eq_condenseSplitMap _ _ _ _ _ fresh _
        (List.length_replicate ..)]
    have remaining : h - i - 1 = h - (i + 1) := by lia
    have power : 2 ^ (h - i) / 2 = 2 ^ (h - (i + 1)) := by
      rw [show h - i = h - (i + 1) + 1 by lia, pow_succ]
      simp
    rw [remaining, power]
    rfl

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
        seeds := tail } := by
  simpa only [nearHalvingBlockRun, Nat.sub_self, pow_zero] using
    nearHalvingBlockRun_iterate_eq_recursiveBlockMap n h Q E (Nat.le_refl h) x seeds tail

end Algebraic.Cutwidth.Extractor.Internal
