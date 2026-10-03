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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Correctness
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters
import Mathlib.Data.List.OfFn

/-!
# Exact canonical-seed execution of the scheduled block loop

The initial pair recombines to the complete runtime condenser word. Each
successive loop state consumes one canonical field seed and applies the
checked one-level block serialization identity. Induction keeps an arbitrary
unconsumed suffix, so it also tracks the final extractor's seed pair without
using a reserve bound or any field enumeration.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem scheduledBlockInitial_ofFn (n h Q E : Nat) (x : Fin n → Bool)
    (seed : ScheduledInitialSeed n h Q E) :
    explicitCondenserBits n (recursiveBlockEntropy h Q 0) E 1 (List.ofFn x)
        (BinaryFieldCodec.encode (sparseFieldExponent 1
          (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E)) seed) =
      List.ofFn (scheduledBlockInitial n h Q E x seed) := by
  let half := explicitCondenserHalfWidth n (recursiveBlockEntropy h Q 0) E 1
  let bits := explicitCondenserBits n (recursiveBlockEntropy h Q 0) E 1 (List.ofFn x)
    (BinaryFieldCodec.encode (sparseFieldExponent 1
      (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E)) seed)
  have length : bits.length = half + half := by
    rw [show bits.length = _ from explicitCondenserBits_length _ _ _ _ _ _]
    exact (explicitCondenserHalfWidth_double _ _ _ _).symm
  change bits = List.ofFn ((Fin.appendEquiv half half)
    ((Fin.appendEquiv half half).symm (fun i => bits[i.val]?.getD false)))
  rw [Equiv.apply_symm_apply]
  symm
  apply List.ext_getElem (by simpa using length.symm)
  intro i _ hi
  simp [hi]

theorem scheduledBlockRunInitial_eq (n h Q E : Nat) (x : Fin n → Bool)
    (seed : ScheduledInitialSeed n h Q E) (tail : List Bool) :
    scheduledBlockRunInitial n h Q E (List.ofFn x)
        (encodeScheduledBlockSeedPrefix n h Q E 0 seed ++ tail) =
      { dimensions := (scheduledBlockInitialWidth n h Q E, recursiveBlockEntropy h Q 0)
        count := 1
        payload := List.ofFn (scheduledBlockInitial n h Q E x seed)
        seeds := tail } := by
  rw [encodeScheduledBlockSeedPrefix_zero]
  unfold scheduledBlockRunInitial
  dsimp only
  rw [show sparseFieldBits 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E) =
      (BinaryFieldCodec.encode (sparseFieldExponent 1
        (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E)) seed).length from
      (BinaryFieldCodec.length_encode _ seed).symm,
    List.take_left, List.drop_left, scheduledBlockInitial_ofFn]

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
        seeds := tail } := by
  induction i generalizing tail with
  | zero =>
    simpa only [Function.iterate_zero_apply, recursiveBlockWidth, recursiveBlockCount,
      recursiveBlockMap, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil] using scheduledBlockRunInitial_eq n h Q E x seeds tail
  | succ i ih =>
    rcases seeds with ⟨prior, fresh⟩
    rw [encodeScheduledBlockSeedPrefix_succ, List.append_assoc,
      Function.iterate_succ_apply', ih (by lia)]
    dsimp only [scheduledBlockRunStep]
    rw [show sparseFieldBits 3 (explicitCondenserBudget
        (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
        (recursiveBlockEntropy h Q i) E) =
        (BinaryFieldCodec.encode (sparseFieldExponent 3 (explicitCondenserBudget
          (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
          (recursiveBlockEntropy h Q i) E)) fresh).length from
        (BinaryFieldCodec.length_encode _ fresh).symm,
      List.take_left, List.drop_left,
      explicitBlockCondenserBits_eq_condenseSplitMap _ _ _ _ _ fresh _
        (List.length_replicate ..)]
    have entropy : recursiveBlockEntropy h Q i / 4 =
        recursiveBlockEntropy h Q (i + 1) := by
      rw [recursiveBlockEntropy_succ h Q (by lia : i < h)]
      simp
    simp only [scheduledBlockStateStep, entropy]
    rfl

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
        seeds := tail } := by
  simpa only [scheduledBlockRun, recursiveBlockEntropy_last] using
    scheduledBlockRun_iterate_eq_recursiveBlockMap n h Q E (Nat.le_refl h) x seeds tail

end Algebraic.Cutwidth.Extractor.Internal
