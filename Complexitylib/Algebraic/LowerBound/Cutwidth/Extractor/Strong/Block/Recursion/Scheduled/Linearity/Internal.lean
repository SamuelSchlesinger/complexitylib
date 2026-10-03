/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Linearity
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Correctness
import Complexitylib.Encoding.BitPolynomial.Addition

/-!
# XOR through the actual scheduled recursive maps

Exact serialization transfers coordinate addition to padded bitwise XOR.
Reading the two output halves preserves this operation. A local Boolean
addition then lets the generic recursive additivity theorem compose these
actual initial, level, and leaf maps without adding a global Boolean instance.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial

/-- Local XOR addition for applying the generic recursive composition theorem. -/
local instance scheduledBoolXorAdd : Add Bool := ⟨Bool.xor⟩

private theorem bool_add_eq_xor (a b : Bool) : a + b = Bool.xor a b := rfl

private theorem getD_addBits (a b : List Bool) (i : Nat) :
    (addBits a b)[i]?.getD false = Bool.xor (a[i]?.getD false) (b[i]?.getD false) := by
  by_cases bound : i < max a.length b.length
  · rw [addBits, List.getElem?_map, List.getElem?_range bound]
    rfl
  · have ha : a.length ≤ i := (le_max_left _ _).trans (Nat.le_of_not_gt bound)
    have hb : b.length ≤ i := (le_max_right _ _).trans (Nat.le_of_not_gt bound)
    have hout : (addBits a b).length ≤ i := by rw [addBits_length]; lia
    simp only [List.getElem?_eq_none ha, List.getElem?_eq_none hb,
      List.getElem?_eq_none hout, Option.getD_none, Bool.xor_false]

private theorem ofFn_add {n : Nat} (x x' : Fin n → Bool) :
    List.ofFn (x + x') = addBits (List.ofFn x) (List.ofFn x') := by
  apply List.ext_getElem (by simp [addBits_length])
  intro i hi hj
  have bound : i < n := by simpa using hi
  have result := (getD_addBits (List.ofFn x) (List.ofFn x') i).symm
  simpa [List.getElem?_eq_getElem, hi, hj, bound, Pi.add_apply, bool_add_eq_xor] using result

private theorem explicitCondenserBits_add (n k e u : Nat) (a b : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    explicitCondenserBits n k e u (addBits a b)
        (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e)) seed) =
      addBits
        (explicitCondenserBits n k e u a
          (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e)) seed))
        (explicitCondenserBits n k e u b
          (BinaryFieldCodec.encode
            (sparseFieldExponent u (explicitCondenserBudget n k e)) seed)) := by
  rw [← encodeCondenserOutput_decodedExplicitCondenser n k e u (addBits a b) seed,
    decodedExplicitCondenser_addBits, encodeCondenserOutput_add,
    encodeCondenserOutput_decodedExplicitCondenser n k e u a seed,
    encodeCondenserOutput_decodedExplicitCondenser n k e u b seed]

private theorem explicitCondenserPair_add (n k e u : Nat) (x x' : Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    explicitCondenserPair n k e u (x + x') seed =
      explicitCondenserPair n k e u x seed + explicitCondenserPair n k e u x' seed := by
  apply Prod.ext <;> funext i
  all_goals
    simp only [explicitCondenserPair, Fin.appendEquiv_symm_apply, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, ofFn_add, explicitCondenserBits_add]
    exact getD_addBits _ _ _

private theorem scheduledBlockInitial_add (n h Q E : Nat) (x x' : Fin n → Bool)
    (seed : ScheduledInitialSeed n h Q E) :
    scheduledBlockInitial n h Q E (x + x') seed =
      scheduledBlockInitial n h Q E x seed + scheduledBlockInitial n h Q E x' seed := by
  simp only [scheduledBlockInitial, explicitCondenserPair, Equiv.apply_symm_apply]
  funext i
  simp only [ofFn_add, explicitCondenserBits_add]
  exact getD_addBits _ _ _

private theorem scheduledBlockStep_add (n h Q E i : Nat)
    (x x' : Fin (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i) → Bool)
    (seed : ScheduledLevelSeed n h Q E i) :
    scheduledBlockStep n h Q E i (x + x') seed =
      scheduledBlockStep n h Q E i x seed + scheduledBlockStep n h Q E i x' seed :=
  explicitCondenserPair_add _ _ _ _ x x' seed

private theorem scheduledBlockLeaf_add (width ell E : Nat) (x x' : Fin width → Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent width ell E)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent width ell E))) :
    decodedOneShotExtractor width ell E (List.ofFn (x + x')) seeds =
      decodedOneShotExtractor width ell E (List.ofFn x) seeds +
        decodedOneShotExtractor width ell E (List.ofFn x') seeds := by
  rw [ofFn_add, decodedOneShotExtractor_addBits]

theorem scheduledBlockExtractor_xor (n h Q E ell : Nat) (x x' : Fin n → Bool)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    scheduledBlockExtractor n h Q E ell (fun i => Bool.xor (x i) (x' i)) seeds =
      scheduledBlockExtractor n h Q E ell x seeds +
        scheduledBlockExtractor n h Q E ell x' seeds := by
  have result := recursiveBlockExtractor_add (scheduledBlockInitial n h Q E)
    (scheduledBlockStep n h Q E) h
    (fun block seed => decodedOneShotExtractor
      (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h) ell E
      (List.ofFn block) seed)
    (scheduledBlockInitial_add n h Q E)
    (fun i _ => scheduledBlockStep_add n h Q E i)
    (scheduledBlockLeaf_add _ ell E) x x' seeds
  exact result

end Algebraic.Cutwidth.Extractor.Internal
