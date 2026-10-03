/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Boolean.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Correctness
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Linearity
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Equiv
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
import Mathlib.Data.Vector.Basic

/-!
# Transporting the actual bit program's retained-seed law

Exact program serialization identifies every output coordinate. The canonical
seed codec and the two-element output equivalence then transport strong
extraction without changing its cap or error. Finite-field instances are
derived locally from the proved quotient cardinalities.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial

private theorem coefficientBlock_flatten_ofFn (t width : Nat) (blocks : Fin t → List Bool)
    (length : ∀ i, (blocks i).length = width) (i : Fin t) :
    coefficientBlock (List.ofFn blocks).flatten width i.val = blocks i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [coefficientBlock, Fin.val_zero, Nat.zero_mul, List.drop_zero,
        List.ofFn_succ, List.flatten_cons]
      exact List.take_left' (length 0)
    · simp only [coefficientBlock, Fin.val_succ, Nat.add_mul, Nat.one_mul,
        List.ofFn_succ, List.flatten_cons]
      rw [Nat.add_comm (j.val * width) width, ← length 0, List.drop_length_add_append]
      simpa only [coefficientBlock, ← length 0] using
        ih (fun j => blocks j.succ) (fun j => length j.succ) j

theorem scheduledBlockBooleanExtractor_eq (n h Q E ell : Nat) (x : Fin n → Bool)
    (seed : Fin (scheduledBlockSeedBits n h Q E ell) → Bool)
    (i : Fin (recursiveBlockCount 1 h)) (j : Fin ell) :
    scheduledBlockBooleanExtractor n h Q E ell x seed i j =
      decide (scheduledBlockExtractor n h Q E ell x
        (decodeScheduledBlockSeeds n h Q E ell (List.ofFn seed)) i j = 1) := by
  have correct := scheduledBlockExtractorBits_eq_scheduledBlockExtractor n h Q E ell x
    (decodeScheduledBlockSeeds n h Q E ell (List.ofFn seed))
  rw [encode_decodeScheduledBlockSeeds n h Q E ell (List.ofFn seed) List.length_ofFn] at correct
  dsimp only [scheduledBlockBooleanExtractor]
  rw [correct, coefficientBlock_flatten_ofFn _ ell _ (fun _ => List.length_ofFn) i]
  simp

private noncomputable def booleanSeedEquiv (n h Q E ell : Nat) :
    (Fin (scheduledBlockSeedBits n h Q E ell) → Bool) ≃
      (RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
        ScheduledFinalSeed n h Q E ell) :=
  (Equiv.vectorEquivFin Bool _).symm.trans
    { toFun bits := decodeScheduledBlockSeeds n h Q E ell bits.val
      invFun seeds := ⟨encodeScheduledBlockSeeds n h Q E ell seeds,
        encodeScheduledBlockSeeds_length n h Q E ell seeds⟩
      left_inv bits := Subtype.ext
        (encode_decodeScheduledBlockSeeds n h Q E ell bits.val bits.property)
      right_inv := decode_encodeScheduledBlockSeeds n h Q E ell }

private theorem booleanSeedEquiv_apply (n h Q E ell : Nat)
    (seed : Fin (scheduledBlockSeedBits n h Q E ell) → Bool) :
    booleanSeedEquiv n h Q E ell seed =
      decodeScheduledBlockSeeds n h Q E ell (List.ofFn seed) := by
  simp only [booleanSeedEquiv, Equiv.trans_apply, Equiv.vectorEquivFin,
    Equiv.coe_fn_symm_mk]
  change decodeScheduledBlockSeeds n h Q E ell (List.Vector.ofFn seed).toList = _
  rw [List.Vector.toList_ofFn]

private def booleanBitEquiv : ZMod 2 ≃ Bool where
  toFun c := decide (c = 1)
  invFun b := (b.toNat : ZMod 2)
  left_inv := by decide
  right_inv := by decide

private def booleanOutputEquiv (t ell : Nat) :
    (Fin t → Fin ell → ZMod 2) ≃ (Fin t → Fin ell → Bool) where
  toFun f i j := booleanBitEquiv (f i j)
  invFun f i j := booleanBitEquiv.symm (f i j)
  left_inv f := by funext i j; exact booleanBitEquiv.symm_apply_apply (f i j)
  right_inv f := by funext i j; exact booleanBitEquiv.apply_symm_apply (f i j)

theorem scheduledBlockBooleanExtractor_xor (n h Q E ell : Nat) (x x' : Fin n → Bool)
    (seed : Fin (scheduledBlockSeedBits n h Q E ell) → Bool) :
    scheduledBlockBooleanExtractor n h Q E ell (fun i => Bool.xor (x i) (x' i)) seed =
      fun i j => Bool.xor (scheduledBlockBooleanExtractor n h Q E ell x seed i j)
        (scheduledBlockBooleanExtractor n h Q E ell x' seed i j) := by
  funext i j
  rw [scheduledBlockBooleanExtractor_eq, scheduledBlockBooleanExtractor_eq,
    scheduledBlockBooleanExtractor_eq, scheduledBlockExtractor_xor]
  change decide ((_ + _ : ZMod 2) = 1) = _
  exact (by decide : ∀ a b : ZMod 2,
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1))) _ _

private theorem boolean_extraction_of_semantic (n h Q E ell : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor (scheduledBlockExtractor n h Q E ell) K ε) :
    WeightedStrongSeededExtractor (scheduledBlockBooleanExtractor n h Q E ell) K ε := by
  have same : scheduledBlockBooleanExtractor n h Q E ell =
      (fun x seed => booleanOutputEquiv (recursiveBlockCount 1 h) ell
        (scheduledBlockExtractor n h Q E ell x (booleanSeedEquiv n h Q E ell seed))) := by
    funext x seed i j
    rw [booleanSeedEquiv_apply]
    exact scheduledBlockBooleanExtractor_eq n h Q E ell x seed i j
  rw [same]
  exact extract.equiv (booleanSeedEquiv n h Q E ell)
    (booleanOutputEquiv (recursiveBlockCount 1 h) ell)

private noncomputable abbrev binaryFieldFintypes (s : Nat) :
    Fintype (AdjoinRoot (binaryModulus s)) := by
  let : Finite (AdjoinRoot (binaryModulus s)) :=
    Nat.finite_of_card_ne_zero (by rw [card_adjoinRoot_binaryModulus]; positivity)
  exact Fintype.ofFinite _

theorem scheduledBlockBooleanExtractor_weighted (n h Q E ell : Nat)
    (budget : 3 * (24 * explicitCondenserBudget (scheduledBlockInitialWidth n h Q E)
      (recursiveBlockEntropy h Q 0) E) + 6 * E ≤ 2 * Q)
    (reserve : ell + 2 * E ≤ Q) :
    WeightedStrongSeededExtractor (scheduledBlockBooleanExtractor n h Q E ell)
      (2 ^ recursiveBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) := by
  let : ∀ s, Fintype (AdjoinRoot (binaryModulus s)) := binaryFieldFintypes
  exact boolean_extraction_of_semantic n h Q E ell
    (scheduledBlockExtractor_weighted n h Q E ell budget reserve)

theorem scheduledBlockBooleanExtractor_dyadic (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    WeightedStrongSeededExtractor
      (scheduledBlockBooleanExtractor n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) := by
  let : ∀ s, Fintype (AdjoinRoot (binaryModulus s)) := binaryFieldFintypes
  exact boolean_extraction_of_semantic _ _ _ _ _
    (scheduledBlockExtractor_dyadic n h L e length depth)

end Algebraic.Cutwidth.Extractor.Internal
