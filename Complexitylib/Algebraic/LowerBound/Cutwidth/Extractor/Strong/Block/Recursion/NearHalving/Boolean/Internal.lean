/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Equiv
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Prod

/-!
# Boolean seed and output transport for near-halving extraction

The exact seed codec and the two-element field equivalence preserve the
joint strong-extraction tests. Uncurrying through the finite product
equivalence places output coordinates in block order. Field finiteness is
derived locally from the proved quotient cardinalities.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private noncomputable def seedEquiv (n h Q E : Nat) :
    (Fin (nearHalvingBlockSeedBits n h Q E) → Bool) ≃ NearHalvingBlockSeeds n h Q E :=
  (Equiv.vectorEquivFin Bool _).symm.trans (nearHalvingBlockSeedEquiv n h Q E).symm

private theorem seedEquiv_apply (n h Q E : Nat)
    (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool) :
    seedEquiv n h Q E seed = decodeNearHalvingBlockSeeds n h Q E (List.ofFn seed) := by
  change (nearHalvingBlockSeedEquiv n h Q E).symm
    ⟨(List.Vector.ofFn seed).toList, (List.Vector.ofFn seed).property⟩ = _
  rw [nearHalvingBlockSeedEquiv_symm_apply]
  change decodeNearHalvingBlockSeeds n h Q E (List.Vector.ofFn seed).toList = _
  rw [List.Vector.toList_ofFn]

private def bitEquiv : ZMod 2 ≃ Bool where
  toFun c := decide (c = 1)
  invFun b := (b.toNat : ZMod 2)
  left_inv := by decide
  right_inv := by decide

private def outputEquiv (t ell : Nat) :
    (Fin t → Fin ell → ZMod 2) ≃ (Fin (t * ell) → Bool) :=
  (Equiv.curry (Fin t) (Fin ell) (ZMod 2)).symm.trans
    ((finProdFinEquiv : Fin t × Fin ell ≃ Fin (t * ell)).arrowCongr bitEquiv)

private theorem outputEquiv_ofFn (t ell : Nat) (f : Fin t → Fin ell → ZMod 2) :
    List.ofFn (outputEquiv t ell f) =
      (List.ofFn fun i => List.ofFn fun j => decide (f i j = 1)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have bound : i.val * ell + j.val < t * ell := by
    have result := (finProdFinEquiv (i, j)).isLt
    change j.val + ell * i.val < t * ell at result
    simpa only [Nat.mul_comm, Nat.add_comm] using result
  have index : (⟨i.val * ell + j.val, bound⟩ : Fin (t * ell)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  change decide (f (finProdFinEquiv.symm _).1 (finProdFinEquiv.symm _).2 = 1) = _
  rw [index, Equiv.symm_apply_apply]

private theorem boolean_extraction_of_semantic (n h Q E : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor (nearHalvingBlockExtractor n h Q E) K ε) :
    WeightedStrongSeededExtractor (nearHalvingBlockBooleanExtractor n h Q E) K ε := by
  have same : nearHalvingBlockBooleanExtractor n h Q E =
      (fun x seed => outputEquiv (recursiveBlockCount 1 h) (nearHalvingBlockLeafLength h Q)
        (nearHalvingBlockExtractor n h Q E x (seedEquiv n h Q E seed))) := by
    funext x seed j
    rw [seedEquiv_apply]
    rfl
  rw [same]
  exact extract.equiv (seedEquiv n h Q E)
    (outputEquiv (recursiveBlockCount 1 h) (nearHalvingBlockLeafLength h Q))

private noncomputable abbrev binaryFieldFintypes (s : Nat) :
    Fintype (AdjoinRoot (binaryModulus s)) := by
  let : Finite (AdjoinRoot (binaryModulus s)) :=
    Nat.finite_of_card_ne_zero (by rw [card_adjoinRoot_binaryModulus]; positivity)
  exact Fintype.ofFinite _

theorem nearHalvingBlockBooleanExtractor_weighted (n h Q E : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) E + 4 * E ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockBooleanExtractor n h Q E)
      (2 ^ nearHalvingBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) := by
  let : ∀ s, Fintype (AdjoinRoot (binaryModulus s)) := binaryFieldFintypes
  exact boolean_extraction_of_semantic n h Q E
    (nearHalvingBlockExtractor_weighted n h Q E capacity budget)

theorem nearHalvingBlockBooleanExtractor_dyadic (n h Q e : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) (e + h + 2) +
      4 * (e + h + 2) ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockBooleanExtractor n h Q (e + h + 2))
      (2 ^ nearHalvingBlockEntropy h Q 0) (((2 : ℝ) ^ e)⁻¹) := by
  let : ∀ s, Fintype (AdjoinRoot (binaryModulus s)) := binaryFieldFintypes
  exact boolean_extraction_of_semantic n h Q (e + h + 2)
    (nearHalvingBlockExtractor_dyadic n h Q e capacity budget)

theorem nearHalvingBlockBooleanExtractor_ofFn (n h Q E : Nat) (x : Fin n → Bool)
    (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool) :
    List.ofFn (nearHalvingBlockBooleanExtractor n h Q E x seed) =
      (List.ofFn fun i => List.ofFn fun j => decide (nearHalvingBlockExtractor n h Q E x
        (decodeNearHalvingBlockSeeds n h Q E (List.ofFn seed)) i j = 1)).flatten :=
  outputEquiv_ofFn (recursiveBlockCount 1 h) (nearHalvingBlockLeafLength h Q)
    (nearHalvingBlockExtractor n h Q E x
      (decodeNearHalvingBlockSeeds n h Q E (List.ofFn seed)))

end Algebraic.Cutwidth.Extractor.Internal
