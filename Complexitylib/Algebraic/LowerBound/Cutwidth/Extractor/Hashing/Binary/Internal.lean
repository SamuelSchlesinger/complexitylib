/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Complexitylib.Classes.P.BitPolynomial
import Complexitylib.Classes.P.BitPolynomial.Remainder
import Complexitylib.Classes.P.BitPolynomial.Trinomial
import Complexitylib.Encoding.BitPolynomial.Trinomial
import Complexitylib.Tactic.PolyTime

/-!
# Projection, collision count, and runtime semantics for binary hashing

Every short coefficient vector lifts to its polynomial, whose degree is
below the explicit modulus. This proves projection surjectivity. The finite
field kernel argument gives the collision count. Polynomial remainder and
prefix coefficients identify the actual list program with this semantic map.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

theorem binaryCoefficientPrefix_surjective {s m : Nat} (width : m ≤ 2 * 3 ^ s) :
    Function.Surjective (binaryCoefficientPrefix s m) := by
  intro y
  refine ⟨AdjoinRoot.mk (binaryModulus s) (Polynomial.ofFn m y), ?_⟩
  have degree : (Polynomial.ofFn m y).degree < (binaryModulus s).degree := by
    rw [Polynomial.degree_eq_natDegree (binaryModulus_monic s).ne_zero, binaryModulus_natDegree]
    exact (Polynomial.ofFn_degree_lt y).trans_le (by exact_mod_cast width)
  simp only [binaryCoefficientPrefix, LinearMap.coe_comp, Function.comp_apply,
    AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff (binaryModulus_monic s)).mpr degree]
  exact Polynomial.toFn_comp_ofFn_eq_id m y

theorem binaryFieldHash_add (s m : Nat) (a b seed : AdjoinRoot (binaryModulus s)) :
    binaryFieldHash s m (a + b) seed = binaryFieldHash s m a seed + binaryFieldHash s m b seed := by
  simp only [binaryFieldHash, mul_add, map_add]

theorem binaryFieldHash_zero (s m : Nat) (seed : AdjoinRoot (binaryModulus s)) :
    binaryFieldHash s m 0 seed = 0 := by
  simp only [binaryFieldHash, mul_zero, map_zero]

open scoped Classical in
theorem binaryFieldHash_collision_count {s m : Nat}
    [Fintype (AdjoinRoot (binaryModulus s))] (width : m ≤ 2 * 3 ^ s)
    {a b : AdjoinRoot (binaryModulus s)} (distinct : a ≠ b) :
    (Finset.univ.filter fun seed => binaryFieldHash s m a seed =
      binaryFieldHash s m b seed).card * 2 ^ m = 2 ^ (2 * 3 ^ s) := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  have fieldCard : Fintype.card (AdjoinRoot (binaryModulus s)) = 2 ^ (2 * 3 ^ s) := by
    rw [← Nat.card_eq_fintype_card, card_adjoinRoot_binaryModulus]
  have count := fieldHash_collision_count (binaryCoefficientPrefix s m).toAddMonoidHom
    (binaryCoefficientPrefix_surjective width) distinct
  have sameMap : fieldHash (binaryCoefficientPrefix s m).toAddMonoidHom = binaryFieldHash s m := rfl
  rw [sameMap, Finset.filter_congr_decidable] at count
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, fieldCard] using count

theorem binaryFieldHash_universal {s m : Nat}
    [Fintype (AdjoinRoot (binaryModulus s))] (width : m ≤ 2 * 3 ^ s) :
    UniversalHashFamily (binaryFieldHash s m) := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  exact fieldHash_universal (binaryCoefficientPrefix s m).toAddMonoidHom
    (binaryCoefficientPrefix_surjective width)

theorem binaryField_decode_inj_of_length (s n : Nat) (capacity : n ≤ 2 * 3 ^ s)
    (a b : List Bool) (ha : a.length = n) (hb : b.length = n)
    (same : BinaryFieldCodec.decode s a = BinaryFieldCodec.decode s b) : a = b := by
  have reduced (bits : List Bool) (length : bits.length = n) :
      AdjoinRoot.modByMonicHom (binaryModulus_monic s) (BinaryFieldCodec.decode s bits) =
        ofBits bits := by
    rw [BinaryFieldCodec.decode, AdjoinRoot.modByMonicHom_mk]
    apply (Polynomial.modByMonic_eq_self_iff (binaryModulus_monic s)).mpr
    rw [Polynomial.degree_eq_natDegree (binaryModulus_monic s).ne_zero, binaryModulus_natDegree]
    exact (Polynomial.ofFn_degree_lt _).trans_le (by exact_mod_cast length ▸ capacity)
  have equal := congrArg (AdjoinRoot.modByMonicHom (binaryModulus_monic s)) same
  rw [reduced a ha, reduced b hb] at equal
  apply List.ext_getElem (ha.trans hb.symm)
  intro i ia ib
  have coefficient := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i) equal
  simp only [ofBits_coeff, List.getElem?_eq_getElem ia, List.getElem?_eq_getElem ib,
    Option.getD_some] at coefficient
  exact (show Function.Injective (fun bit : Bool => (bit.toNat : ZMod 2)) from by decide) coefficient

private theorem toFn_ofBits_take (m : Nat) (bits : List Bool) :
    Polynomial.toFn m (ofBits (bits.take m)) = Polynomial.toFn m (ofBits bits) := by
  funext i
  simp only [Polynomial.toFn, LinearMap.pi_apply, Polynomial.lcoeff_apply, ofBits_coeff,
    List.getElem?_take_of_lt i.isLt]

theorem binaryHashBits_correct (s : Nat) (source seed halfDegree outputCount : List Bool)
    (half : halfDegree.length = 3 ^ s) :
    Polynomial.toFn outputCount.length (ofBits (binaryHashBits source seed halfDegree outputCount)) =
      binaryFieldHash s outputCount.length (BinaryFieldCodec.decode s source)
        (BinaryFieldCodec.decode s seed) := by
  simp only [binaryHashBits, toFn_ofBits_take, ofBits_remainderBits, ofBits_mulBits, half,
    ofBits_trinomialBits]
  unfold binaryFieldHash binaryCoefficientPrefix BinaryFieldCodec.decode
  simp only [LinearMap.coe_comp, Function.comp_apply, ← map_mul, AdjoinRoot.modByMonicHom_mk]
  rfl

theorem decodedBinaryHash_eq (s m : Nat) (source : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) :
    decodedBinaryHash s m source seed = binaryFieldHash s m (BinaryFieldCodec.decode s source) seed := by
  have correct := binaryHashBits_correct s source (BinaryFieldCodec.encode s seed)
    (List.replicate (3 ^ s) true) (List.replicate m true) (by simp)
  rw [List.length_replicate] at correct
  simpa only [decodedBinaryHash, BinaryFieldCodec.decode_encode] using correct

theorem decodedBinaryHash_addBits (s m : Nat) (a b : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) :
    decodedBinaryHash s m (addBits a b) seed =
      decodedBinaryHash s m a seed + decodedBinaryHash s m b seed := by
  simp only [decodedBinaryHash_eq, BinaryFieldCodec.decode_addBits, binaryFieldHash_add]

theorem decodedBinaryHash_universal {s m n : Nat}
    [Fintype (AdjoinRoot (binaryModulus s))]
    (capacity : n ≤ 2 * 3 ^ s) (width : m ≤ 2 * 3 ^ s) :
    UniversalHashFamily (fun bits : {bits : List Bool // bits.length = n} =>
      decodedBinaryHash s m bits.val) := by
  have sameMap : (fun bits : {bits : List Bool // bits.length = n} =>
      decodedBinaryHash s m bits.val) =
        (fun bits : {bits : List Bool // bits.length = n} =>
          binaryFieldHash s m (BinaryFieldCodec.decode s bits.val)) := by
    funext bits seed
    exact decodedBinaryHash_eq s m bits.val seed
  rw [sameMap]
  apply (binaryFieldHash_universal width).comp_injective
  intro a b same
  exact Subtype.ext (binaryField_decode_inj_of_length s n capacity
    a.val b.val a.property b.property same)

theorem decodedBinaryHash_flatStrongSeededExtractor {s m n K : Nat} {ε : ℝ}
    [Fintype (AdjoinRoot (binaryModulus s))]
    (capacity : n ≤ 2 * 3 ^ s) (width : m ≤ 2 * 3 ^ s)
    (positive : 0 < K) (error : 0 ≤ ε) (budget : (2 : ℝ) ^ m ≤ 4 * ε ^ 2 * K) :
    FlatStrongSeededExtractor (fun bits : {bits : List Bool // bits.length = n} =>
      decodedBinaryHash s m bits.val) K ε := by
  apply (decodedBinaryHash_universal capacity width).flatStrongSeededExtractor positive error
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using budget

theorem binaryHashBits_length (s : Nat) (source seed halfDegree outputCount : List Bool)
    (half : halfDegree.length = 3 ^ s) :
    (binaryHashBits source seed halfDegree outputCount).length =
      min outputCount.length (2 * 3 ^ s) := by
  have represents : ofBits (trinomialBits halfDegree.length) = binaryModulus s := by
    rw [half, ofBits_trinomialBits]
    rfl
  have nonzero : ofBits (trinomialBits halfDegree.length) ≠ 0 := by
    rw [represents]
    exact (binaryModulus_monic s).ne_zero
  have positive : significantLength (trinomialBits halfDegree.length) ≠ 0 :=
    fun zero => nonzero ((significantLength_eq_zero_iff _).mp zero)
  have degree := ofBits_natDegree (trinomialBits halfDegree.length) nonzero
  rw [represents, binaryModulus_natDegree] at degree
  simp only [binaryHashBits, List.length_take, remainderBits_length, positive, ↓reduceIte, ← degree]

theorem binaryHashEval_pair (source seed halfDegree outputCount : List Bool) :
    binaryHashEval (pair (pair source seed) (pair halfDegree outputCount)) =
      binaryHashBits source seed halfDegree outputCount := by
  simp only [binaryHashEval, pairFst_pair, pairSnd_pair]

theorem binaryHashEval_length_le (z : List Bool) : (binaryHashEval z).length ≤ z.length := by
  apply (List.length_take_le _ _).trans
  exact (pairSnd_length_le _).trans (pairSnd_length_le z)

theorem binaryHashBits_mem_FP {source seed halfDegree outputCount : List Bool → List Bool}
    (hsource : source ∈ FP) (hseed : seed ∈ FP)
    (hhalf : halfDegree ∈ FP) (hcount : outputCount ∈ FP) :
    (fun z => binaryHashBits (source z) (seed z) (halfDegree z) (outputCount z)) ∈ FP := by
  have product : (fun z => mulBits (seed z) (source z)) ∈ FP := by
    have encoded : (fun z => mulEval (pair (seed z) (source z))) ∈ FP := by polytime
    exact mem_FP_of_eq encoded fun z => mulEval_pair _ _
  have reduced : (fun z =>
      remainderBits (mulBits (seed z) (source z)) (trinomialBits (halfDegree z).length)) ∈ FP := by
    have encoded : (fun z => remainderEval
      (pair (mulBits (seed z) (source z)) (trinomialBits (halfDegree z).length))) ∈ FP := by
      polytime
    exact mem_FP_of_eq encoded fun z => remainderEval_pair _ _
  unfold binaryHashBits
  polytime

theorem binaryHashEval_mem_FP : binaryHashEval ∈ FP := by
  unfold binaryHashEval
  apply binaryHashBits_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
