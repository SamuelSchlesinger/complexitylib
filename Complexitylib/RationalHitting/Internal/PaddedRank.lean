/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Rectangular

/-!
# Rational hitting lists: padded rank

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/PaddedRank.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.TestPolynomial
open Polynomial Matrix Module
open LaurentReduction SmallExpansion Rectangular RectangularExpansion
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

lemma polynomialMap_single (M : ℕ) (b : Fin M) :
    polynomialMap M (Pi.single b (1 : K)) = X^b.val := by
  ext j
  by_cases hj : j < M
  · rw [polynomialMap_coeff M _ ⟨j,hj⟩,coeff_X_pow]
    simp [Pi.single_apply,Fin.ext_iff,eq_comm]
  · rw [polynomialMap_coeff_high M _ j (Nat.le_of_not_gt hj)]
    rw [coeff_X_pow]
    have hb : b.val ≠ j := by omega
    simp [Ne.symm hb]

lemma taylor_matrix (M : ℕ) (a : K) (i j : Fin M) :
    LinearMap.toMatrix' (taylorCoordinates M a).toLinearMap i j =
      (((X + C a)^j.val : K[X]).coeff i.val) := by
  change taylorCoordinates M a (Pi.single j 1) i = _
  rw [taylorCoordinates_apply,polynomialMap_single,taylor_X_pow]

lemma taylorCoordinates_symm (M : ℕ) (a : K) :
    (taylorCoordinates M a).symm = taylorCoordinates M (-a) := by
  ext x i
  rfl

lemma reverseCoordinates_symm_apply (M : ℕ) (x : Fin M → K) :
    (reverseCoordinates M).symm x = fun j => x j.rev := rfl

lemma reverseTaylor_symm_matrix (M : ℕ) (a : K) (i j : Fin M) :
    LinearMap.toMatrix' (reverseTaylorCoordinates M a).symm.toLinearMap i j =
      (((X + C (-a))^j.rev.val : K[X]).coeff i.val) := by
  rw [LinearMap.toMatrix'_apply]
  simp only [reverseTaylorCoordinates, LinearEquiv.trans_symm,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, reverseCoordinates_symm_apply]
  rw [taylorCoordinates_symm]
  have he : (fun k : Fin M => (Pi.single j (1 : K) : Fin M → K) k.rev) =
      (Pi.single j.rev (1 : K) : Fin M → K) := by
    funext k
    simp only [Pi.single_apply]
    have hh : k.rev = j ↔ k = j.rev := by
      constructor <;> intro h
      · rw [← Fin.rev_rev k,h]
      · rw [h,Fin.rev_rev]
    congr 1
    exact propext hh
  rw [he,taylorCoordinates_apply,polynomialMap_single,taylor_X_pow]

/-- The reverse-Taylor test matrix over the univariate polynomial ring in t.
Summation over all M Taylor coordinates appends only zero terms. -/
def full (M : ℕ) (a : K) : Matrix (Fin M) (Fin M) K[X] := fun i j =>
  ∑ r : Fin M, C ((((X+C (-a))^r.rev.val : K[X]).coeff i.val) *
    (((X+C a)^j.val : K[X]).coeff r.val)) * X^r.val

/-- The polynomial test matrix with columns above the threshold set to zero. -/
def padded (M N : ℕ) (a : K) : Matrix (Fin M) (Fin M) K[X] :=
  fun i j => if j.val < N then full M a i j else 0

/-- The original t indeterminate embeds into the fresh Laurent indeterminate. -/
def embed : K[X] →+* F K := Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single 1 1)

lemma embed_C (a : K) : embed (C a) = HahnSeries.C a := by simp [embed]
lemma embed_X_pow (a : ℕ) : embed ((X : K[X])^a) = HahnSeries.single (a : ℤ) 1 := by
  simp [embed,HahnSeries.single_pow]

lemma full_embed (M : ℕ) (a : K) :
    (embed.mapMatrix (full M a)) = LinearMap.toMatrix' (testMap M a) := by
  apply Matrix.ext
  intro i j
  change embed (full M a i j) = testMap M a (Pi.single j 1) i
  simp only [full,map_sum,map_mul,embed_C,embed_X_pow]
  change _ = liftMap (reverseTaylorCoordinates M a).symm.toLinearMap
    (weightMap Fin.val (liftMap (taylorCoordinates M a).toLinearMap (Pi.single j 1))) i
  rw [liftMap_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [reverseTaylor_symm_matrix]
  have hin : liftMap (taylorCoordinates M a).toLinearMap (Pi.single j (1 : F K)) r =
      HahnSeries.C ((((X+C a)^j.val : K[X]).coeff r.val)) := by
    rw [liftMap_apply]
    simp [Pi.single_apply,taylorCoordinates_apply,polynomialMap_single]
  simp only [weightMap,LinearMap.coe_mk,AddHom.coe_mk,hin]
  ring

lemma full_natDegree_le (M : ℕ) (a : K) (i j : Fin M) :
    (full M a i j).natDegree ≤ M-1 := by
  apply natDegree_sum_le_of_forall_le
  intro r _
  apply (natDegree_C_mul_le _ _).trans
  simpa using Nat.le_sub_one_of_lt r.isLt

lemma padded_natDegree_le (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).natDegree ≤ M-1 := by
  by_cases hj : j.val < N
  · simpa [padded,hj] using full_natDegree_le M a i j
  · simp [padded,hj]

end
end RationalHitting.TestPolynomial

namespace RationalHitting.PaddedRank
open Matrix Module
open TestPolynomial LaurentReduction SmallExpansion Rectangular RectangularExpansion
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The full block matrix formed from the coefficient and test matrices. -/
def raw {w q M : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (R : Fin w → Matrix (Fin M) (Fin M) (F K)) :
    Matrix (Fin q × Fin M) (Fin q × Fin M) (F K) :=
  fun a b => ∑ i, A i a.1 b.1 * R i a.2 b.2

lemma raw_apply.{v_1} {K : Type v_1} [Field K]  {w q M : ℕ}
  (A : Fin w → Matrix (Fin q) (Fin q) (RationalHitting.LaurentReduction.F K))
  (R : Fin w → Matrix (Fin M) (Fin M) (RationalHitting.LaurentReduction.F K))
  (f : Fin q × Fin M → RationalHitting.LaurentReduction.F K) (α : Fin q) (j : Fin M) :
  (RationalHitting.PaddedRank.raw A R).mulVec f (α, j) =
    ∑ i, ∑ γ, A i α γ * (R i).mulVec (fun b => f (γ, b)) j := by
  simp only [Matrix.mulVec, dotProduct, raw, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin w)))
    (t := (Finset.univ : Finset (Fin q)))]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Pad vectors in the truncated column space with zeros. -/
def extend (q M N : ℕ) : (Fin q × Fin N → F K) →ₗ[F K] (Fin q × Fin M → F K) where
  toFun f a := if h : a.2.val < N then f (a.1,⟨a.2.val,h⟩) else 0
  map_add' f g := by ext a; dsimp; split_ifs <;> simp
  map_smul' c f := by ext a; dsimp; split_ifs <;> simp

lemma extend_low.{v_1} {K : Type v_1} [Field K]  (q M N : ℕ)
  (f : Fin q × Fin N → RationalHitting.LaurentReduction.F K) (α : Fin q) (j : Fin M) :
  N ≤ ↑j → (RationalHitting.PaddedRank.extend q M N) f (α, j) = 0 := by
  intro hj
  simp [extend,not_lt.mpr hj]

lemma extend_injective.{v_1} {K : Type v_1} [Field K]
  (q M N : ℕ) (hNM : N ≤ M) :
  Function.Injective ⇑(RationalHitting.PaddedRank.extend (K := K) q M N) := by
  intro f g h
  funext ⟨α,j⟩
  have hh := congrFun h (α,⟨j.val,j.isLt.trans_le hNM⟩)
  simpa [extend,j.isLt] using hh

lemma padded_mulVec_low.{v_1} {K : Type v_1} [Field K]  (M N : ℕ)
  (a : K) (f : Fin M → RationalHitting.LaurentReduction.F K)
  (hf : ∀ (j : Fin M), N ≤ ↑j → f j = 0) :
  (RationalHitting.TestPolynomial.embed.mapMatrix
          (RationalHitting.TestPolynomial.padded M N a)).mulVec
      f =
    (RationalHitting.SmallExpansion.testMap M a) f := by
  rw [← Matrix.toLin'_toMatrix' (testMap M a), ← full_embed M a, Matrix.toLin'_apply]
  funext i
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < N
  · simp [padded,hj]
  · simp [padded,hj,hf j (Nat.le_of_not_gt hj)]

/-- The padded test matrices satisfy a rectangular rank lower bound,
using an invertible witness and the expansion theorem. -/
theorem rank_ge (w B M N q e : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N+2*w^3*B) (hq : q ≤ B) (he : 0 < e)
    (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (X : Fin w → Matrix (Fin e) (Fin e) (F K))
    (hX : Function.Injective (blockEval A X)) :
    q*N ≤ (raw A (fun i => embed.mapMatrix (padded M N (points i)))).rank := by
  let R := fun i => embed.mapMatrix (padded M N (points i))
  let L := (raw A R).mulVecLin.comp (extend q M N)
  have hi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    let f : Fin q → Fin M → F K := fun α j => extend q M N v (α,j)
    have hf : ∀ α j, N ≤ j.val → f α j = 0 := extend_low q M N v
    have hker : ∀ α, ∑ i, ∑ γ, A i α γ • testMap M (points i) (f γ) = 0 := by
      intro α
      funext j
      have hh := congrFun hv (α,j)
      change (raw A R).mulVec (extend q M N v) (α,j) = 0 at hh
      rw [raw_apply] at hh
      simpa only [R, f, padded_mulVec_low M N _ _ (hf _),
        Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hh
    have hzero := rectangular_kernel_zero w B M N q e hw hN hMN hq he points hp A X hX f hf hker
    have hext : extend q M N v = 0 := by
      funext ⟨α,j⟩
      exact congrFun (congrFun hzero α) j
    apply extend_injective q M N (by omega)
    simpa only [map_zero] using hext
  let E := LinearMap.toMatrix' (extend (K := K) q M N)
  have hE : E.mulVecLin = extend q M N := Matrix.toLin'_toMatrix' _
  have hr : (raw A R * E).rank = q*N := by
    rw [Matrix.rank,Matrix.mulVecLin_mul,hE]
    rw [LinearMap.finrank_range_of_inj hi]
    simp
  exact hr ▸ Matrix.rank_mul_le_left (raw A R) E

lemma numeric_gap (w B M N q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hMN : M = N+2*w^3*B) (hM : B*(2*w^3*B) < M) : (q-1)*M < q*N := by
  have hh : q*(2*w^3*B) < M := (Nat.mul_le_mul_right _ hqB).trans_lt hM
  have hq' : q-1+1=q := by omega
  have heq : q*M = (q-1)*M+M := by
    calc
      _ = (q-1+1)*M := by rw [hq']
      _ = _ := by ring
  have heq' : q*N+q*(2*w^3*B) = (q-1)*M+M := by
    calc
      _ = q*M := by rw [hMN]; ring
      _ = _ := heq
  omega

end
end RationalHitting.PaddedRank

namespace RationalHitting.TestPolynomial
open Polynomial Matrix
open LaurentReduction
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E]

lemma map_taylor_coeff (φ : K →+* E) (a : K) (j r : ℕ) :
    φ (((X+C a)^j : K[X]).coeff r) = (((X+C (φ a))^j : E[X]).coeff r) := by
  rw [← Polynomial.coeff_map]
  simp

lemma full_map (φ : K →+* E) (M : ℕ) (a : K) (i j : Fin M) :
    (full M a i j).map φ = full M (φ a) i j := by
  unfold full
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul]
  rw [map_taylor_coeff φ (-a),map_taylor_coeff φ a,map_neg]

lemma padded_map (φ : K →+* E) (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).map φ = padded M N (φ a) i j := by
  by_cases hj : j.val < N <;> simp [padded,hj,full_map]

lemma eval₂_padded (φ : K →+* E) (M N : ℕ) (a : K) (i j : Fin M) :
    (padded M N a i j).eval₂ (HahnSeries.C.comp φ) (HahnSeries.single 1 1) =
      embed (padded M N (φ a) i j) := by
  rw [← padded_map φ M N a i j]
  change (padded M N a i j).eval₂ ((HahnSeries.C : E →+* F E).comp φ) (HahnSeries.single (1 : ℤ)
    1) =
    ((padded M N a i j).map φ).eval₂ HahnSeries.C (HahnSeries.single 1 1)
  rw [Polynomial.eval₂_map]

end
end RationalHitting.TestPolynomial

end Complexity
