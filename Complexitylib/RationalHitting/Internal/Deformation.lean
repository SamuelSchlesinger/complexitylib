/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BlockDivision

/-!
# Rational hitting lists: deformation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Deformation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.QuantumLift
open HahnSeries Matrix MvPolynomial
open RationalHitting.QuantumMatrices RationalHitting.PolynomialHahn
open RationalHitting.BlockDivision
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- The two-parameter polynomial lift. -/
def polynomialLift (R : Matrix (ZMod d) (ZMod d) K) :
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 2) K) := fun i j =>
  ∑ a : ZMod d, ∑ b : ZMod d,
    monomial (Finsupp.single 0 a.val + Finsupp.single 1 b.val)
      (fourierCoeff χ R a b * weyl χ a b i j)

omit [CharZero K] in
lemma polynomialLift_embed (R : Matrix (ZMod d) (ZMod d) K) :
    PolynomialHahn.embed.mapMatrix (polynomialLift χ R) = representation χ (liftD χ R) := by
  ext i j g
  change (PolynomialHahn.embed (polynomialLift χ R i j)).coeff g = (lift χ R).coeff g i j
  simp only [polynomialLift, map_sum, HahnSeries.coeff_sum, embed_monomial,
    lift, Matrix.sum_apply, ]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have he : exponent (Finsupp.single 0 a.val + Finsupp.single 1 b.val) =
      toLex ((a.val : ℤ), (b.val : ℤ)) := by simp [exponent]
  rw [he]
  simp only [HahnSeries.coeff_single]
  split_ifs <;> rfl

lemma polynomialLift_specialize (hχ : χ.IsPrimitive) (R : Matrix (ZMod d) (ZMod d) K) :
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom.mapMatrix
      (polynomialLift χ R) = R := by
  have h := fourier_reconstruction χ hχ R
  ext i j
  have hij := congrFun (congrFun h i) j
  simpa [polynomialLift, eval_monomial, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] using hij

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Flatten a block matrix after applying the polynomial lift to each block. -/
def blockPolynomial (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    Matrix (m × ZMod d) (m × ZMod d) (MvPolynomial (Fin 2) K) :=
  fun i j => polynomialLift χ (A i.1 j.1) i.2 j.2

/-- Flatten the original block matrix over the coefficient field. -/
def blockOriginal (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    Matrix (m × ZMod d) (m × ZMod d) K := fun i j => A i.1 j.1 i.2 j.2

omit [CharZero K] in
lemma blockPolynomial_embed (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    PolynomialHahn.embed.mapMatrix (blockPolynomial χ A) =
      blockEmbedding (representation χ) (fun i j => liftD χ (A i j)) := by
  funext ⟨i,a⟩ ⟨j,b⟩
  exact congrFun (congrFun (polynomialLift_embed χ (A i j)) a) b

lemma blockPolynomial_specialize (hχ : χ.IsPrimitive)
    (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom.mapMatrix
      (blockPolynomial χ A) = blockOriginal A := by
  funext ⟨i,a⟩ ⟨j,b⟩
  exact congrFun (congrFun (polynomialLift_specialize χ hχ (A i j)) a) b

/-- The rank gap forces the determinant of the actual polynomial lift to be
nonzero. The Hahn division ring is only a proof device; the resulting polynomial
is the original finite Fourier lift, not a new generator. -/
theorem blockPolynomial_det_ne_zero (hχ : χ.IsPrimitive)
    (A : Matrix m m (Matrix (ZMod d) (ZMod d) K))
    (hm : 1 ≤ Fintype.card m)
    (hA : (Fintype.card m - 1)*d < (blockOriginal A).rank) :
    (blockPolynomial χ A).det ≠ 0 := by
  let B := blockPolynomial χ A
  have hrank := RationalHitting.RankSpecialization.rank_le
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))) PolynomialHahn.embed
    PolynomialHahn.embed_injective B
  rw [blockPolynomial_specialize χ hχ, blockPolynomial_embed] at hrank
  have hu := isUnit_of_rank_gt (representation χ) (fun i j => liftD χ (A i j)) hm
    (by simpa [ZMod.card] using hA.trans_le hrank)
  have hdet : (PolynomialHahn.embed.mapMatrix B).det ≠ 0 := by
    rw [blockPolynomial_embed]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero
  intro hz
  rw [← RingHom.map_det, hz, map_zero] at hdet
  exact hdet rfl

end
end RationalHitting.QuantumLift

namespace RationalHitting.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices QuantumLift
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- Coefficient polynomials for the exact cyclic-diagonal Fourier transform. -/
def coeffP (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) : K[X] :=
  Polynomial.C ((d : K)⁻¹) * ∑ j, Polynomial.C (χ (-a*j)) * R j (j-b)

/-- Embed the univariate parameter as the first of three polynomial variables. -/
def uni : K[X] →+* MvPolynomial (Fin 3) K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

/-- The three-parameter polynomial lift, before specialization. -/
def lift (R : Matrix (ZMod d) (ZMod d) K[X]) :
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 3) K) := fun i j =>
  ∑ a : ZMod d, ∑ b : ZMod d,
    uni (coeffP χ R a b) * MvPolynomial.C (weyl χ a b i j) *
      MvPolynomial.X 1 ^ a.val * MvPolynomial.X 2 ^ b.val

/-- Embed t into a coefficient field, leaving p,r polynomial indeterminates. -/
def specialize (φ : K →+* E) (t : E) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) E :=
  eval₂Hom (MvPolynomial.C.comp φ) (Fin.cases (MvPolynomial.C t) MvPolynomial.X)

lemma specialize_uni (φ : K →+* E) (t : E) (p : K[X]) :
    specialize φ t (uni p) = MvPolynomial.C (p.eval₂ φ t) := by
  have he : (specialize φ t).comp uni =
      MvPolynomial.C.comp (Polynomial.eval₂RingHom φ t) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [specialize,uni]
    · simp [specialize,uni]
  exact congrArg (fun h : K[X] →+* MvPolynomial (Fin 2) E => h p) he

lemma coeffP_eval (φ : K →+* E) (t : E)
    (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    (coeffP χ R a b).eval₂ φ t =
      QuantumMatrices.fourierCoeff (φ.toMonoidHom.compAddChar χ) ((Polynomial.eval₂RingHom φ
        t).mapMatrix R) a b := by
  simp [coeffP,QuantumMatrices.fourierCoeff,Polynomial.eval₂_mul,Polynomial.eval₂_finsetSum]

lemma weyl_map.{v_1, v_2} {K : Type v_1} {E : Type v_2} [Field K] [Field E]
  {d : ℕ}  (χ : AddChar (ZMod d) K) (φ : K →+* E) (a b i j : ZMod d) :
  φ (weyl χ a b i j) = weyl (φ.toMonoidHom.compAddChar χ) a b i j := by
  by_cases h : i = j+b <;> simp [weyl,h]

lemma specialize_lift (φ : K →+* E) (t : E)
    (R : Matrix (ZMod d) (ZMod d) K[X]) :
    (specialize φ t).mapMatrix (lift χ R) =
      polynomialLift (φ.toMonoidHom.compAddChar χ) ((Polynomial.eval₂RingHom φ t).mapMatrix R) := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply,lift,map_sum,map_mul,map_pow,
    specialize_uni,coeffP_eval]
  simp only [specialize,eval₂Hom_X',eval₂Hom_C,RingHom.comp_apply,weyl_map,polynomialLift]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial,map_mul]
  rfl

lemma uni_totalDegree_le (p : K[X]) : (uni p).totalDegree ≤ p.natDegree := by
  classical
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum,map_mul,map_pow]
  apply totalDegree_finsetSum_le
  intro j hj
  simp only [uni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,Polynomial.eval₂_X]
  apply (totalDegree_mul _ _).trans
  apply (Nat.add_le_add (totalDegree_C _).le (totalDegree_pow _ _)).trans
  simp only [zero_add,totalDegree_X,Nat.mul_one]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)

lemma coeffP_natDegree_le (R : Matrix (ZMod d) (ZMod d) K[X]) (D : ℕ)
    (hR : ∀ i j, (R i j).natDegree ≤ D) (a b : ZMod d) :
    (coeffP χ R a b).natDegree ≤ D := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hR _ _)

lemma lift_totalDegree_le (R : Matrix (ZMod d) (ZMod d) K[X]) (D : ℕ)
    (hR : ∀ i j, (R i j).natDegree ≤ D) (i j : ZMod d) :
    (lift χ R i j).totalDegree ≤ D+2*(d-1) := by
  apply totalDegree_finsetSum_le
  intro a _
  apply totalDegree_finsetSum_le
  intro b _
  apply (totalDegree_mul _ _).trans
  apply (Nat.add_le_add (totalDegree_mul _ _) (totalDegree_pow _ _)).trans
  apply (Nat.add_le_add (Nat.add_le_add (totalDegree_mul _ _) (totalDegree_pow _ _)) le_rfl).trans
  simp only [totalDegree_C,totalDegree_X,Nat.mul_one,Nat.add_zero]
  have hh := (uni_totalDegree_le (coeffP χ R a b)).trans (coeffP_natDegree_le χ R D hR a b)
  have ha : a.val ≤ d-1 := Nat.le_sub_one_of_lt (ZMod.val_lt a)
  have hb : b.val ≤ d-1 := Nat.le_sub_one_of_lt (ZMod.val_lt b)
  omega

end
end RationalHitting.ThreeLift

namespace RationalHitting.PencilDeformation
open Matrix Polynomial MvPolynomial
open TestPolynomial LaurentReduction
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
variable {w q M N : ℕ} [NeZero M]

/-- The truncated polynomial test matrix, reindexed by cyclic indices. -/
def test (M N : ℕ) [NeZero M] (a : K) : Matrix (ZMod M) (ZMod M) K[X] :=
  (padded M N a).reindex (ZMod.finEquiv M).toEquiv (ZMod.finEquiv M).toEquiv

/-- Combine coefficient matrices with polynomial test blocks. -/
def polyBlocks (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    Matrix (Fin q) (Fin q) (Matrix (ZMod M) (ZMod M) K[X]) :=
  fun α β => ∑ i, A i α β • test M N (points i)

/-- The polynomial matrix obtained by applying the three-parameter lift. -/
def polynomial (χ : AddChar (ZMod M) K)
    (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    Matrix (Fin q × ZMod M) (Fin q × ZMod M) (MvPolynomial (Fin 3) K) :=
  fun a b => ThreeLift.lift χ (polyBlocks (M := M) (N := N) A points a.1 b.1) a.2 b.2

lemma specialize.{v_1, v_2} {K : Type v_1} {E : Type v_2} [Field K]
   [Field E]  {w q M N : ℕ} [NeZero M] (χ : AddChar (ZMod M) K)
  (φ : K →+* E) (t : E) (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
  (ThreeLift.specialize φ t).mapMatrix (polynomial (N := N) χ A points) =
    QuantumLift.blockPolynomial (φ.toMonoidHom.compAddChar χ)
      (fun α β => (Polynomial.eval₂RingHom φ t).mapMatrix
        (polyBlocks (M := M) (N := N) A points α β)) := by
  funext ⟨α,i⟩ ⟨β,j⟩
  exact congrFun (congrFun (ThreeLift.specialize_lift χ φ t (polyBlocks A points α β)) i) j

lemma raw_specialize.{v_1, v_2} {K : Type v_1} {E : Type v_2}
  [Field K]  [Field E]  {w q M N : ℕ} [NeZero M] (φ : K →+* E)
  (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
  QuantumLift.blockOriginal
      (fun α β => (Polynomial.eval₂RingHom ((HahnSeries.C : E →+* F E).comp φ)
        (HahnSeries.single 1 1)).mapMatrix (polyBlocks (M := M) (N := N) A points α β)) =
    (PaddedRank.raw (fun i => ((HahnSeries.C : E →+* F E).comp φ).mapMatrix (A i))
      (fun i => embed.mapMatrix (padded M N (φ (points i))))).reindex
        (Equiv.prodCongr (Equiv.refl (Fin q)) (ZMod.finEquiv M).toEquiv)
        (Equiv.prodCongr (Equiv.refl (Fin q)) (ZMod.finEquiv M).toEquiv) := by
  funext ⟨α,j⟩ ⟨β,k⟩
  simp only [QuantumLift.blockOriginal,polyBlocks,Matrix.sum_apply,Matrix.smul_apply,
    Polynomial.smul_eq_C_mul,RingHom.mapMatrix_apply,Matrix.map_apply,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,
    Polynomial.eval₂_C,Matrix.reindex_apply,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,Equiv.refl_symm,test]
  apply Finset.sum_congr rfl
  intro i _
  change ((HahnSeries.C : E →+* F E).comp φ) (A i α β) *
    (padded M N (points i) ((ZMod.finEquiv M).symm j) ((ZMod.finEquiv M).symm k)).eval₂
      ((HahnSeries.C : E →+* F E).comp φ) (HahnSeries.single 1 1) =
    ((HahnSeries.C : E →+* F E).comp φ) (A i α β) *
      embed (padded M N (φ (points i)) ((ZMod.finEquiv M).symm j) ((ZMod.finEquiv M).symm k))
  rw [eval₂_padded]

omit [CharZero K] in
/-- The three-variable determinant is nonzero. The witness can lie over an
extension field and is never an input to the generator. -/
theorem det_ne_zero (χ : AddChar (ZMod M) K) (hχ : χ.IsPrimitive)
    (φ : K →+* E) (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) K)
    (B e : ℕ) (hw : 1 ≤ w) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hN : 1 ≤ N) (hMN : M = N+2*w^3*B) (hM : B*(2*w^3*B) < M) (he : 0 < e)
    (X : Fin w → Matrix (Fin e) (Fin e) (F E))
    (hX : Function.Injective (Rectangular.blockEval
      (fun i => ((HahnSeries.C : E →+* F E).comp φ).mapMatrix (A i)) X)) :
    (polynomial (N := N) χ A points).det ≠ 0 := by
  let : CharZero (F E) := CharZero.of_addMonoidHom
    (HahnSeries.C : E →+* F E).toAddMonoidHom (map_one (HahnSeries.C : E →+* F E))
    HahnSeries.C_injective
  let ψ : K →+* F E := (HahnSeries.C : E →+* F E).comp φ
  let τ : F E := HahnSeries.single 1 1
  let A' := fun i => ψ.mapMatrix (A i)
  let W := fun α β => (Polynomial.eval₂RingHom ψ τ).mapMatrix (polyBlocks (M := M) (N := N) A
    points α β)
  have hr := PaddedRank.rank_ge w B M N q e hw hN hMN hqB he
    (fun i => φ (points i)) (φ.injective.comp hp) A' X hX
  have hr' : (q-1)*M < (QuantumLift.blockOriginal W).rank := by
    rw [show QuantumLift.blockOriginal W = _ from raw_specialize φ A points, Matrix.rank_reindex]
    exact (PaddedRank.numeric_gap w B M N q hq hqB hMN hM).trans_le hr
  have hχ' : (ψ.toMonoidHom.compAddChar χ).IsPrimitive :=
    hχ.compMulHom_of_isPrimitive ψ.injective
  have hd := QuantumLift.blockPolynomial_det_ne_zero (ψ.toMonoidHom.compAddChar χ) hχ' W
    (by simpa using hq) (by simpa using hr')
  intro hz
  have hm := congrArg (ThreeLift.specialize ψ τ) hz
  rw [map_zero, RingHom.map_det, specialize χ ψ τ] at hm
  exact hd hm

lemma polyBlocks_degree.{v_1} {K : Type v_1} [Field K]
  {w q M N : ℕ} [NeZero M] (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K)
  (α β : Fin q) (i j : ZMod M) :
  (polyBlocks (M := M) (N := N) A points α β i j).natDegree ≤ M - 1 := by
  simp only [polyBlocks,Matrix.sum_apply,Matrix.smul_apply,Polynomial.smul_eq_C_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact padded_natDegree_le M N (points r) _ _

omit [CharZero K] in
lemma entry_degree (χ : AddChar (ZMod M) K)
    (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K)
    (a b : Fin q × ZMod M) :
    (polynomial (N := N) χ A points a b).totalDegree ≤ 3*M := by
  have hh := ThreeLift.lift_totalDegree_le χ (polyBlocks (M := M) (N := N) A points a.1 b.1)
    (M-1) (polyBlocks_degree A points a.1 b.1) a.2 b.2
  exact hh.trans (by omega)
end
end RationalHitting.PencilDeformation


namespace RationalHitting.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

lemma coeffP_zero (a b : ZMod d) : coeffP χ 0 a b = 0 := by simp [coeffP]
lemma coeffP_add (R S : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    coeffP χ (R+S) a b = coeffP χ R a b + coeffP χ S a b := by
  simp [coeffP,mul_add,Finset.sum_add_distrib]
lemma coeffP_smul (c : K) (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    coeffP χ (c • R) a b = Polynomial.C c * coeffP χ R a b := by
  simp only [coeffP,Matrix.smul_apply,Polynomial.smul_eq_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma lift_zero : lift χ 0 = 0 := by
  funext i j
  simp [lift,coeffP_zero]
lemma lift_add (R S : Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (R+S) = lift χ R + lift χ S := by
  funext i j
  simp [lift,coeffP_add,map_add,add_mul,Finset.sum_add_distrib]
lemma lift_smul (c : K) (R : Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (c • R) = c • lift χ R := by
  funext i j
  simp only [lift,coeffP_smul,map_mul,uni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
    Matrix.smul_apply,MvPolynomial.smul_eq_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The original matrix pencil evaluated on the supplied blocks. -/
def linear : Matrix (ZMod d) (ZMod d) K[X] →ₗ[K]
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 3) K) where
  toFun := lift χ
  map_add' := lift_add χ
  map_smul' := by intro c R; simpa using lift_smul χ c R

lemma lift_sum {ι : Type*} (S : Finset ι) (R : ι → Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (∑ i ∈ S, R i) = ∑ i ∈ S, lift χ (R i) := map_sum (linear χ) R S
end
end RationalHitting.ThreeLift

end Complexity
