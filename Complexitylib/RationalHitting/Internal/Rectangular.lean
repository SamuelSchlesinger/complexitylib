/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.SmallExpansion

/-!
# Rational hitting lists: rectangular

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Rectangular.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.Rectangular
open Module Matrix
open scoped BigOperators Kronecker
noncomputable section
variable {F : Type*} [Field F]

/-- The ordinary Kronecker evaluation, with the two vector indices curried in
reverse order. This is only a coordinate convention. -/
def blockEval {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) :
    (Fin e → Fin q → F) →ₗ[F] (Fin e → Fin q → F) where
  toFun v β := ∑ i, ∑ δ, X i β δ • (A i).mulVec (v δ)
  map_add' v u := by
    funext β
    simp only [Pi.add_apply, Matrix.mulVec_add, smul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext β
    simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mulVec_smul,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro δ _
    rw [mul_comm]

lemma no_shrunk_subspace {w q e : ℕ} (he : 0 < e)
    (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F)
    (hX : Function.Injective (blockEval A X))
    (V W : Submodule F (Fin q → F))
    (hVW : ∀ i, V.map (A i).mulVecLin ≤ W) : finrank F V ≤ finrank F W := by
  let g : (Fin e → V) →ₗ[F] (Fin e → W) :=
    { toFun := fun v β => ⟨∑ i, ∑ δ, X i β δ • (A i).mulVec (v δ), by
        apply W.sum_mem
        intro i _
        apply W.sum_mem
        intro δ _
        exact W.smul_mem _ (hVW i ⟨v δ, (v δ).property, rfl⟩)⟩
      map_add' := by
        intro v u
        funext β
        apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply, Matrix.mulVec_add,
          smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        funext β
        apply Subtype.ext
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
          Matrix.mulVec_smul, Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro δ _
        rw [mul_comm] }
  have hg : Function.Injective g := by
    intro v u h
    have hh : blockEval A X (fun δ => (v δ : Fin q → F)) =
        blockEval A X (fun δ => (u δ : Fin q → F)) := by
      funext β
      exact congrArg Subtype.val (congrFun h β)
    have heq := hX hh
    funext δ
    exact Subtype.ext (congrFun heq δ)
  have hd := LinearMap.finrank_le_finrank_of_injective hg
  simp only [Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hd
  exact Nat.le_of_mul_le_mul_left hd he

/-- Full-rank blocks preserve the dimension of a common input subspace; this
form avoids any unwarranted specialization of Laurent-series coefficients. -/
lemma blockEval_injective_of_leftInverse {w q e : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F)
    (J : (Fin e → Fin q → F) →ₗ[F] (Fin e → Fin q → F))
    (hJ : J.comp (blockEval A X) = LinearMap.id) :
    Function.Injective (blockEval A X) := by
  apply Function.HasLeftInverse.injective
  exact ⟨J, fun v => DFunLike.congr_fun hJ v⟩


variable {P Q : Type*} [AddCommGroup P] [Module F P]
  [AddCommGroup Q] [Module F Q]

/-- The subspace spanned by the components of a vector. -/
def componentSpace {q : ℕ} (f : Fin q → P) : Submodule F P :=
  Submodule.span F (Set.range f)

/-- A component regarded as a vector in the component span. -/
def component {q : ℕ} (f : Fin q → P) (α : Fin q) : componentSpace (F := F) f :=
  ⟨f α, Submodule.subset_span ⟨α, rfl⟩⟩

/-- Coordinates of each component in a basis of their span. -/
def coefficientMatrix {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) : Matrix (Fin q) (Fin k) F :=
  fun α => b.equivFun (component (F := F) f α)

lemma span_component_top {q : ℕ} (f : Fin q → P) :
    Submodule.span F (Set.range (component (F := F) f)) = ⊤ := by
  apply Submodule.map_injective_of_injective (componentSpace (F := F) f).injective_subtype
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
  rfl

lemma rank_coefficientMatrix {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) : (coefficientMatrix f b).rank = k := by
  have hs : Submodule.span F (Set.range (coefficientMatrix f b)) = ⊤ := by
    have hh := congrArg (Submodule.map b.equivFun.toLinearMap) (span_component_top f)
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr b.equivFun.surjective] at hh
    exact hh
  rw [Matrix.rank_eq_finrank_span_row]
  change finrank F (Submodule.span F (Set.range (coefficientMatrix f b))) = k
  rw [hs]
  simp

lemma coefficientMatrix_expansion {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) (α : Fin q) :
    ∑ j, (coefficientMatrix f b) α j • (b j : P) = f α := by
  simpa only [coefficientMatrix, Basis.equivFun_apply, Submodule.coe_sum,
    Submodule.coe_smul, component] using congrArg Subtype.val (b.sum_repr (component (F := F) f α))

/-- The output map of the wk possible component images. -/
def imageCombination {w k : ℕ} (T : Fin w → P →ₗ[F] Q) (u : Fin k → P) :
    (Fin w × Fin k → F) →ₗ[F] Q :=
  Fintype.linearCombination F (fun ij => T ij.1 (u ij.2))

/-- The concatenated coefficient matrix. -/
def concatMatrix {w q k : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (P : Matrix (Fin q) (Fin k) F) : Matrix (Fin q) (Fin w × Fin k) F :=
  fun α ij => (A ij.1 * P) α ij.2

lemma concat_row_relation {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0) (α : Fin q) :
    (concatMatrix A (coefficientMatrix f b)).row α ∈
      (imageCombination T (fun j => (b j : P))).ker := by
  rw [LinearMap.mem_ker]
  change (∑ ij : Fin w × Fin k,
    (∑ γ, A ij.1 α γ * coefficientMatrix f b γ ij.2) • T ij.1 (b ij.2 : P)) = 0
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_smul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  simp_rw [mul_smul, ← Finset.smul_sum, ← map_smul, ← map_sum,
    coefficientMatrix_expansion]
  exact hker α

lemma rank_concat_lt {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0)
    (hex : (w-1)*k < finrank F (imageCombination T (fun j => (b j : P))).range)
    (hw : 1 ≤ w) : (concatMatrix A (coefficientMatrix f b)).rank < k := by
  let H := imageCombination T (fun j => (b j : P))
  have hle : Submodule.span F (Set.range (concatMatrix A (coefficientMatrix f b)).row) ≤
      H.ker := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact concat_row_relation A T f b hker α
  have hr := Submodule.finrank_mono hle
  rw [← Matrix.rank_eq_finrank_span_row] at hr
  have hd := H.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin] at hd
  have hw' : (w-1)*k+k = w*k := by
    calc
      _ = (w-1+1)*k := by ring
      _ = _ := by congr 1; omega
  change (w-1)*k < finrank F H.range at hex
  omega

lemma coefficient_image_le_concat {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (P : Matrix (Fin q) (Fin k) F) (i : Fin w) :
    (Submodule.span F (Set.range P.col)).map (A i).mulVecLin ≤
      Submodule.span F (Set.range (concatMatrix A P).col) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨v, ⟨j, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨(i,j), ?_⟩
  funext α
  simp [concatMatrix, Matrix.mulVec, Matrix.mul_apply, dotProduct]


lemma component_image_le_range {w q k : ℕ} (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f)) (i : Fin w) :
    (componentSpace (F := F) f).map (T i) ≤
      (imageCombination T (fun j => (b j : P))).range := by
  rw [imageCombination, Fintype.range_linearCombination]
  rintro _ ⟨x, hx, rfl⟩
  have he : (∑ j, (b.repr ⟨x,hx⟩) j • (b j : P)) = x := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (b.sum_repr ⟨x,hx⟩)
  rw [← he, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(i,j), rfl⟩

/-- A kernel vector with sufficiently expansive component span contradicts
any invertible block evaluation of the same coefficient matrices. -/
theorem kernel_impossible {w q k e : ℕ} (hw : 1 ≤ w) (he : 0 < e)
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (X : Fin w → Matrix (Fin e) (Fin e) F)
    (hX : Function.Injective (blockEval A X))
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0)
    (hex : (w-1)*k < finrank F (imageCombination T (fun j => (b j : P))).range) :
    False := by
  let Pmat := coefficientMatrix f b
  let Cmat := concatMatrix A Pmat
  let V := Submodule.span F (Set.range Pmat.col)
  let W := Submodule.span F (Set.range Cmat.col)
  have hVW : ∀ i, V.map (A i).mulVecLin ≤ W :=
    fun i => coefficient_image_le_concat A Pmat i
  have hd := no_shrunk_subspace he A X hX V W hVW
  have hV : finrank F V = k := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact rank_coefficientMatrix f b
  have hW : finrank F W < k := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact rank_concat_lt A T f b hker hex hw
  omega


/-- The block matrix obtained as a sum of Kronecker products. -/
def blockMatrix {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) :
    Matrix (Fin q × Fin e) (Fin q × Fin e) F := ∑ i, A i ⊗ₖ X i

lemma blockMatrix_mulVec {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) (v : Fin e → Fin q → F)
    (α : Fin q) (β : Fin e) :
    (blockMatrix A X).mulVec (fun j => v j.2 j.1) (α,β) = blockEval A X v β α := by
  classical
  simp only [blockMatrix, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.kronecker_apply, Finset.sum_mul, Fintype.sum_prod_type,
    blockEval, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext δ; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro γ _
  ring

lemma blockEval_injective_of_isUnit {w q e : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) (h : IsUnit (blockMatrix A X)) :
    Function.Injective (blockEval A X) := by
  have hh := Matrix.mulVec_injective_iff_isUnit.mpr h
  intro v u hv
  have hflat : (fun j : Fin q × Fin e => v j.2 j.1) = (fun j => u j.2 j.1) := by
    apply hh
    funext j
    rw [blockMatrix_mulVec, blockMatrix_mulVec]
    exact congrFun (congrFun hv j.2) j.1
  funext β α
  exact congrFun hflat (α,β)

end
end RationalHitting.Rectangular


namespace RationalHitting.RectangularExpansion
open Module Matrix
open scoped BigOperators
open LaurentReduction SmallExpansion Rectangular
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The rectangular Taylor tests have no nonzero kernel component family when
the same coefficients have an invertible matrix witness. -/
theorem rectangular_kernel_zero (w B M N q e : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2*w^3*B) (hq : q ≤ B) (he : 0 < e)
    (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (X : Fin w → Matrix (Fin e) (Fin e) (F K))
    (hX : Function.Injective (blockEval A X))
    (f : Fin q → Fin M → F K)
    (hf : ∀ α j, N ≤ j.val → f α j = 0)
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • testMap M (points i) (f γ) = 0) : f = 0 := by
  classical
  by_contra hn
  obtain ⟨α, hα⟩ : ∃ α, f α ≠ 0 := by
    by_contra! hh
    exact hn (funext hh)
  let U := componentSpace (F := F K) f
  let k := finrank (F K) U
  let b := Module.finBasis (F K) U
  let T := fun i => testMap M (points i)
  let W := (imageCombination T (fun j => (b j : Fin M → F K))).range
  have hk : 1 ≤ k := by
    apply finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨component (F := F K) f α, ?_⟩
    intro hz
    exact hα (congrArg Subtype.val hz)
  have hkq : k ≤ q := by
    simpa using finrank_le_of_span_eq_top (span_component_top (F := F K) f)
  have hU : ∀ x ∈ U, ∀ j : Fin M, N ≤ j.val → x j = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨α, rfl⟩ := hx; exact hf α
    | zero => intro j _; rfl
    | add x y _ _ hx hy => intro j hj; simp [hx j hj, hy j hj]
    | smul c x _ hx => intro j hj; simp [hx j hj]
  have hW : ∀ i, U.map (T i) ≤ W := fun i => component_image_le_range T f b i
  have hex := small_expansion w B M N hw hN hMN points hp U W hU hW hk (hkq.trans hq)
  exact kernel_impossible hw he A T X hX f b hker hex

end
end RationalHitting.RectangularExpansion

end Complexity
