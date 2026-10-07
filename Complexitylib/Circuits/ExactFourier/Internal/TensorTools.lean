/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.LinearDAG

/-!
# Exact Fourier circuits: tensor tools

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/TensorTools.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- Exact finite tensor and disjoint-block constructions for the triangular
monotonicity experiment in 05-corners:130–201. -/
namespace ExactFourier
open scoped Kronecker BigOperators
namespace TensorTools

variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

theorem unit_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (hA : IsUnit A) :
    IsUnit (Matrix.reindex e e A) :=
  hA.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom

theorem unit_tensor (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : IsUnit A) (hB : IsUnit B) : IsUnit (A ⊗ₖ B) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_kronecker]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA).pow _ |>.mul
    (((Matrix.isUnit_iff_isUnit_det _).mp hB).pow _)

/-- Exchange the middle and final summands while retaining the first block. -/
def middleEquiv : (ι ⊕ κ) ⊕ τ ≃ (ι ⊕ τ) ⊕ κ where
  toFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  left_inv := by rintro ((i|k)|t) <;> rfl
  right_inv := by rintro ((i|t)|k) <;> rfl

 theorem pad_middle
    {ι : Type} {κ : Type} {τ : Type}      [DecidableEq τ] (A : Matrix ι ι ℂ) (E : Matrix ι κ ℂ)
      (Y : Matrix κ κ ℂ) :
    Matrix.reindex (middleEquiv (τ := τ)) middleEquiv
      (Matrix.fromBlocks (Matrix.fromBlocks A E 0 Y) 0 0 (1 : Matrix τ τ ℂ)) =
    Matrix.fromBlocks (Matrix.fromBlocks A 0 0 (1 : Matrix τ τ ℂ))
      (Matrix.fromRows E 0) 0 Y := by
  ext i j
  rcases i with (i|t)|k <;> rcases j with (j|t')|k' <;>
    simp [Matrix.reindex_apply, middleEquiv, Matrix.fromBlocks, Matrix.fromRows, Sum.elim,
      Matrix.one_apply]

 theorem pad_front
    {ι : Type} {κ : Type} {τ : Type}    [DecidableEq ι]   (B : Matrix τ τ ℂ) (F : Matrix τ κ ℂ)
      (Z : Matrix κ κ ℂ) :
    Matrix.reindex (Equiv.sumAssoc ι τ κ).symm (Equiv.sumAssoc ι τ κ).symm
      (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (Matrix.fromBlocks B F 0 Z)) =
    Matrix.fromBlocks (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 B)
      (Matrix.fromRows 0 F) 0 Z := by
  ext i j
  rcases i with (i|t)|k <;> rcases j with (j|t')|k' <;>
    simp [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.fromRows, Sum.elim, Matrix.one_apply]

 theorem join_mul
    {ι : Type} {κ : Type} {τ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι]
      [DecidableEq τ] (A : Matrix ι ι ℂ) (B : Matrix τ τ ℂ)
    (E : Matrix ι κ ℂ) (F : Matrix τ κ ℂ) (Y Z : Matrix κ κ ℂ) :
    Matrix.fromBlocks (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 B)
        (Matrix.fromRows 0 F) 0 Z *
      Matrix.fromBlocks (Matrix.fromBlocks A 0 0 (1 : Matrix τ τ ℂ))
        (Matrix.fromRows E 0) 0 Y =
    Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B)
      (Matrix.fromRows E (F * Y)) 0 (Z * Y) := by
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext i j
  rcases i with i|t <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.fromRows, Sum.elim,
      Matrix.one_apply]

theorem price_join (p : MatrixPrice) (A : Matrix ι ι ℂ) (B : Matrix τ τ ℂ)
    (E : Matrix ι κ ℂ) (F : Matrix τ κ ℂ) (Y Z : Matrix κ κ ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (hY : IsUnit Y) (hZ : IsUnit Z) :
    p.value (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B)
      (Matrix.fromRows E (F * Y)) 0 (Z * Y)) ≤
      p.value (Matrix.fromBlocks A E 0 Y) + p.value (Matrix.fromBlocks B F 0 Z) := by
  have hT : IsUnit (Matrix.fromBlocks A E 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA,hY⟩
  have hU : IsUnit (Matrix.fromBlocks B F 0 Z) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hB,hZ⟩
  have hT' : IsUnit (Matrix.fromBlocks (Matrix.fromBlocks A E 0 Y) 0 0 (1 : Matrix τ τ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hT,isUnit_one⟩
  have hU' : IsUnit (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (Matrix.fromBlocks B F 0 Z)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,hU⟩
  rw [← join_mul, ← pad_middle, ← pad_front]
  calc
    _ ≤ _ := p.mul_le _ _ (unit_reindex _ _ hU') (unit_reindex _ _ hT')
    _ = _ := by
      rw [p.reindex _ _ hU', p.reindex _ _ hT',
        p.directSum _ _ isUnit_one hU, p.identity_pad _ hT, p.one]; ring

end TensorTools
end ExactFourier

end

section
/- Two cell programs sharing only their persistent state space. Unlike the
triangular experiment, no invertibility of the state block is assumed. -/
namespace ExactFourier
open TensorTools
namespace CellJoin
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Execute two cells with shared state and separate data blocks, retaining the final state. -/
abbrev join (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ) :
    Matrix ((α ⊕ γ) ⊕ β) ((α ⊕ γ) ⊕ β) ℂ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks X.toBlocks₁₁ 0 (Y.toBlocks₁₂ * X.toBlocks₂₁) Y.toBlocks₁₁)
    (Matrix.fromRows X.toBlocks₁₂ (Y.toBlocks₁₂ * X.toBlocks₂₂))
    (Matrix.fromCols (Y.toBlocks₂₂ * X.toBlocks₂₁) Y.toBlocks₂₁)
    (Y.toBlocks₂₂ * X.toBlocks₂₂)

theorem join_eq
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α]
      [DecidableEq γ] (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ) :
    join X Y =
    Matrix.reindex (Equiv.sumAssoc α γ β).symm (Equiv.sumAssoc α γ β).symm
        (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 Y) *
      Matrix.reindex (middleEquiv (ι := α) (κ := β) (τ := γ)) middleEquiv
        (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) := by
  have hX : Matrix.reindex (middleEquiv (ι := α) (κ := β) (τ := γ)) middleEquiv
      (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) =
      Matrix.fromBlocks (Matrix.fromBlocks X.toBlocks₁₁ 0 0 1)
        (Matrix.fromRows X.toBlocks₁₂ 0) (Matrix.fromCols X.toBlocks₂₁ 0) X.toBlocks₂₂ := by
    ext i j
    rcases i with (a|c)|b <;> rcases j with (a'|c')|b' <;>
      simp [Matrix.reindex_apply, middleEquiv, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  have hY : Matrix.reindex (Equiv.sumAssoc α γ β).symm (Equiv.sumAssoc α γ β).symm
        (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 Y) =
      Matrix.fromBlocks (Matrix.fromBlocks 1 0 0 Y.toBlocks₁₁)
        (Matrix.fromRows 0 Y.toBlocks₁₂) (Matrix.fromCols 0 Y.toBlocks₂₁) Y.toBlocks₂₂ := by
    ext i j
    rcases i with (a|c)|b <;> rcases j with (a'|c')|b' <;>
      simp [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [hX,hY]
  simp only [join, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with (a|c)|b <;> rcases j with (a'|c')|b' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.fromRows, Matrix.fromCols, Sum.elim, Matrix.one_apply]

theorem unit (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ)
    (hX : IsUnit X) (hY : IsUnit Y) : IsUnit (join X Y) := by
  rw [join_eq]
  exact (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,hY⟩)).mul
    (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩))

theorem price (p : MatrixPrice) (X : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ) (hX : IsUnit X) (hY : IsUnit Y) :
    p.value (join X Y) ≤ p.value X + p.value Y := by
  have hX' : IsUnit (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩
  have hY' : IsUnit (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,hY⟩
  rw [join_eq]
  calc
    _ ≤ _ := p.mul_le _ _ (unit_reindex _ _ hY') (unit_reindex _ _ hX')
    _ = _ := by
      rw [p.reindex _ _ hY',p.reindex _ _ hX',
        p.directSum _ _ isUnit_one hY,p.identity_pad _ hX,p.one]; ring

end CellJoin
end ExactFourier

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools

variable {α β σ κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ]

/-- Exchange the last two factors of a three-coordinate product. -/
def swapLast : (σ × α) × β ≃ (σ × β) × α where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv := by rintro ⟨⟨s,a⟩,b⟩; rfl
  right_inv := by rintro ⟨⟨s,b⟩,a⟩; rfl

/-- Distribute a tensor lift across the triangular data and state blocks. -/
def liftEquiv : ((σ × α) ⊕ κ) × β ≃ ((σ × β) × α) ⊕ (κ × β) :=
  (Equiv.sumProdDistrib _ _ _).trans (Equiv.sumCongr swapLast (Equiv.refl _))

 /-- Lift the previous off-diagonal contribution with an identity on the new tensor factor. -/
 def oldE (E : Matrix (σ × α) κ ℂ) : Matrix ((σ × β) × α) (κ × β) ℂ :=
   fun i j => E (i.1.1,i.2) j.1 * (1 : Matrix β β ℂ) i.1.2 j.2

 theorem lift_identity
    {α : Type} {β : Type} {σ : Type} {κ : Type}      [DecidableEq β] [DecidableEq σ]  (M :
      Matrix α α ℂ) (E : Matrix (σ × α) κ ℂ)
    (Y : Matrix κ κ ℂ) :
    Matrix.reindex liftEquiv liftEquiv
      (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y ⊗ₖ (1 : Matrix β β ℂ)) =
    Matrix.fromBlocks ((1 : Matrix (σ × β) (σ × β) ℂ) ⊗ₖ M) (oldE E) 0
      (Y ⊗ₖ (1 : Matrix β β ℂ)) := by
   ext i j
   rcases i with ⟨⟨s,b⟩,a⟩|⟨i,b⟩ <;> rcases j with ⟨⟨s',b'⟩,a'⟩|⟨j,b'⟩ <;>
     simp [Matrix.reindex_apply, liftEquiv, swapLast, Matrix.kroneckerMap_apply,
       Matrix.fromBlocks, oldE, Matrix.one_apply, mul_comm,        Prod.mk.injEq, and_comm]
   split_ifs <;> simp_all

 theorem new_identity
    {α : Type} {β : Type} {κ : Type}      [DecidableEq κ] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
      (D : Matrix β β ℂ) :
    Matrix.reindex (Equiv.prodSumDistrib κ α β) (Equiv.prodSumDistrib κ α β)
      ((1 : Matrix κ κ ℂ) ⊗ₖ Matrix.fromBlocks M C 0 D) =
    Matrix.fromBlocks ((1 : Matrix κ κ ℂ) ⊗ₖ M) ((1 : Matrix κ κ ℂ) ⊗ₖ C) 0
      ((1 : Matrix κ κ ℂ) ⊗ₖ D) := by
  ext i j
  rcases i with ⟨i,a⟩|⟨i,b⟩ <;> rcases j with ⟨j,a'⟩|⟨j,b'⟩ <;>
    simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.fromBlocks]

 /-- Combine the old lifted contribution with the new coupling contribution. -/
 def nextE (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ) (C : Matrix α β ℂ) :
    Matrix (((σ × β) ⊕ κ) × α) (κ × β) ℂ :=
    fun i j => match i.1 with
    | Sum.inl s => E (s.1,i.2) j.1 * (1 : Matrix β β ℂ) s.2 j.2
    | Sum.inr k => Y k j.1 * C i.2 j.2

/-- Merge the old and new call coordinates into one product block. -/
def mergeEquiv : (((σ × β) × α) ⊕ (κ × α)) ⊕ (κ × β) ≃
    (((σ × β) ⊕ κ) × α) ⊕ (κ × β) :=
  Equiv.sumCongr (Equiv.sumProdDistrib (σ × β) κ α).symm (Equiv.refl _)

 theorem merge_identity
    {α : Type} {β : Type} {σ : Type} {κ : Type}  [Fintype β]  [Fintype κ]  [DecidableEq β]
      [DecidableEq σ] [DecidableEq κ] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (D : Matrix β β ℂ)
    (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ) :
    Matrix.reindex mergeEquiv mergeEquiv
      (Matrix.fromBlocks
        (Matrix.fromBlocks ((1 : Matrix (σ × β) (σ × β) ℂ) ⊗ₖ M) 0 0
          ((1 : Matrix κ κ ℂ) ⊗ₖ M))
        (Matrix.fromRows (oldE E) (((1 : Matrix κ κ ℂ) ⊗ₖ C) *
          (Y ⊗ₖ (1 : Matrix β β ℂ)))) 0
        (((1 : Matrix κ κ ℂ) ⊗ₖ D) * (Y ⊗ₖ (1 : Matrix β β ℂ)))) =
    Matrix.fromBlocks ((1 : Matrix ((σ × β) ⊕ κ) ((σ × β) ⊕ κ) ℂ) ⊗ₖ M)
      (nextE E Y C) 0 (Y ⊗ₖ D) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with ⟨s|k,a⟩|⟨i,b⟩ <;> rcases j with ⟨s'|k',a'⟩|⟨j,b'⟩ <;>
    simp [Matrix.reindex_apply, mergeEquiv, Matrix.kroneckerMap_apply,
      Matrix.fromBlocks, Matrix.fromRows, Sum.elim, oldE, nextE, Matrix.one_apply]

 theorem next_price (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ)
    (hM : IsUnit M) (hD : IsUnit D) (hY : IsUnit Y) :
    p.value (Matrix.fromBlocks ((1 : Matrix ((σ × β) ⊕ κ) ((σ × β) ⊕ κ) ℂ) ⊗ₖ M)
       (nextE E Y C) 0 (Y ⊗ₖ D)) ≤
      Fintype.card β * p.value (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) +
      Fintype.card κ * p.value (Matrix.fromBlocks M C 0 D) := by
  have hT : IsUnit (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ isUnit_one hM,hY⟩
  have hK : IsUnit (Matrix.fromBlocks M C 0 D) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,hD⟩
  have hh := price_join p ((1 : Matrix (σ × β) (σ × β) ℂ) ⊗ₖ M)
    ((1 : Matrix κ κ ℂ) ⊗ₖ M) (oldE E) ((1 : Matrix κ κ ℂ) ⊗ₖ C)
    (Y ⊗ₖ (1 : Matrix β β ℂ)) ((1 : Matrix κ κ ℂ) ⊗ₖ D)
    (unit_tensor _ _ isUnit_one hM) (unit_tensor _ _ isUnit_one hM)
    (unit_tensor _ _ hY isUnit_one) (unit_tensor _ _ isUnit_one hD)
  rw [← lift_identity, ← new_identity] at hh
  rw [p.reindex _ _ (unit_tensor _ _ hT isUnit_one),
    p.reindex _ _ (unit_tensor _ _ isUnit_one hK),
    p.tensor _ _ hT isUnit_one, p.tensor _ _ isUnit_one hK, p.one, p.one] at hh
  simp only [mul_zero, add_zero, zero_add] at hh
  rw [← merge_identity, p.reindex]
  · exact hh
  · apply Matrix.isUnit_fromBlocks_zero₂₁.mpr
    constructor
    · exact Matrix.isUnit_fromBlocks_zero₂₁.mpr
        ⟨unit_tensor _ _ isUnit_one hM, unit_tensor _ _ isUnit_one hM⟩
    · exact (unit_tensor _ _ isUnit_one hD).mul (unit_tensor _ _ hY isUnit_one)

end ExactFourier.Triangular

end

section
/- Whole-row-block compression used in the proof of triangular monotonicity
(05-corners.tex:145–209). Only the block-copy index is changed; individual rows
of a spatial block are never independently mixed. -/
namespace ExactFourier.RowCompression
open scoped BigOperators

section Splitting
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- A chosen linear right inverse splits a surjection with its kernel. -/
def splitEquiv (f : E →ₗ[K] F) (s : F →ₗ[K] E)
    (hs : f.comp s = LinearMap.id) : E ≃ₗ[K] F × LinearMap.ker f where
  toFun x := (f x, ⟨x-s (f x), by
    change f (x-s (f x)) = 0
    have h := LinearMap.congr_fun hs (f x)
    simpa using sub_eq_zero.mpr h.symm⟩)
  invFun x := s x.1 + x.2
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · have h : f (s x.1) = x.1 := LinearMap.congr_fun hs x.1
      have hx : f (x.2 : E) = 0 := x.2.property
      simp only [map_add, h, hx, add_zero]
    · apply Subtype.ext
      have h : f (s x.1) = x.1 := LinearMap.congr_fun hs x.1
      have hx : f (x.2 : E) = 0 := x.2.property
      simp only [map_add, h, hx, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · exact map_add f x y
    · apply Subtype.ext
      simp only [Prod.snd_add, Submodule.coe_add, map_add]
      abel
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul f c x
    · apply Subtype.ext
      simp [smul_sub]

@[simp] theorem splitEquiv_fst (f : E →ₗ[K] F) (s : F →ₗ[K] E)
    (hs : f.comp s = LinearMap.id) (x : E) : (splitEquiv f s hs x).1 = f x := rfl

/-- Two surjections from the same finite-dimensional domain differ by an
invertible change of domain. This is the block-copy coordinate change V. -/
theorem surjective_equiv [FiniteDimensional K E] (f g : E →ₗ[K] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ e : E ≃ₗ[K] E, ∀ x, f (e x) = g x := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  obtain ⟨t, ht⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  have hd : Module.finrank K (LinearMap.ker g) = Module.finrank K (LinearMap.ker f) := by
    have h1 := f.finrank_range_add_finrank_ker
    have h2 := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hf] at h1
    rw [LinearMap.range_eq_top.mpr hg] at h2
    omega
  let a : LinearMap.ker g ≃ₗ[K] LinearMap.ker f := LinearEquiv.ofFinrankEq _ _ hd
  let e := (splitEquiv g t ht).trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl K F) a).trans (splitEquiv f s hs).symm)
  refine ⟨e, ?_⟩
  intro x
  have h := congrArg Prod.fst ((splitEquiv f s hs).apply_symm_apply
    (g x, a (splitEquiv g t ht x).2))
  exact h

/-- Equality of row spaces, not an assumption of full row rank, suffices. -/
theorem range_equiv [FiniteDimensional K E] (f g : E →ₗ[K] F)
    (hfg : LinearMap.range f = LinearMap.range g) :
    ∃ e : E ≃ₗ[K] E, ∀ x, f (e x) = g x := by
  let g' : E →ₗ[K] LinearMap.range f := g.codRestrict (LinearMap.range f)
    (by intro x; rw [hfg]; exact LinearMap.mem_range_self g x)
  have hg' : Function.Surjective g' := by
    rintro ⟨y, hy⟩
    rw [hfg] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  obtain ⟨e, he⟩ := surjective_equiv f.rangeRestrict g'
    (LinearMap.range_eq_top.mp f.range_rangeRestrict) hg'
  exact ⟨e, fun x => congrArg Subtype.val (he x)⟩

end Splitting
section Matrices
variable {K α β : Type*} [Field K] [Fintype α] [DecidableEq α]

/-- The row-space equivalence as an actual invertible left multiplier. -/
theorem matrix_row_equiv (R S : Matrix α β K)
    (hRS : Submodule.span K (Set.range R) = Submodule.span K (Set.range S)) :
    ∃ V : Matrix α α K, IsUnit V ∧ V * R = S := by
  obtain ⟨e, he⟩ := range_equiv R.vecMulLinear S.vecMulLinear
    (by simpa only [range_vecMulLinear, Matrix.row] using hRS)
  let V := e.toLinearMap.toMatrixRight'
  let W := e.symm.toLinearMap.toMatrixRight'
  have hVW : V * W = 1 := by
    rw [← LinearMap.toMatrixRight'_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
    rw [h, LinearMap.toMatrixRight'_id]
  have hWV : W * V = 1 := by
    rw [← LinearMap.toMatrixRight'_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; simp
    rw [h, LinearMap.toMatrixRight'_id]
  refine ⟨V, ⟨⟨V, W, hVW, hWV⟩, rfl⟩, ?_⟩
  apply Matrix.toLinearMapRight'.injective
  rw [Matrix.toLinearMapRight'_mul]
  change R.vecMulLinear.comp (LinearMap.toMatrixRight'.symm
      (LinearMap.toMatrixRight' e.toLinearMap)) = S.vecMulLinear
  rw [LinearEquiv.symm_apply_apply]
  exact LinearMap.ext he

/-- Select a sparse spanning-family basis and perform the invertible compression
on the *whole* row-block index. At most dim(β → K) rows remain. -/
theorem sparse_row_compression {γ : Type*} [Fintype β] (R : Matrix α β K)
    (Q : γ → β → K)
    (hspan : Submodule.span K (Set.range R) = Submodule.span K (Set.range Q)) :
    ∃ V : Matrix α α K, IsUnit V ∧ ∃ I : Finset α,
      I.card ≤ Fintype.card β ∧
      (∀ i, i ∉ I → (V*R) i = 0) ∧
      (∀ i ∈ I, ∃ g, (V*R) i = Q g) := by
  classical
  obtain ⟨t, htQ, htcard, htspan, hti⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn K (Set.range Q)
  have hta : Fintype.card t ≤ Fintype.card α := by
    rw [Fintype.card_coe, htcard, ← hspan]
    exact finrank_range_le_card R
  have htb : t.card ≤ Fintype.card β := by
    rw [htcard]
    simpa using (Submodule.finrank_le (Submodule.span K (Set.range Q)))
  let e : t ↪ α := Classical.choice (Function.Embedding.nonempty_of_card_le hta)
  let S : Matrix α β K := fun i => if h : ∃ b : t, e b = i then (h.choose : β → K) else 0
  have hSe (b : t) : S (e b) = b := by
    dsimp only [S]
    have hb : ∃ c : t, e c = e b := ⟨b,rfl⟩
    rw [dite_eq_left hb]
    exact congrArg Subtype.val (e.injective hb.choose_spec)
  have hspanS : Submodule.span K (Set.range S) = Submodule.span K (t : Set (β → K)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      dsimp only [S]
      split_ifs with hi
      · exact Submodule.subset_span hi.choose.property
      · exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      intro b hb
      exact Submodule.subset_span ⟨e ⟨b,hb⟩, hSe ⟨b,hb⟩⟩
  have hRS : Submodule.span K (Set.range R) = Submodule.span K (Set.range S) := by
    rw [hspanS, htspan, hspan]
  obtain ⟨V,hV,hVS⟩ := matrix_row_equiv R S hRS
  let I := Finset.univ.map e
  refine ⟨V,hV,I, ?_, ?_, ?_⟩
  · simpa [I] using htb
  · intro i hi
    rw [hVS]

    dsimp [S]
    apply dite_eq_right
    simpa [I] using hi
  · intro i hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hi
    have hbQ := htQ b.property
    obtain ⟨g,hg⟩ := hbQ
    refine ⟨g, ?_⟩
    rw [hVS, hSe, hg]

end Matrices
end ExactFourier.RowCompression

end

end Complexity
