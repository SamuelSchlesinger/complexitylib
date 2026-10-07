/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PivotAlgebra

/-!
# Exact Fourier circuits: pivot join

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PivotJoin.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier.Pivot
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Apply the pivot transform to the four blocks of a square matrix on a sum type. -/
noncomputable def ofMatrix (K : Matrix (α⊕β) (α⊕β) ℂ) :=
  matrix K.toBlocks₁₁ K.toBlocks₁₂ K.toBlocks₂₁ K.toBlocks₂₂

@[simp] theorem of_fromBlocks
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    ofMatrix (Matrix.fromBlocks A C B D)=matrix A C B D := rfl

/-- Join cells in reverse order and restore the original order of their data blocks. -/
noncomputable def reverseJoin (X : Matrix (α⊕β) (α⊕β) ℂ)
    (Y : Matrix (γ⊕β) (γ⊕β) ℂ) : Matrix ((α⊕γ)⊕β) ((α⊕γ)⊕β) ℂ :=
  Matrix.reindex (Equiv.sumCongr (Equiv.sumComm γ α) (Equiv.refl β))
    (Equiv.sumCongr (Equiv.sumComm γ α) (Equiv.refl β)) (CellJoin.join Y X)

theorem reverseJoin_eq
    {α : Type} {β : Type} {γ : Type}  [Fintype β]     (X : Matrix (α⊕β) (α⊕β) ℂ)
    (Y : Matrix (γ⊕β) (γ⊕β) ℂ) :
    reverseJoin X Y=Matrix.fromBlocks
      (Matrix.fromBlocks X.toBlocks₁₁ (X.toBlocks₁₂*Y.toBlocks₂₁) 0 Y.toBlocks₁₁)
      (Matrix.fromRows (X.toBlocks₁₂*Y.toBlocks₂₂) Y.toBlocks₁₂)
      (Matrix.fromCols X.toBlocks₂₁ (X.toBlocks₂₂*Y.toBlocks₂₁))
      (X.toBlocks₂₂*Y.toBlocks₂₂) := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;> rfl

omit [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ] in
theorem of_join (X : Matrix (α⊕β) (α⊕β) ℂ)
    (Y : Matrix (γ⊕β) (γ⊕β) ℂ)
    (hD : IsUnit X.toBlocks₂₂) (hH : IsUnit Y.toBlocks₂₂) :
    ofMatrix (CellJoin.join X Y)=reverseJoin (ofMatrix X) (ofMatrix Y) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hD
  have hh := (Matrix.isUnit_iff_isUnit_det _).mp hH
  rw [reverseJoin_eq]
  simp only [ofMatrix,CellJoin.join,matrix,Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₁₂,Matrix.toBlocks_fromBlocks₂₁,Matrix.toBlocks_fromBlocks₂₂,
    Matrix.mul_inv_rev,Matrix.fromRows_mul,Matrix.mul_fromCols]
  have h1 : X.toBlocks₂₂ * X.toBlocks₂₂⁻¹=1 := Matrix.mul_nonsing_inv _ hd
  have h2 : Y.toBlocks₂₂⁻¹ * Y.toBlocks₂₂=1 := Matrix.nonsing_inv_mul _ hh
  have h3 (W : Matrix β α ℂ) : Y.toBlocks₂₂⁻¹*(Y.toBlocks₂₂*W)=W :=
    Matrix.nonsing_inv_mul_cancel_left _ _ hh
  have h4 {τ : Type} (W : Matrix β τ ℂ) : X.toBlocks₂₂*(X.toBlocks₂₂⁻¹*W)=W := by
    rw [← Matrix.mul_assoc,h1,Matrix.one_mul]
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [Matrix.fromBlocks,Matrix.fromRows,Matrix.fromCols,Sum.elim,
      Matrix.sub_apply,Matrix.neg_apply,
      Matrix.mul_assoc,h3,h4,
      Matrix.mul_neg,Matrix.neg_mul]

end ExactFourier.Pivot

end

section
namespace ExactFourier.CellJoin
variable {α γ : Type} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]

theorem scalar_price (p : MatrixPrice) (X : Matrix (α⊕PUnit) (α⊕PUnit) ℂ)
    (Y : Matrix (γ⊕PUnit) (γ⊕PUnit) ℂ) (hX : IsUnit X) (hY : IsUnit Y) :
    p.value (join X Y)=p.value X+p.value Y := by
  let e := Equiv.sumComm γ PUnit
  let Y' := Matrix.reindex e e Y
  have hu : IsUnit Y' := TensorTools.unit_reindex e Y hY
  have he : Matrix.reindex (TensorTools.middleEquiv (ι := α) (κ := PUnit) (τ := γ))
      TensorTools.middleEquiv (OnePort.product X Y')=join X Y := by
    rw [OnePort.product,Reindexed.mul,join_eq]
    congr 1
    ext i j
    rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
      simp [OnePort.unionSecond,Y',e,TensorTools.middleEquiv,Matrix.reindex_apply,
        Matrix.fromBlocks,Sum.elim,Matrix.one_apply]
  rw [← he,p.reindex _ _ (OnePort.product_isUnit X Y' hX hu),OnePort.price p X Y' hX hu,
    p.reindex e Y hY]

end ExactFourier.CellJoin

end

section
namespace ExactFourier.Pivot
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem of_unit (K : Matrix (α⊕β) (α⊕β) ℂ)
    (hA : IsUnit K.toBlocks₁₁) (hD : IsUnit K.toBlocks₂₂) : IsUnit (ofMatrix K) :=
  unit _ _ _ _ hA hD

theorem of_reindex_data
    {α : Type} {β : Type} {γ : Type}  [Fintype β]   [DecidableEq β]  (e : α≃γ) (K : Matrix (α⊕β)
      (α⊕β) ℂ) :
    ofMatrix (Matrix.reindex (Equiv.sumCongr e (Equiv.refl β))
      (Equiv.sumCongr e (Equiv.refl β)) K)=
      Matrix.reindex (Equiv.sumCongr e (Equiv.refl β))
        (Equiv.sumCongr e (Equiv.refl β)) (ofMatrix K) := by
  ext i j
  cases i <;> cases j <;> rfl

omit [Fintype α] in
@[simp] theorem of_one : ofMatrix (1 : Matrix (α⊕β) (α⊕β) ℂ)=1 := by
  have he : (1 : Matrix (α⊕β) (α⊕β) ℂ)=Matrix.fromBlocks 1 0 0 1 := by
    ext i j; cases i <;> cases j <;> simp [Matrix.one_apply,Matrix.fromBlocks]
  rw [he,of_fromBlocks]
  simp [matrix]

theorem run_block_units (K : Matrix (α⊕β) (α⊕β) ℂ)
    (hA : IsUnit K.toBlocks₁₁) (hD : IsUnit K.toBlocks₂₂) (t : ℕ) :
    IsUnit (CellStream.run K t).toBlocks₁₁ ∧ IsUnit (CellStream.run K t).toBlocks₂₂ := by
  induction t with
  | zero =>
    have h1 : (CellStream.run K 0).toBlocks₁₁=1 := by ext i; exact Fin.elim0 i.1
    have h2 : (CellStream.run K 0).toBlocks₂₂=1 := by
      ext i j; simp [CellStream.run,Matrix.toBlocks₂₂,Matrix.one_apply]
    rw [h1,h2]; exact ⟨isUnit_one,isUnit_one⟩
  | succ t ih =>
    have h1 : (CellStream.run K (t+1)).toBlocks₁₁=
        Matrix.reindex (timeSplit t α).symm (timeSplit t α).symm
          (CellJoin.join K (CellStream.run K t)).toBlocks₁₁ := rfl
    have h2 : (CellStream.run K (t+1)).toBlocks₂₂=
        (CellStream.run K t).toBlocks₂₂*K.toBlocks₂₂ := rfl
    rw [h1,h2]
    exact ⟨TensorTools.unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA,ih.1⟩),ih.2.mul hD⟩

theorem reverseJoin_scalar_price (p : MatrixPrice) (X : Matrix (α⊕PUnit) (α⊕PUnit) ℂ)
    (Y : Matrix (γ⊕PUnit) (γ⊕PUnit) ℂ) (hX : IsUnit X) (hY : IsUnit Y) :
    p.value (reverseJoin X Y)=p.value X+p.value Y := by
  rw [reverseJoin,p.reindex _ _ (CellJoin.unit Y X hY hX),CellJoin.scalar_price p Y X hY hX,
    add_comm]

theorem run_scalar_price (p : MatrixPrice) (K : Matrix (α⊕PUnit) (α⊕PUnit) ℂ)
    (hK : IsUnit K) (t : ℕ) : p.value (CellStream.run K t)=(t : ℝ)*p.value K := by
  induction t with
  | zero => simp [CellStream.run,p.one]
  | succ t ih =>
    rw [CellStream.run,p.reindex _ _ (CellJoin.unit K _ hK (CellStream.unit K hK t)),
      CellJoin.scalar_price p K _ hK (CellStream.unit K hK t),ih]
    push_cast; ring

theorem run_pivot_price (p : MatrixPrice) (K : Matrix (α⊕PUnit) (α⊕PUnit) ℂ)
    (hA : IsUnit K.toBlocks₁₁) (hD : IsUnit K.toBlocks₂₂) (t : ℕ) :
    p.value (ofMatrix (CellStream.run K t))=(t : ℝ)*p.value (ofMatrix K) := by
  induction t with
  | zero => simp [CellStream.run,p.one]
  | succ t ih =>
    have hb := run_block_units K hA hD t
    have hJ : IsUnit (ofMatrix (CellJoin.join K (CellStream.run K t))) :=
      of_unit _ (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA,hb.1⟩) (hb.2.mul hD)
    rw [CellStream.run,of_reindex_data,p.reindex _ _ hJ,of_join K _ hD hb.2,
      reverseJoin_scalar_price p _ _ (of_unit K hA hD) (of_unit _ hb.1 hb.2),ih]
    push_cast; ring

end ExactFourier.Pivot

namespace ExactFourier.MatrixPrice
variable {α : Type} [Fintype α] [DecidableEq α]

theorem scalar_pivot_le (p : MatrixPrice) (A : Matrix α α ℂ)
    (C : Matrix α PUnit ℂ) (B : Matrix PUnit α ℂ) (D : Matrix PUnit PUnit ℂ)
    (hA : IsUnit A) (hD : IsUnit D) (hK : IsUnit (Matrix.fromBlocks A C B D)) :
    p.value (Pivot.matrix A C B D)≤p.value (Matrix.fromBlocks A C B D) := by
  let K := Matrix.fromBlocks A C B D
  have h (t : ℕ) : (t : ℝ)*(p.value (Pivot.matrix A C B D)-p.value K)≤4 := by
    have hb := Pivot.run_block_units K hA hD t
    have H := p.pivot_bound (CellStream.run K t).toBlocks₁₁
      (CellStream.run K t).toBlocks₁₂ (CellStream.run K t).toBlocks₂₁
      (CellStream.run K t).toBlocks₂₂ hb.1 hb.2
      (by rw [Matrix.fromBlocks_toBlocks]; exact CellStream.unit K hK t)
    rw [Matrix.fromBlocks_toBlocks] at H
    change p.value (Pivot.ofMatrix (CellStream.run K t)) ≤ _ at H
    rw [Pivot.run_pivot_price p K hA hD t,Pivot.run_scalar_price p K hK t] at H
    simp only [Fintype.card_punit,Nat.cast_one,mul_one] at H
    change (t:ℝ)*p.value (Pivot.matrix A C B D)≤(t:ℝ)*p.value K+4 at H
    linarith
  by_contra hh
  have hd : 0<p.value (Pivot.matrix A C B D)-p.value K := sub_pos.mpr (lt_of_not_ge hh)
  obtain ⟨t,ht⟩ := exists_nat_gt (4/(p.value (Pivot.matrix A C B D)-p.value K))
  have ht' := (div_lt_iff₀ hd).mp ht
  linarith [h t]

/-- Exact scalar pivot invariance, 07-pivots:175--240. The proof uses finite
single-port chains; its constant four is amortized without any continuity law. -/
theorem scalar_pivot (p : MatrixPrice) (A : Matrix α α ℂ)
    (C : Matrix α PUnit ℂ) (B : Matrix PUnit α ℂ) (D : Matrix PUnit PUnit ℂ)
    (hA : IsUnit A) (hD : IsUnit D) (hK : IsUnit (Matrix.fromBlocks A C B D)) :
    p.value (Pivot.matrix A C B D)=p.value (Matrix.fromBlocks A C B D) := by
  apply le_antisymm (p.scalar_pivot_le A C B D hA hD hK)
  have hh := p.scalar_pivot_le (A-C*D⁻¹*B) (C*D⁻¹) (-D⁻¹*B) D⁻¹
    (Pivot.schur_unit A C B D hD hK) (Matrix.isUnit_nonsing_inv_iff.mpr hD)
    (Pivot.unit A C B D hA hD)
  rwa [Pivot.involutive A C B D hD] at hh

end ExactFourier.MatrixPrice

end

section
namespace ExactFourier
namespace BasisExchange
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Take the data rows from `U` and the selected-coordinate row from `V`. -/
noncomputable def mix (U V : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    Matrix (α⊕PUnit) (α⊕PUnit) ℂ :=
  Matrix.fromBlocks U.toBlocks₁₁ U.toBlocks₁₂ V.toBlocks₂₁ V.toBlocks₂₂

theorem mix_mul
    {α : Type} [Fintype α]  (U V W : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    mix U V*W=mix (U*W) (V*W) := by
  ext i j
  cases i <;> cases j <;>
    simp [mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,Matrix.mul_apply,Fintype.sum_sum_type,Sum.elim]

theorem mix_one_left
    {α : Type}  [DecidableEq α] (T : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    mix 1 T=Matrix.fromBlocks 1 0 T.toBlocks₂₁ T.toBlocks₂₂ := by
  ext i j; cases i <;> cases j <;> simp [mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,Matrix.one_apply]

theorem mix_one_right
    {α : Type}  [DecidableEq α] (T : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    mix T 1=Matrix.fromBlocks T.toBlocks₁₁ T.toBlocks₁₂ 0 1 := by
  ext i j; cases i <;> cases j <;> simp [mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂]

theorem price_split (p : MatrixPrice) (U V : Matrix (α⊕PUnit) (α⊕PUnit) ℂ)
    (hU : IsUnit U) (hV : IsUnit V) (hU' : IsUnit (mix U V)) (hV' : IsUnit (mix V U)) :
    p.value (mix V U*(mix U V)⁻¹)=p.value (V*U⁻¹) := by
  let T := V*U⁻¹
  have hi := Matrix.isUnit_nonsing_inv_iff.mpr hU
  have hT : IsUnit T := hV.mul hi
  have hUinv := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hrel : T*U=V := Matrix.nonsing_inv_mul_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det
    _).mp hU)
  have hL : mix U V*U⁻¹=mix 1 T := by rw [mix_mul,hUinv]
  have hR : mix V U*U⁻¹=mix T 1 := by rw [mix_mul,hUinv]
  have huL : IsUnit (mix 1 T) := by rw [← hL]; exact hU'.mul hi
  have huR : IsUnit (mix T 1) := by rw [← hR]; exact hV'.mul hi
  rw [mix_one_left] at huL
  rw [mix_one_right] at huR
  have hD := (Matrix.isUnit_fromBlocks_zero₁₂.mp huL).2
  have hA := (Matrix.isUnit_fromBlocks_zero₂₁.mp huR).1
  have hP : Pivot.ofMatrix T*(mix U V)=mix V U := by
    have hl : mix U V=mix 1 T*U := by rw [mix_mul,Matrix.one_mul,hrel]
    have hr : mix V U=mix T 1*U := by rw [mix_mul,Matrix.one_mul,hrel]
    rw [hl,hr,← Matrix.mul_assoc,mix_one_left,mix_one_right]
    rw [Pivot.ofMatrix,Pivot.solve _ _ _ _ hD]
  have he : mix V U*(mix U V)⁻¹=Pivot.ofMatrix T := by
    rw [← hP,Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU')]
  rw [he]
  exact p.scalar_pivot T.toBlocks₁₁ T.toBlocks₁₂ T.toBlocks₂₁ T.toBlocks₂₂ hA hD
    (by rwa [Matrix.fromBlocks_toBlocks]) |>.trans (by rw [Matrix.fromBlocks_toBlocks])

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Split one selected coordinate from the complement of that coordinate. -/
def isolate (i : ι) : ι≃{j : ι // j≠i}⊕PUnit where
  toFun j := if h : j=i then Sum.inr PUnit.unit else Sum.inl ⟨j,h⟩
  invFun := Sum.elim Subtype.val (fun _ => i)
  left_inv j := by by_cases h : j=i <;> simp [h]
  right_inv j := by rcases j with ⟨j,h⟩|⟨⟩ <;> simp [*]

theorem update_isolate
    {ι : Type}  [DecidableEq ι] (U V : Matrix ι ι ℂ) (i : ι) :
    Matrix.reindex (isolate i) (isolate i) (U.updateRow i (V i))=
      mix (Matrix.reindex (isolate i) (isolate i) U) (Matrix.reindex (isolate i) (isolate i) V)
        := by
  ext a b
  rcases a with ⟨a,ha⟩|⟨⟩ <;> rcases b with ⟨b,hb⟩|⟨⟩ <;>
    simp_all [Matrix.reindex_apply,isolate,mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,Matrix.updateRow_apply]

/-- Exchange any corresponding members of two bases, assuming exactly that
both original and both exchanged lists are bases. -/
theorem price (p : MatrixPrice) (U V : Matrix ι ι ℂ) (i : ι)
    (hU : IsUnit U) (hV : IsUnit V)
    (hU' : IsUnit (U.updateRow i (V i))) (hV' : IsUnit (V.updateRow i (U i))) :
    p.value (V.updateRow i (U i)*(U.updateRow i (V i))⁻¹)=p.value (V*U⁻¹) := by
  let e := isolate i
  have h := price_split p (Matrix.reindex e e U) (Matrix.reindex e e V)
    (TensorTools.unit_reindex _ _ hU) (TensorTools.unit_reindex _ _ hV)
    (by rw [← update_isolate]; exact TensorTools.unit_reindex _ _ hU')
    (by rw [← update_isolate]; exact TensorTools.unit_reindex _ _ hV')
  rw [← update_isolate,← update_isolate,Matrix.inv_reindex,← Reindexed.mul,
    Matrix.inv_reindex,← Reindexed.mul] at h
  rw [p.reindex _ _ (hV'.mul (Matrix.isUnit_nonsing_inv_iff.mpr hU')),
    p.reindex _ _ (hV.mul (Matrix.isUnit_nonsing_inv_iff.mpr hU))] at h
  exact h

end BasisExchange
end ExactFourier

end

section
namespace ExactFourier.DensePair
open scoped Matrix

/-- The weighted four-cycle whose wraparound entry is `l`. -/
def J (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,1,0,0;0,0,1,0;0,0,0,1;l,0,0,0]
/-- The identity plus the weighted four-cycle `J l`. -/
def X (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,0,0;0,1,1,0;0,0,1,1;l,0,0,1]
/-- The four-cycle construction with its middle forward link removed. -/
def Xb (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,0,0;0,1,0,0;0,0,1,1;l,0,0,1]
/-- The identity plus the three forward links, with no wraparound link. -/
def Xd : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,0,0;0,1,1,0;0,0,1,1;0,0,0,1]
/-- The first intermediate shear matrix in the dense-pair factorization. -/
def Y1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0;0,1,1,0;0,0,1,0;0,0,0,1]
/-- The second intermediate matrix, adding the first row's two forward links. -/
def Y2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,1,0;0,0,1,0;0,0,0,1]
/-- The third intermediate matrix, retaining only the first row's added links. -/
def Y3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;0,0,1,0;0,0,0,1]
/-- The fourth intermediate matrix, introducing the weighted wraparound link. -/
def Y4 (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;0,0,1,0;l,0,0,1]
/-- The fifth intermediate matrix in the dense-pair row-operation sequence. -/
def Y5 (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;l,0,1,1;l,0,0,1]
/-- The final intermediate matrix before the rank-one correction. -/
def Y6 (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,0;0,1,0,0;l,0,1,1;0,0,0,1]

/-- The backward cyclic permutation of four coordinates. -/
def cycle : Equiv.Perm (Fin 4) where
  toFun := ![3,0,1,2]
  invFun := ![1,2,3,0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem J_monomial (l : ℂ) (hl : l≠0) : MonomialMatrix (J l) := by
  refine ⟨cycle,![l,1,1,1],?_,?_⟩
  · intro i; fin_cases i <;> simp [hl]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [J,cycle]

theorem X_eq (l : ℂ) : X l=1+J l := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X,J]

theorem det_J (l : ℂ) : (J l).det=-l := by
  rw [Matrix.det_succ_row_zero]
  norm_num [J,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_X (l : ℂ) : (X l).det=1-l := by
  rw [Matrix.det_succ_row_zero]
  norm_num [X,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide] ; ring

theorem det_Xb (l : ℂ) : (Xb l).det=1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Xb,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_Xd : Xd.det=1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Xd,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_Y1 : Y1.det=1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Y1,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_Y2 : Y2.det=1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Y2,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_Y3 : Y3.det=1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Y3,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_Y4 (l : ℂ) : (Y4 l).det=1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Y4,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_Y5 (l : ℂ) : (Y5 l).det=1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Y5,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide]

theorem det_Y6 (l : ℂ) : (Y6 l).det=1-l := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Y6,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
    show (2 : Fin 3) ≠ 0 by decide,
    show (1 : Fin 3) < 2 by decide, show ¬(2 : Fin 3) ≤ 1 by decide,
    show (1 : Fin 4) < 2 by decide, show ¬(2 : Fin 4) ≤ 1 by decide] ; ring

theorem exchange01 (l : ℂ) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ).updateRow 1 (X l 1)=Y1 ∧
      (X l).updateRow 1 ((1 : Matrix (Fin 4) (Fin 4) ℂ) 1)=Xb l := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Y1,X,Xb,Matrix.updateRow_apply]

theorem exchange23 (l : ℂ) : Y2.updateRow 1 (Xb l 1)=Y3 ∧
    (Xb l).updateRow 1 (Y2 1)=X l := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Y2,Y3,X,Xb,Matrix.updateRow_apply]

theorem exchange34 (l : ℂ) : Y3.updateRow 3 (X l 3)=Y4 l ∧
    (X l).updateRow 3 (Y3 3)=Xd := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Y3,Y4,X,Xd,Matrix.updateRow_apply]

theorem exchange56 (l : ℂ) : (Y5 l).updateRow 3 (Xd 3)=Y6 l ∧
    Xd.updateRow 3 (Y5 l 3)=X l := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Y5,Y6,X,Xd,Matrix.updateRow_apply]

theorem shear12 : Y2=Matrix.transvection 0 1 1*Y1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Y1,Y2,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.transvection,Matrix.single,
      Matrix.one_apply]

theorem shear45 (l : ℂ) : Y5 l=Matrix.transvection 2 3 1*Y4 l := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Y4,Y5,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.transvection,Matrix.single,
      Matrix.one_apply]

end ExactFourier.DensePair

end

end Complexity
