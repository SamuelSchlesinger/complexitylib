/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PivotJoin

/-!
# Exact Fourier circuits: monomial feedback

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/MonomialFeedback.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier.MatrixPrice
open scoped Matrix Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

theorem one_add_monomial (p : MatrixPrice) (J : Matrix α α ℂ)
    (hJ : IsUnit J) (hmono : MonomialMatrix J) (hI : IsUnit (1+J)) :
    p.value (1+J)≤Fintype.card α := by
  let F : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;1,0]
  have hF : IsUnit F := by
    rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
    norm_num [F,Matrix.det_fin_two]
  have hpF : p.value F=1 := by
    have he : F=(Matrix.transvection (1 : Fin 2) 0 (1 : ℂ)).submatrix
        (Equiv.swap 0 1) (Equiv.refl _) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [F,Matrix.transvection,Matrix.single,Matrix.submatrix_apply]
    rw [he,p.submatrix_equiv _ (transvection_isUnit _ _ (by decide) _) _,p.normalized]
  have hT : IsUnit (pairLayer (β := α) F) := pairLayer_unit F hF
  have hP : IsUnit (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 J) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,hJ⟩
  have he : pairLayer (β := α) F*Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 J=
      Matrix.fromBlocks 1 J 1 0 := by
    rw [pairLayer_eq]
    simp [F,Matrix.fromBlocks_multiply]
  have hK : IsUnit (Matrix.fromBlocks (1 : Matrix α α ℂ) J (1 : Matrix α α ℂ) 0) := by
    rw [← he]; exact hT.mul hP
  have hpT : p.value (pairLayer (β := α) F)=Fintype.card α := by
    rw [pairLayer,p.reindex _ _ (TensorTools.unit_tensor _ _ hF isUnit_one),
      p.tensor _ _ hF isUnit_one,hpF,p.one]
    ring
  have hpP : p.value (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 J)=0 := by
    rw [p.directSum _ _ isUnit_one hJ,p.one,(p.zero_iff J hJ).mpr hmono,zero_add]
  have hp := p.mul_le _ _ hT hP
  rw [he,hpT,hpP,add_zero] at hp
  have hf := p.feedback (1 : Matrix α α ℂ) J 1 0 1 isUnit_one hK
    (by simp) (by simpa [CellPoly.feedback] using hI)
  simpa [CellPoly.feedback] using hf.trans hp

theorem source_shear (p : MatrixPrice) (U V : Matrix α α ℂ) (hU : IsUnit U) (hV : IsUnit V)
    (i j : α) (hij : i≠j) (c : ℂ) :
    p.value (V*(Matrix.transvection i j c*U)⁻¹)≤p.value (V*U⁻¹)+1 := by
  have hE := transvection_isUnit i j hij c
  rw [Matrix.mul_inv_rev,← Matrix.mul_assoc]
  have hh := p.mul_le (V*U⁻¹) (Matrix.transvection i j c)⁻¹
    (hV.mul (Matrix.isUnit_nonsing_inv_iff.mpr hU)) (Matrix.isUnit_nonsing_inv_iff.mpr hE)
  rw [p.inverse _ hE] at hh
  have hhE := p.transvection_le_one i j hij c
  linarith

end ExactFourier.MatrixPrice

end

section
namespace ExactFourier.DensePair
open scoped Matrix

theorem four_price (p : MatrixPrice) (l : ℂ) (hl : l≠0) (hl1 : l≠1) :
    p.value (X l*(Y6 l)⁻¹)≤6 := by
  have hneq : 1-l≠0 := sub_ne_zero.mpr (Ne.symm hl1)
  have hX : IsUnit (X l) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by rwa
    [det_X]))
  have hJ : IsUnit (J l) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by
    simpa [det_J] using hl))
  have hXb : IsUnit (Xb l) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Xb]; exact
    isUnit_one)
  have hXd : IsUnit Xd := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Xd]; exact isUnit_one)
  have hY1 : IsUnit Y1 := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Y1]; exact isUnit_one)
  have hY2 : IsUnit Y2 := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Y2]; exact isUnit_one)
  have hY3 : IsUnit Y3 := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Y3]; exact isUnit_one)
  have hY4 : IsUnit (Y4 l) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Y4]; exact
    isUnit_one)
  have hY5 : IsUnit (Y5 l) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_Y5]; exact
    isUnit_one)
  have hY6 : IsUnit (Y6 l) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by
    rwa [det_Y6]))
  have h0 := p.one_add_monomial (J l) hJ (J_monomial l hl) (by rwa [← X_eq])
  rw [← X_eq] at h0
  have h01 := BasisExchange.price p 1 (X l) 1 isUnit_one hX
    (by rw [(exchange01 l).1]; exact hY1) (by rw [(exchange01 l).2]; exact hXb)
  rw [(exchange01 l).1,(exchange01 l).2,inv_one,mul_one] at h01
  have h12 := p.source_shear Y1 (Xb l) hY1 hXb 0 1 (by decide) 1
  rw [← shear12] at h12
  have h23 := BasisExchange.price p Y2 (Xb l) 1 hY2 hXb
    (by rw [(exchange23 l).1]; exact hY3) (by rw [(exchange23 l).2]; exact hX)
  rw [(exchange23 l).1,(exchange23 l).2] at h23
  have h34 := BasisExchange.price p Y3 (X l) 3 hY3 hX
    (by rw [(exchange34 l).1]; exact hY4) (by rw [(exchange34 l).2]; exact hXd)
  rw [(exchange34 l).1,(exchange34 l).2] at h34
  have h45 := p.source_shear (Y4 l) Xd hY4 hXd 2 3 (by decide) 1
  rw [← shear45] at h45
  have h56 := BasisExchange.price p (Y5 l) Xd 3 hY5 hXd
    (by rw [(exchange56 l).1]; exact hY6) (by rw [(exchange56 l).2]; exact hX)
  rw [(exchange56 l).1,(exchange56 l).2] at h56
  norm_num at h0
  linarith

end ExactFourier.DensePair

end

section
noncomputable section
namespace ExactFourier.DensePair
open scoped Matrix Kronecker

/-- The row permutation exchanging the last two coordinates of the pivot matrix. -/
def rowY : Equiv.Perm (Fin 4) where
  toFun := ![0,1,3,2]
  invFun := ![0,1,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
/-- The row permutation exchanging the first pair and the last pair of coordinates. -/
def rowX : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
/-- The four-entry vector determining the pivot's rank-one correction. -/
def delta (l : ℂ) : Fin 4 → ℂ := ![-1,1,l,-l]
/-- Alternating signs for the pivot's rank-one correction. -/
def signs : Fin 4 → ℂ := ![1,-1,1,-1]
/-- The identity plus the pivot correction `delta l * signsᵀ / (1 - l)`. -/
def rankOne (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  1+(Matrix.of fun i j => delta l i*signs j/(1-l))
/-- The four-coordinate matrix obtained after the first diagonal normalization. -/
def scaled (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![l,1,1,1;1,l,1,1;1,1,l⁻¹,1;1,1,1,l⁻¹]
/-- The four-coordinate matrix in the second normalization of the dense pair. -/
def scaled2 (u : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,u,u,1;u,1,u,1;u,u,u^2,1;1,1,1,1]
/-- The two-coordinate matrix with three unit entries and lower-right entry `u`. -/
def B (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;1,u]

theorem rankOne_mul (l : ℂ) (hl1 : l≠1) :
    rankOne l*(Y6 l).submatrix rowY (Equiv.refl _)=
      (X l).submatrix rowX (Equiv.refl _) := by
  have h : 1-l≠0 := sub_ne_zero.mpr (Ne.symm hl1)
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rankOne,delta,signs,Y6,X,rowY,rowX,Fin.sum_univ_succ,
      Matrix.submatrix_apply,Matrix.one_apply] <;> field_simp <;> ring

/-- Left diagonal weights normalizing the rank-one pivot correction. -/
def left1 (l : ℂ) : Fin 4 → ℂ := fun i => (1-l)/delta l i

theorem left1_ne (l : ℂ) (hl : l≠0) (hl1 : l≠1) : ∀ i,left1 l i≠0 := by
  intro i
  fin_cases i <;> simp [left1,delta,hl,sub_ne_zero.mpr (Ne.symm hl1)]

theorem signs_ne : ∀ i,signs i≠0 := by intro i; fin_cases i <;> norm_num [signs]

theorem scale1 (l : ℂ) (hl : l≠0) (hl1 : l≠1) :
    Matrix.diagonal (left1 l)*rankOne l*Matrix.diagonal signs=scaled l := by
  have h : 1-l≠0 := sub_ne_zero.mpr (Ne.symm hl1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,Matrix.mul_diagonal,rankOne,left1,delta,signs,scaled
      ] <;> field_simp <;> ring

/-- Left diagonal weights for the second normalization of the dense pair. -/
def left2 (l : ℂ) : Fin 4 → ℂ := ![l⁻¹,l⁻¹,l⁻¹,1]
/-- Right diagonal weights for the second normalization of the dense pair. -/
def right2 (l : ℂ) : Fin 4 → ℂ := ![1,1,1,l]
theorem left2_ne (l : ℂ) (hl : l≠0) : ∀ i,left2 l i≠0 := by
  intro i; fin_cases i <;> simp [left2,hl]
theorem right2_ne (l : ℂ) (hl : l≠0) : ∀ i,right2 l i≠0 := by
  intro i; fin_cases i <;> simp [right2,hl]

theorem scale2 (l : ℂ) (hl : l≠0) :
    Matrix.diagonal (left2 l)*scaled l*Matrix.diagonal (right2 l)=scaled2 l⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,Matrix.mul_diagonal,left2,right2,scaled,scaled2,hl,pow_two]

/-- Identify four row coordinates with pairs of bits in the chosen tensor order. -/
def bitsRow : (Fin 4)≃(Fin 2×Fin 2) where
  toFun := ![(1,0),(0,1),(1,1),(0,0)]
  invFun := fun p => if p.1=0 then (if p.2=0 then 3 else 1) else (if p.2=0 then 0 else 2)
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> rfl

/-- Identify four column coordinates with pairs of bits in the chosen tensor order. -/
def bitsCol : (Fin 4)≃(Fin 2×Fin 2) where
  toFun := ![(0,1),(1,0),(1,1),(0,0)]
  invFun := fun p => if p.1=0 then (if p.2=0 then 3 else 0) else (if p.2=0 then 1 else 2)
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> rfl

theorem tensor_scaled (u : ℂ) : (B u⊗ₖB u).submatrix bitsRow bitsCol=scaled2 u := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [B,bitsRow,bitsCol,scaled2,Matrix.submatrix_apply,pow_two]

theorem B_unit (u : ℂ) (hu : u≠1) : IsUnit (B u) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [isUnit_iff_ne_zero]
  simpa [B,Matrix.det_fin_two] using sub_ne_zero.mpr hu

end ExactFourier.DensePair

end
end

section
namespace ExactFourier.DensePair
open scoped Matrix Kronecker

theorem rankOne_price (p : MatrixPrice) (l : ℂ) (hl : l≠0) (hl1 : l≠1) :
    IsUnit (rankOne l) ∧ p.value (rankOne l)≤6 := by
  have hX : IsUnit (X l) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (by rw [det_X]; exact sub_ne_zero.mpr (Ne.symm hl1)))
  have hY : IsUnit (Y6 l) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (by rw [det_Y6]; exact sub_ne_zero.mpr (Ne.symm hl1)))
  have hY' := (Matrix.isUnit_submatrix_equiv rowY (Equiv.refl _)).mpr hY
  have he : rankOne l=(X l).submatrix rowX (Equiv.refl _)*
      ((Y6 l).submatrix rowY (Equiv.refl _))⁻¹ := by
    rw [← rankOne_mul l hl1,Matrix.mul_nonsing_inv_cancel_right _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp hY')]
  have hf : rankOne l=(X l*(Y6 l)⁻¹).submatrix rowX rowY := by
    rw [he,Matrix.inv_submatrix_equiv,Matrix.submatrix_mul_equiv]
  rw [hf]
  exact ⟨(Matrix.isUnit_submatrix_equiv rowX rowY).mpr
    (hX.mul (Matrix.isUnit_nonsing_inv_iff.mpr hY)),
    by rw [p.submatrix_equiv _ (hX.mul (Matrix.isUnit_nonsing_inv_iff.mpr hY))];
       exact four_price p l hl hl1⟩

theorem normalized_price (p : MatrixPrice) (u : ℂ) (hu : u≠0) (hu1 : u≠1) :
    p.value (B u)≤(3:ℝ)/2 := by
  let l := u⁻¹
  have hl : l≠0 := inv_ne_zero hu
  have hl1 : l≠1 := by simpa [l] using hu1
  obtain ⟨hT,hprice⟩ := rankOne_price p l hl hl1
  have hD1 : IsUnit (Matrix.diagonal (left1 l)) := Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (left1_ne l hl hl1 i)))
  have hR1 : IsUnit (Matrix.diagonal signs) := Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (signs_ne i)))
  have hS : IsUnit (scaled l) := by rw [← scale1 l hl hl1]; exact (hD1.mul hT).mul hR1
  have hp1 := p.monomial (rankOne l) (Matrix.diagonal (left1 l)) (Matrix.diagonal signs) hT
    (MonomialMatrix.diagonal _ (left1_ne l hl hl1)) (MonomialMatrix.diagonal _ signs_ne)
  rw [scale1 l hl hl1] at hp1
  have hp2 := p.monomial (scaled l) (Matrix.diagonal (left2 l)) (Matrix.diagonal (right2 l)) hS
    (MonomialMatrix.diagonal _ (left2_ne l hl)) (MonomialMatrix.diagonal _ (right2_ne l hl))
  rw [scale2 l hl] at hp2
  have he : l⁻¹=u := inv_inv u
  rw [he] at hp2
  have hb := B_unit u hu1
  have hp3 := p.submatrix_equiv (B u⊗ₖ B u) (TensorTools.unit_tensor _ _ hb hb) bitsRow bitsCol
  rw [tensor_scaled,p.tensor _ _ hb hb] at hp3
  norm_num at hp3
  linarith

theorem price (p : MatrixPrice) (H : Matrix (Fin 2) (Fin 2) ℂ)
    (hH : IsUnit H) (hdense : ∀ i j,H i j≠0) : p.value H≤(3:ℝ)/2 := by
  let u := H 0 0*H 1 1/(H 0 1*H 1 0)
  have hu : u≠0 := div_ne_zero (mul_ne_zero (hdense _ _) (hdense _ _))
    (mul_ne_zero (hdense _ _) (hdense _ _))
  have hu1 : u≠1 := by
    intro he
    have he' : H 0 0*H 1 1=H 0 1*H 1 0 := (div_eq_one_iff_eq
      (mul_ne_zero (hdense _ _) (hdense _ _))).mp he
    have hh := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hH)
    apply hh
    simp [Matrix.det_fin_two,he']
  let d : Fin 2 → ℂ := ![(H 0 0)⁻¹,(H 1 0)⁻¹]
  let e : Fin 2 → ℂ := ![1,H 0 0/H 0 1]
  have hd : ∀ i,d i≠0 := by intro i; fin_cases i <;> simp [d,hdense]
  have he : ∀ i,e i≠0 := by intro i; fin_cases i <;> simp [e,hdense]
  have heq : Matrix.diagonal d*H*Matrix.diagonal e=B u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul,Matrix.mul_diagonal,d,e,B,u,hdense] <;> field_simp [hdense]
  have hp := p.monomial H (Matrix.diagonal d) (Matrix.diagonal e) hH
    (MonomialMatrix.diagonal _ hd) (MonomialMatrix.diagonal _ he)
  rw [heq] at hp
  rw [← hp]
  exact normalized_price p u hu hu1

end ExactFourier.DensePair

end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Coordinates outside the image of an embedding. -/
abbrev complement (e : β ↪ α) := {a : α // a∉Set.range e}
instance (e : β ↪ α) : Fintype (complement e) := Fintype.ofFinite _
instance (e : β ↪ α) : DecidableEq (complement e) := Classical.decEq _

/-- Split the ambient coordinates into an embedding's image and its complement. -/
def coordinates (e : β ↪ α) : β⊕complement e ≃ α := by
  classical
  letI : DecidablePred (fun a => a∈Set.range e) := Classical.decPred _
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

@[simp] theorem coordinates_inl
    {α : Type} {β : Type}     (e : β ↪ α) (i : β) : coordinates e (Sum.inl i)=e i := rfl
@[simp] theorem coordinates_inr
    {α : Type} {β : Type}     (e : β ↪ α) (i : complement e) : coordinates e (Sum.inr i)=i.val
      := rfl

/-- Extend a matrix along an embedding, acting as the identity on unused coordinates. -/
def matrix (e : β ↪ α) (A : Matrix β β ℂ) : Matrix α α ℂ :=
  Matrix.reindex (coordinates e) (coordinates e) (Matrix.fromBlocks A 0 0 (1 : Matrix
    (complement e) (complement e) ℂ))

theorem unit (e : β ↪ α) (A : Matrix β β ℂ) (hA : IsUnit A) : IsUnit (matrix e A) :=
  TensorTools.unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA,isUnit_one⟩)

theorem price (p : MatrixPrice) (e : β ↪ α) (A : Matrix β β ℂ) (hA : IsUnit A) :
    p.value (matrix e A)=p.value A := by
  rw [matrix,p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA,isUnit_one⟩),p.identity_pad
    _ hA]

/-- Embed two distinct selected coordinates as a copy of `Fin 2`. -/
def pair (i j : α) (hij : i≠j) : Fin 2 ↪ α where
  toFun := fun a => if a=0 then i else j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

@[simp] theorem pair_zero
    {α : Type}   (i j : α) (hij : i≠j) : pair i j hij 0=i := rfl
@[simp] theorem pair_one
    {α : Type}   (i j : α) (hij : i≠j) : pair i j hij 1=j := by
      change (if (1 : Fin 2)=0 then i else j)=j; simp

omit [Fintype α] [DecidableEq α] in
theorem complement_ne_pair (i j : α) (hij : i≠j) (a : complement (pair i j hij)) :
    a.val≠i ∧ a.val≠j := by
  constructor
  · intro h; exact a.property ⟨0,h.symm⟩
  · intro h; apply a.property; exact ⟨1,by simpa using h.symm⟩

omit [Fintype α] in
theorem pair_matrix (i j : α) (hij : i≠j) (s t : ℂ) :
    matrix (pair i j hij) (!![1,s;t,1] : Matrix (Fin 2) (Fin 2) ℂ)=
      1+Matrix.single i j s+Matrix.single j i t := by
  ext a b
  obtain ⟨a,rfl⟩ := (coordinates (pair i j hij)).surjective a
  obtain ⟨b,rfl⟩ := (coordinates (pair i j hij)).surjective b
  have he (a b : Fin 2⊕complement (pair i j hij)) :
      matrix (pair i j hij) (!![1,s;t,1]) (coordinates (pair i j hij) a)
      (coordinates (pair i j hij) b)=
      Matrix.fromBlocks (!![1,s;t,1]) 0 0 (1 : Matrix (complement (pair i j hij)) (complement
        (pair i j hij)) ℂ) a b := by
    simp [matrix,Matrix.reindex_apply]
  rw [he]
  rcases a with a|a <;> rcases b with b|b
  · fin_cases a <;> fin_cases b <;> simp [Matrix.single,hij,Ne.symm hij]
  · have ha := complement_ne_pair i j hij b
    fin_cases a <;> simp [Matrix.single,Ne.symm ha.1,Ne.symm ha.2]
  · have ha := complement_ne_pair i j hij a
    fin_cases b <;> simp [Matrix.single,ha.1,ha.2,Ne.symm ha.1,Ne.symm ha.2]
  · have ha := complement_ne_pair i j hij a
    have hb := complement_ne_pair i j hij b
    simp [Matrix.single,Matrix.one_apply,Ne.symm ha.1,Ne.symm ha.2,Ne.symm hb.1,Ne.symm hb.2,
      Subtype.ext_iff]

theorem pair_price (p : MatrixPrice) (i j : α) (hij : i≠j) (s t : ℂ)
    (hs : s≠0) (ht : t≠0) (hst : 1-s*t≠0) :
    IsUnit (1+Matrix.single i j s+Matrix.single j i t) ∧
    p.value (1+Matrix.single i j s+Matrix.single j i t)≤(3:ℝ)/2 := by
  let H : Matrix (Fin 2) (Fin 2) ℂ := !![1,s;t,1]
  have hH : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (by simpa [H,Matrix.det_fin_two] using hst))
  rw [← pair_matrix i j hij s t]
  refine ⟨unit _ H hH,?_⟩
  rw [price p _ H hH]
  exact DensePair.price p H hH (by intro a b; fin_cases a <;> fin_cases b <;> simp [H,hs,ht])

end ExactFourier.Embedded

end
end

end Complexity
