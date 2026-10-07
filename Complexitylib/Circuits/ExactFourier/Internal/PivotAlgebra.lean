/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PolynomialClearing

/-!
# Exact Fourier circuits: pivot algebra

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PivotAlgebra.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier.Pivot
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The block pivot transform using the inverse of the lower-right block. -/
noncomputable def matrix (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix (α⊕β) (α⊕β) ℂ :=
  Matrix.fromBlocks (A-C*D⁻¹*B) (C*D⁻¹) (-D⁻¹*B) D⁻¹

theorem factor (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    matrix A C B D=Matrix.fromBlocks A C 0 (1 : Matrix β β ℂ)*
      Matrix.fromBlocks (1 : Matrix α α ℂ) 0 (-D⁻¹*B) D⁻¹ := by
  simp [matrix,Matrix.fromBlocks_multiply,Matrix.mul_assoc,sub_eq_add_neg]

theorem unit (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hA : IsUnit A) (hD : IsUnit D) :
    IsUnit (matrix A C B D) := by
  rw [factor]
  exact (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA,isUnit_one⟩).mul
    (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,Matrix.isUnit_nonsing_inv_iff.mpr hD⟩)

theorem solve (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hD : IsUnit D) :
    matrix A C B D*Matrix.fromBlocks (1 : Matrix α α ℂ) 0 B D=
      Matrix.fromBlocks A C 0 (1 : Matrix β β ℂ) := by
  have hi := Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  simp [matrix,Matrix.fromBlocks_multiply,Matrix.mul_assoc,hi]

theorem involutive
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hD : IsUnit D) :
    matrix (A-C*D⁻¹*B) (C*D⁻¹) (-D⁻¹*B) D⁻¹=Matrix.fromBlocks A C B D := by
  have hi := Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hj := Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hii := Matrix.nonsing_inv_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  simp [matrix,hii,Matrix.mul_assoc,hi]
  rw [← Matrix.mul_assoc,hj,Matrix.one_mul]

theorem schur_unit (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hD : IsUnit D)
    (hK : IsUnit (Matrix.fromBlocks A C B D)) : IsUnit (A-C*D⁻¹*B) := by
  let := hD.invertible
  simpa only [Matrix.invOf_eq_nonsing_inv] using
    (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂ (A := A) (B := C) (C := B)).mp hK

end ExactFourier.Pivot

end

section
namespace ExactFourier.MatrixPrice

theorem pair_le_two_of_entry (p : MatrixPrice) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnit A) (ha : A 0 0≠0) : p.value A≤2 := by
  let L := Matrix.transvection (1 : Fin 2) 0 (A 1 0/A 0 0)
  let U := Matrix.transvection (0 : Fin 2) 1 (A 0 1/A 0 0)
  let d : Fin 2 → ℂ := ![A 0 0,A.det/A 0 0]
  have hdet : A.det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hd : ∀ i,d i≠0 := by intro i; fin_cases i <;> simp [d,ha,hdet]
  have hL : IsUnit L := transvection_isUnit _ _ (by decide) _
  have hU : IsUnit U := transvection_isUnit _ _ (by decide) _
  have hD : IsUnit (Matrix.diagonal d) := Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hd i)))
  have he : A=L*(Matrix.diagonal d*U) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L,U,d,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply,
        Matrix.transvection,Matrix.single,Matrix.one_apply,Matrix.det_fin_two] <;>
      field_simp ; ring
  have hp := p.mul_le L (Matrix.diagonal d*U) hL (hD.mul hU)
  have hm := p.monomial U (Matrix.diagonal d) 1 hU (MonomialMatrix.diagonal d hd) MonomialMatrix.one
  rw [mul_one] at hm
  rw [← he,hm] at hp
  have hl := p.transvection_le_one (1 : Fin 2) 0 (by decide) (A 1 0/A 0 0)
  have hu := p.transvection_le_one (0 : Fin 2) 1 (by decide) (A 0 1/A 0 0)
  change p.value L≤1 at hl
  change p.value U≤1 at hu
  linarith

theorem pair_le_two (p : MatrixPrice) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnit A) : p.value A≤2 := by
  by_cases ha : A 0 0≠0
  · exact p.pair_le_two_of_entry A hA ha
  · have ha0 : A 0 0=0 := not_ne_iff.mp ha
    have hc : A 1 0≠0 := by
      intro hc
      have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)
      apply hd
      simp [Matrix.det_fin_two,ha0,hc]
    let e : Equiv.Perm (Fin 2) := Equiv.swap 0 1
    have hB : IsUnit (A.submatrix e (Equiv.refl _)) :=
      (Matrix.isUnit_submatrix_equiv e (Equiv.refl _)).mpr hA
    have hp := p.pair_le_two_of_entry (A.submatrix e (Equiv.refl _)) hB
      (by simpa [e,Matrix.submatrix_apply] using hc)
    rwa [p.submatrix_equiv A hA e (Equiv.refl _)] at hp

end ExactFourier.MatrixPrice

end

section
namespace ExactFourier
open scoped Kronecker
variable {β : Type} [Fintype β] [DecidableEq β]

/-- Identify a two-valued coordinate tag with a sum of two copies of the coordinate type. -/
def twoProdEquiv (β : Type) : Fin 2×β ≃ β⊕β where
  toFun := fun x => if x.1=0 then Sum.inl x.2 else Sum.inr x.2
  invFun := Sum.elim (fun b => (0,b)) (fun b => (1,b))
  left_inv := by rintro ⟨i,b⟩; fin_cases i <;> simp
  right_inv := by intro b; cases b <;> simp

/-- Apply the same two-coordinate matrix to each pair of corresponding block coordinates. -/
noncomputable def pairLayer (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (β⊕β) (β⊕β) ℂ :=
  Matrix.reindex (twoProdEquiv β) (twoProdEquiv β) (A ⊗ₖ (1 : Matrix β β ℂ))

theorem pairLayer_eq
    {β : Type}  [DecidableEq β] (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pairLayer (β := β) A=Matrix.fromBlocks (A 0 0•1) (A 0 1•1) (A 1 0•1) (A 1 1•1) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem pairLayer_unit (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A) :
    IsUnit (pairLayer (β := β) A) :=
  TensorTools.unit_reindex _ _ (TensorTools.unit_tensor _ _ hA isUnit_one)

namespace MatrixPrice
theorem pair_layer (p : MatrixPrice) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A) :
    p.value (pairLayer (β := β) A)≤2*Fintype.card β := by
  rw [pairLayer,p.reindex _ _ (TensorTools.unit_tensor _ _ hA isUnit_one),
    p.tensor _ _ hA isUnit_one,p.one,mul_zero,add_zero]
  have h := mul_le_mul_of_nonneg_left (p.pair_le_two A hA) (Nat.cast_nonneg (Fintype.card β) :
    (0:ℝ)≤_)
  nlinarith only [h]
end MatrixPrice
end ExactFourier

end

section
namespace ExactFourier
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_invertible_evaluation (G : Matrix α α (Polynomial ℂ)) (z0 : ℂ)
    (hG : IsUnit (G.map (eval z0))) (E : Finset ℂ) :
    ∃ s : ℂ,s∉E ∧ IsUnit (G.map (eval s)) := by
  classical
  have hd : G.det≠0 := by
    intro he
    have hdu := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG)
    apply hdu
    have hh := RingHom.map_det (evalRingHom z0) G
    rw [he,map_zero] at hh
    exact hh.symm
  obtain ⟨s,hs⟩ := (E∪G.det.roots.toFinset).exists_notMem
  refine ⟨s,fun h => hs (Finset.mem_union_left _ h),?_⟩
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro he
  apply hs
  apply Finset.mem_union_right
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hd).mpr
  have hh := RingHom.map_det (evalRingHom s) G
  exact hh.trans he

end ExactFourier

end

section
namespace ExactFourier.Pivot
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Extend a pair layer on the two state blocks by the identity on the data block. -/
noncomputable def side (L : Matrix (Fin 2) (Fin 2) ℂ) : Matrix ((α⊕β)⊕β) ((α⊕β)⊕β) ℂ :=
  Matrix.reindex (Equiv.sumAssoc α β β).symm (Equiv.sumAssoc α β β).symm
    (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 (pairLayer (β := β) L))

theorem side_eq
    {α β : Type} [DecidableEq α] [DecidableEq β] (L : Matrix (Fin 2) (Fin 2) ℂ) :
    side (α := α) (β := β) L=
      Matrix.fromBlocks (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 (L 0 0•1))
        (Matrix.fromRows 0 (L 0 1•1)) (Matrix.fromCols 0 (L 1 0•1)) (L 1 1•1) := by
  rw [side,pairLayer_eq]
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;> rfl

theorem side_unit (L : Matrix (Fin 2) (Fin 2) ℂ) (hL : IsUnit L) :
    IsUnit (side (α := α) (β := β) L) :=
  TensorTools.unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,pairLayer_unit L
    hL⟩)

theorem side_price (p : MatrixPrice) (L : Matrix (Fin 2) (Fin 2) ℂ) (hL : IsUnit L) :
    p.value (side (α := α) (β := β) L)≤2*Fintype.card β := by
  rw [side,p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,pairLayer_unit L hL⟩),
    p.directSum _ _ isUnit_one (pairLayer_unit L hL),p.one,zero_add]
  exact p.pair_layer L hL

/-- Place the original block matrix between the state coordinates used by the pivot. -/
noncomputable def middle (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix ((α⊕β)⊕β) ((α⊕β)⊕β) ℂ :=
  Matrix.reindex TensorTools.middleEquiv TensorTools.middleEquiv
    (Matrix.fromBlocks (Matrix.fromBlocks A C B D) 0 0 (1 : Matrix β β ℂ))

theorem middle_eq
    {α : Type} {β : Type}    [DecidableEq β] (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    middle A C B D=Matrix.fromBlocks (Matrix.fromBlocks A 0 0 (1 : Matrix β β ℂ))
      (Matrix.fromRows C 0) (Matrix.fromCols B 0) D := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;> rfl

/-- The two-coordinate pivot factor with entries `[[b, 1], [1, 1]]`. -/
def P (b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![b,1;1,1]
/-- The two-coordinate pivot factor with entries `[[1, 1-b], [1, -b]]`. -/
def Q (b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,1-b;1,-b]

theorem P_unit (b : ℂ) (hb : b≠1) : IsUnit (P b) := by
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  simpa [P,Matrix.det_fin_two] using sub_ne_zero.mpr hb

theorem Q_unit (b : ℂ) : IsUnit (Q b) := by
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  have he : (Q b).det=(-1 : ℂ) := by simp [Q,Matrix.det_fin_two]; ring
  rw [he]; exact neg_ne_zero.mpr one_ne_zero

/-- The data block of the parameterized pivot cell. -/
noncomputable def data (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromBlocks A C ((1-b)•B) (b•1+(1-b)•D)
/-- The block carrying the pivot cell's state contribution into its data coordinates. -/
noncomputable def co (C : Matrix α β ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromRows C (1+(1-b)•D)
/-- The block carrying the pivot cell's data contribution into its state coordinates. -/
noncomputable def bo (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromCols ((-b)•B) (b•(1-D))
/-- The pivot cell's state block `1 - b • D`. -/
noncomputable def state (D : Matrix β β ℂ) (b : ℂ) := 1-b•D
/-- Assemble the parameterized data, coupling, and state blocks into one pivot cell. -/
noncomputable def cell (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) :=
  Matrix.fromBlocks (data A C B D b) (co C D b) (bo B D b) (state D b)

theorem cell_eq (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) :
    cell A C B D b=side (Q b)*middle A C B D*side (P b) := by
  rw [side_eq,side_eq,middle_eq]
  simp only [cell,data,co,bo,state,P,Q,        Matrix.fromBlocks_multiply,
    Matrix.fromCols_mul_fromRows,
    Matrix.fromRows_mul,Matrix.mul_fromCols,Matrix.fromCols_mul_fromBlocks,
    Matrix.fromBlocks_mul_fromRows,    Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,Matrix.zero_mul,Matrix.mul_zero,
    add_zero,zero_add]
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [Matrix.fromBlocks,Matrix.fromRows,Matrix.fromCols,Sum.elim,sub_smul,smul_sub,
      Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,Matrix.neg_apply] <;> ring

end ExactFourier.Pivot

end

section
namespace ExactFourier.Pivot
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem cell_unit (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) (hb : b≠1)
    (hK : IsUnit (Matrix.fromBlocks A C B D)) : IsUnit (cell A C B D b) := by
  rw [cell_eq]
  exact ((side_unit _ (Q_unit b)).mul (TensorTools.unit_reindex _ _
    (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hK,isUnit_one⟩))).mul (side_unit _ (P_unit b hb))

theorem cell_price (p : MatrixPrice) (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) (hb : b≠1)
    (hK : IsUnit (Matrix.fromBlocks A C B D)) :
    p.value (cell A C B D b)≤p.value (Matrix.fromBlocks A C B D)+4*Fintype.card β := by
  have hm : IsUnit (middle A C B D) := TensorTools.unit_reindex _ _
    (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hK,isUnit_one⟩)
  have hq : IsUnit (side (α := α) (β := β) (Q b)) := side_unit _ (Q_unit b)
  have hp : IsUnit (side (α := α) (β := β) (P b)) := side_unit _ (P_unit b hb)
  have h1 := p.mul_le _ _ (hq.mul hm) hp
  have h2 := p.mul_le _ _ hq hm
  have h3 := side_price (α := α) (β := β) p (Q b) (Q_unit b)
  have h4 := side_price (α := α) (β := β) p (P b) (P_unit b hb)
  have he : p.value (middle A C B D)=p.value (Matrix.fromBlocks A C B D) := by
    rw [middle,p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hK,isUnit_one⟩),
      p.identity_pad _ hK]
  rw [← cell_eq] at h1
  rw [he] at h2
  linarith

theorem choose_data (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ)
    (hK : IsUnit (Matrix.fromBlocks A C B D)) :
    ∃ b : ℂ,b≠0 ∧ b≠1 ∧ IsUnit (data A C B D b) := by
  classical
  let K := Matrix.fromBlocks A C B D
  let J := Matrix.fromBlocks (0 : Matrix α α ℂ) (0 : Matrix α β ℂ) (-B) (1-D)
  let G : Matrix (α⊕β) (α⊕β) (Polynomial ℂ) := fun i j => Polynomial.C (K i j)+X*Polynomial.C (J
    i j)
  have he (b : ℂ) : G.map (eval b)=data A C B D b := by
    ext i j
    change eval b (G i j)=data A C B D b i j
    cases i <;> cases j <;> simp [G,K,J,data,Matrix.fromBlocks,Sum.elim,sub_smul] <;> ring
  have h0 : IsUnit (G.map (eval 0)) := by
    rw [he]; simpa [data] using hK
  obtain ⟨b,hb,hu⟩ := exists_invertible_evaluation G 0 h0 {0,1}
  have hb' : b≠0 ∧ b≠1 := by simpa using hb
  exact ⟨b,hb'.1,hb'.2,by rwa [he] at hu⟩

theorem denominator
    {β : Type}  [DecidableEq β] (D : Matrix β β ℂ) (b : ℂ) : 1-(1 : ℂ)•state D b=b•D := by
  simp [state]

theorem cell_feedback
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (b : ℂ) (hb : b≠0) (hD : IsUnit D) :
    CellPoly.feedback (data A C B D b) (co C D b) (bo B D b) (state D b) 1=
      matrix A C B D := by
  have hi := Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hj := Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hinv : (b•D)⁻¹=b⁻¹•D⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simp [smul_smul,hi,hb]
  have hCD : C*D⁻¹*D=C := by rw [Matrix.mul_assoc,hi,Matrix.mul_one]
  rw [CellPoly.feedback,denominator,hinv]
  simp only [data,co,bo,matrix,Matrix.fromRows_mul,
    Matrix.mul_smul,Matrix.smul_mul,
    smul_smul,Matrix.add_mul,Matrix.one_mul]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks,Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,
      smul_sub,sub_smul,Matrix.mul_sub,Matrix.mul_one,      hj,hi,hCD,Matrix.one_mul] <;>
        field_simp <;> ring

end ExactFourier.Pivot

namespace ExactFourier.MatrixPrice
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem pivot_bound (p : MatrixPrice) (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hA : IsUnit A) (hD : IsUnit D)
    (hK : IsUnit (Matrix.fromBlocks A C B D)) :
    p.value (Pivot.matrix A C B D)≤p.value (Matrix.fromBlocks A C B D)+4*Fintype.card β := by
  obtain ⟨b,hb0,hb1,hM⟩ := Pivot.choose_data A C B D hK
  have hden : IsUnit (1-(1 : ℂ)•Pivot.state D b) := by
    rw [Pivot.denominator]; exact scalar_unit _ hD _ hb0
  have hH : IsUnit (CellPoly.feedback (Pivot.data A C B D b) (Pivot.co C D b)
      (Pivot.bo B D b) (Pivot.state D b) 1) := by
    rw [Pivot.cell_feedback A C B D b hb0 hD]; exact Pivot.unit A C B D hA hD
  have hf := p.feedback (Pivot.data A C B D b) (Pivot.co C D b)
    (Pivot.bo B D b) (Pivot.state D b) 1 hM (Pivot.cell_unit A C B D b hb1 hK) hden hH
  rw [Pivot.cell_feedback A C B D b hb0 hD] at hf
  exact hf.trans (Pivot.cell_price p A C B D b hb1 hK)

end ExactFourier.MatrixPrice

end

end Complexity
