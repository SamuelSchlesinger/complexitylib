/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.RawWordBound

/-!
# Exact Fourier circuits: raw positive

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/RawPositive.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem embedded (e : α ↪ β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Embedded.matrix e M)=p.value M := by
 rw [Embedded.matrix,p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,isUnit_one⟩),
  p.directSum _ _ hM isUnit_one,p.one,add_zero]

theorem zero_iff (M : Matrix α α ℂ) (hM : IsUnit M) : p.value M=0 ↔ MonomialMatrix M := by
 refine ⟨?_,p.monomial_zero M⟩
 intro hz
 by_contra hn
 have ha : 2≤Fintype.card α := by
  by_contra h
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact hn (monomial_of_subsingleton M hM)
 let e : Fin 2 ↪ α := (Fin.castLEEmb ha).trans (Fintype.equivFin α).symm.toEmbedding
 let V : Word (fun _:Unit=>α) (fun _=>M) α := callWord () (Function.Embedding.refl _)
 have hv : V.matrix=M := by rw [matrix_callWord,Embedded.matrix_refl]
 obtain ⟨h,hh,W,hW,hw⟩ := word_generates V (hv.symm ▸ hM) (hv.symm ▸ hn)
  (Embedded.matrix e shearU) (Embedded.unit e shearU shearU_unit)
 have hb := p.word_bound (fun _:Unit=>hM) W (Embedded.matrix e shearU) hW
 rw [hw] at hb
 have hweight : V.weight (fun _:Unit=>p.value M)=p.value M := by simp [V,Word.weight]
 rw [hweight,hz,mul_zero,p.embedded e shearU shearU_unit,p.normalized] at hb
 norm_num at hb
end ExactFourier.Packing.RawPrice

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace MonomialMatrix
variable {α : Type} [Fintype α] [DecidableEq α]
theorem transpose
    {α : Type}  [DecidableEq α] {M : Matrix α α ℂ} (hM : MonomialMatrix M) : MonomialMatrix
      M.transpose := by
 obtain ⟨s,d,hd,hs⟩ := hM
 refine ⟨s.symm,fun j=>d (s.symm j),fun j=>hd _,?_⟩
 intro i j
 change M j i=_
 rw [hs]
 by_cases h : i=s.symm j
 · subst i; simp
 · have hh : j≠s i := by intro he; exact h (by rw [he,s.symm_apply_apply])
   simp [h,hh]
end MonomialMatrix
namespace MatrixSymmetry
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem unit_transpose (M : Matrix α α ℂ) (hM : IsUnit M) : IsUnit M.transpose := by
 apply (Matrix.isUnit_iff_isUnit_det _).mpr
 simpa using (Matrix.isUnit_iff_isUnit_det M).mp hM

theorem inverse_tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (M⊗ₖN)⁻¹=M⁻¹⊗ₖN⁻¹ := by
 apply Matrix.inv_eq_right_inv
 rw [← Matrix.mul_kronecker_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hN),Matrix.one_kronecker_one]

theorem inverse_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (Matrix.fromBlocks M 0 0 N)⁻¹=Matrix.fromBlocks M⁻¹ 0 0 N⁻¹ := by
 apply Matrix.inv_eq_right_inv
 simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hN),Matrix.fromBlocks_one]

theorem inverse_reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 (Matrix.reindex e e M)⁻¹=Matrix.reindex e e M⁻¹ := by
 apply Matrix.inv_eq_right_inv
 change (Matrix.reindexAlgEquiv ℂ ℂ e) M*(Matrix.reindexAlgEquiv ℂ ℂ e) M⁻¹=1
 rw [← map_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)]
 exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_one
theorem transpose_tensor
    {α : Type} {β : Type}     (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 (M⊗ₖN).transpose=M.transpose⊗ₖN.transpose := rfl

end MatrixSymmetry
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing.RawPrice
open MatrixSymmetry
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Average the raw prices of a matrix, its inverse, its transpose, and inverse transpose. -/
def symValue (M : Matrix α α ℂ) : ℝ :=
 (p.value M+p.value M⁻¹+p.value M.transpose+p.value M.transpose⁻¹)/4

theorem sym_nonneg (M : Matrix α α ℂ) (hM : IsUnit M) : 0≤p.symValue M := by
 have h1 := p.nonneg M hM
 have h2 := p.nonneg M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
 have h3 := p.nonneg M.transpose (unit_transpose M hM)
 have h4 := p.nonneg M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))
 dsimp [symValue]
 positivity

theorem sym_zero (M : Matrix α α ℂ) (hM : IsUnit M) : p.symValue M=0 ↔ MonomialMatrix M := by
 constructor
 · intro hz
   have h1 := p.nonneg M hM
   have h2 := p.nonneg M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
   have h3 := p.nonneg M.transpose (unit_transpose M hM)
   have h4 := p.nonneg M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))
   apply (p.zero_iff M hM).mp
   dsimp [symValue] at hz
   linarith
 · intro hm
   simp only [symValue,p.monomial_zero M hm,p.monomial_zero _ hm.inverse,
    p.monomial_zero _ hm.transpose,p.monomial_zero _ hm.transpose.inverse]
   norm_num

theorem sym_reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.symValue (Matrix.reindex e e M)=p.symValue M := by
 simp only [symValue,inverse_reindex e M hM,Matrix.transpose_reindex,
  inverse_reindex e M.transpose (unit_transpose M hM)]
 rw [p.reindex e M hM,p.reindex e M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM),
  p.reindex e M.transpose (unit_transpose M hM),
  p.reindex e M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))]

theorem sym_mul (M N : Matrix α α ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (M*N)≤p.symValue M+p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 have h1 := p.mul_le M N hM hN
 have h2 := p.mul_le N⁻¹ M⁻¹ hiN hiM
 have h3 := p.mul_le N.transpose M.transpose htN htM
 have h4 := p.mul_le M.transpose⁻¹ N.transpose⁻¹ hitM hitN
 simp only [symValue,Matrix.mul_inv_rev,Matrix.transpose_mul]
 linarith

theorem sym_monomial (M L R : Matrix α α ℂ) (hM : IsUnit M)
 (hL : MonomialMatrix L) (hR : MonomialMatrix R) : p.symValue (L*M*R)=p.symValue M := by
 have hm := (hL.unit _).mul hM |>.mul (hR.unit _)
 have one_side : ∀ (M L R : Matrix α α ℂ),IsUnit M→MonomialMatrix L→MonomialMatrix R→
  p.symValue (L*M*R)≤p.symValue M := by
  intro M L R hM hL hR
  have h1 := p.sym_mul L M (hL.unit _) hM
  have h2 := p.sym_mul (L*M) R ((hL.unit _).mul hM) (hR.unit _)
  rw [(p.sym_zero L (hL.unit _)).mpr hL] at h1
  rw [(p.sym_zero R (hR.unit _)).mpr hR] at h2
  linarith
 apply le_antisymm (one_side M L R hM hL hR)
 have hh := one_side (L*M*R) L⁻¹ R⁻¹ hm hL.inverse hR.inverse
 have he : L⁻¹*(L*M*R)*R⁻¹=M := by
  simp only [← mul_assoc,Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det L).mp (hL.unit
    _)),one_mul]
  rw [mul_assoc,Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp (hR.unit _)),mul_one]
 rw [he] at hh
 exact hh

theorem sym_tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (M⊗ₖN)=(Fintype.card β : ℝ)*p.symValue M+(Fintype.card α : ℝ)*p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 simp only [symValue,inverse_tensor M N hM hN,transpose_tensor,inverse_tensor _ _ htM htN]
 rw [p.tensor M N hM hN,p.tensor M⁻¹ N⁻¹ hiM hiN,p.tensor M.transpose N.transpose htM htN,
  p.tensor M.transpose⁻¹ N.transpose⁻¹ hitM hitN]
 ring

theorem sym_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (Matrix.fromBlocks M 0 0 N)=p.symValue M+p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 simp only [symValue,inverse_sum M N hM hN,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
  inverse_sum _ _ htM htN]
 rw [p.directSum M N hM hN,p.directSum M⁻¹ N⁻¹ hiM hiN,p.directSum M.transpose N.transpose htM htN,
  p.directSum M.transpose⁻¹ N.transpose⁻¹ hitM hitN]
 ring

theorem sym_inverse (M : Matrix α α ℂ) (hM : IsUnit M) : p.symValue M⁻¹=p.symValue M := by
 have hdet := (Matrix.isUnit_iff_isUnit_det M).mp hM
 have htdet := (Matrix.isUnit_iff_isUnit_det M.transpose).mp (unit_transpose M hM)
 simp only [symValue,Matrix.nonsing_inv_nonsing_inv M hdet,Matrix.transpose_nonsing_inv,
  Matrix.nonsing_inv_nonsing_inv M.transpose htdet]
 ring

theorem sym_transpose (M : Matrix α α ℂ) : p.symValue M.transpose=p.symValue M := by
 simp only [symValue,Matrix.transpose_transpose]
 ring
end ExactFourier.Packing.RawPrice

end
end

section
noncomputable section
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice)

theorem shear_inverse : p.value shearU⁻¹=1 := by
 let d : Fin 2→ℂ := ![1,-1]
 let L := Matrix.diagonal d
 have hL : MonomialMatrix L := MonomialMatrix.diagonal d (by intro i; fin_cases i <;> norm_num [d])
 have he : shearU⁻¹=L*shearU*L := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
   norm_num [L,d,shearU,Matrix.mul_apply,Fin.sum_univ_two,Matrix.transvection,
    Matrix.diagonal,Matrix.single,Matrix.one_apply]
 rw [he,p.monomial _ L L shearU_unit hL hL,p.normalized]

theorem shear_transpose : p.value shearU.transpose=1 := by
 have he : Matrix.reindex (Fin.revPerm (n := 2)) (Fin.revPerm (n := 2)) shearU=shearU.transpose
   := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply,shearU,Matrix.transvection,
    Fin.revPerm,Fin.rev,Matrix.single]
 rw [← he,p.reindex _ _ shearU_unit,p.normalized]

theorem shear_transpose_inverse : p.value shearU.transpose⁻¹=1 := by
 have he : Matrix.reindex (Fin.revPerm (n := 2)) (Fin.revPerm (n := 2)) shearU=shearU.transpose
   := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply,shearU,Matrix.transvection,
    Fin.revPerm,Fin.rev,Matrix.single]
 rw [← he,MatrixSymmetry.inverse_reindex _ _ shearU_unit,
  p.reindex _ _ (Matrix.isUnit_nonsing_inv_iff.mpr shearU_unit),p.shear_inverse]

theorem sym_normalized : p.symValue shearU=1 := by
 rw [symValue,p.normalized,p.shear_inverse,p.shear_transpose,p.shear_transpose_inverse]
 norm_num

/-- The matrix price obtained by symmetrizing a raw comparison price. -/
def toMatrixPrice : MatrixPrice where
 value := p.symValue
 nonneg := p.sym_nonneg
 zero_iff := p.sym_zero
 reindex := p.sym_reindex
 monomial := p.sym_monomial
 mul_le := p.sym_mul
 tensor := p.sym_tensor
 directSum := p.sym_sum
 inverse := p.sym_inverse
 transpose := fun M _=>p.sym_transpose M
 normalized := p.sym_normalized
end ExactFourier.Packing.RawPrice

end
end

section
namespace ExactFourier.BasisExchange
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Keep the selected rows of `K` and use identity rows at all remaining positions. -/
def rows (K : Matrix ι ι ℂ) (H : Finset ι) : Matrix ι ι ℂ :=
  fun i j => if i∈H then K i j else (1 : Matrix ι ι ℂ) i j

theorem rows_insert (K : Matrix ι ι ℂ) (H : Finset ι) (j : ι) (hj : j∉H) :
    (rows K H).updateRow j (rows K Hᶜ j)=rows K (insert j H) ∧
    (rows K Hᶜ).updateRow j (rows K H j)=rows K (insert j H)ᶜ := by
  constructor <;> ext a b
  all_goals
    by_cases ha : a=j
    · subst a; simp [rows,Matrix.updateRow_apply,hj]
    · simp [rows,Matrix.updateRow_apply,ha]

theorem price_many (p : MatrixPrice) (K : Matrix ι ι ℂ)
    (hU : ∀ H : Finset ι,IsUnit (rows K H)) (H : Finset ι) :
    p.value (rows K Hᶜ*(rows K H)⁻¹)=p.value K := by
  induction H using Finset.induction_on with
  | empty =>
    have he : rows K ∅=1 := by ext i j; simp [rows]
    have hu : rows K Finset.univ=K := by ext i j; simp [rows]
    simp only [Finset.compl_empty,he,hu,inv_one,mul_one]
  | @insert j H hj ih =>
    have he := BasisExchange.price p (rows K H) (rows K Hᶜ) j (hU H) (hU Hᶜ)
      (by rw [(rows_insert K H j hj).1]; exact hU _) (by rw [(rows_insert K H j hj).2]; exact hU _)
    rw [(rows_insert K H j hj).1,(rows_insert K H j hj).2] at he
    exact he.trans ih

variable [LinearOrder ι]

theorem rows_unit (K : Matrix ι ι ℂ) (hl : K.IsLowerTriangular)
    (hd : ∀ i,K i i=1) (H : Finset ι) : IsUnit (rows K H) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hl' : (rows K H).IsLowerTriangular := by
    intro i j hij
    by_cases hi : i∈H
    · simp [rows,hi,hl hij]
    · have hij' : i<j := hij
      simp [rows,hi,ne_of_lt hij']
  rw [Matrix.det_of_isLowerTriangular _ hl']
  simp [rows,hd]

theorem price_triangular (p : MatrixPrice) (K : Matrix ι ι ℂ) (hl : K.IsLowerTriangular)
    (hd : ∀ i,K i i=1) (H : Finset ι) :
    p.value (rows K Hᶜ*(rows K H)⁻¹)=p.value K :=
  price_many p K (rows_unit K hl hd) H

end ExactFourier.BasisExchange

end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

/-- Bit strings represented recursively by a sum of two copies of the shorter strings. -/
abbrev Bits : ℕ → Type
  | 0 => PUnit
  | m+1 => Bits m ⊕ Bits m
@[reducible] instance bitsFintype : (m : ℕ) → Fintype (Bits m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m+1 => letI := bitsFintype m; inferInstanceAs (Fintype (Bits m ⊕ Bits m))
@[reducible] instance bitsDecidableEq : (m : ℕ) → DecidableEq (Bits m)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | m+1 => letI := bitsDecidableEq m; inferInstanceAs (DecidableEq (Bits m ⊕ Bits m))
@[reducible] instance bitsLinearOrder : (m : ℕ) → LinearOrder (Bits m)
  | 0 => inferInstanceAs (LinearOrder PUnit)
  | m+1 => @Sum.Lex.linearOrder (Bits m) (Bits m) (bitsLinearOrder m) (bitsLinearOrder m)

@[reducible] instance (priority := 2000) bitsLT (m : ℕ) : LT (Bits m) :=
  (bitsLinearOrder m).toLT

@[simp] theorem bits_card (m : ℕ) : Fintype.card (Bits m)=2^m := by
  induction m with
  | zero => simp [Bits]
  | succ m ih => simpa [Bits,pow_succ,mul_two] using congrArg (fun n => n+n) ih

/-- The recursive signed-bit matrix whose square is zero. -/
def D : (m : ℕ) → Matrix (Bits m) (Bits m) ℂ
  | 0 => 0
  | m+1 => Matrix.fromBlocks (D m) 0 1 (-D m)
/-- The identity plus the nilpotent signed-bit matrix `D m`. -/
def T (m : ℕ) : Matrix (Bits m) (Bits m) ℂ := 1+D m

theorem D_square (m : ℕ) : D m*D m=0 := by
  induction m with
  | zero => simp [D]
  | succ m ih => simp [D,Matrix.fromBlocks_multiply,ih]

theorem T_inv_mul (m : ℕ) : (1-D m)*T m=1 := by
  rw [T,mul_add,sub_mul,sub_mul,one_mul,one_mul,mul_one,D_square]
  abel

theorem T_unit (m : ℕ) : IsUnit (T m) :=
  by
    rw [isUnit_iff_exists_inv']
    exact ⟨1-D m,T_inv_mul m⟩

theorem T_inv (m : ℕ) : (T m)⁻¹=1-D m := Matrix.inv_eq_left_inv (T_inv_mul m)

theorem D_lower (m : ℕ) : (D m).IsLowerTriangular := by
  induction m with
  | zero => intro i j hij; rfl
  | succ m ih =>
    intro i j hij
    change (toLex i : Bits m ⊕ₗ Bits m) < toLex j at hij
    rcases i with i|i <;> rcases j with j|j
    · have hh : i<j := Sum.Lex.inl_lt_inl_iff.mp hij
      exact ih hh
    · rfl
    · exact False.elim (Sum.Lex.not_inr_lt_inl hij)
    · change -(D m i j)=0
      have hh : i<j := Sum.Lex.inr_lt_inr_iff.mp hij
      rw [ih hh,neg_zero]

theorem D_diag (m : ℕ) : ∀ i,D m i i=0 := by
  induction m with
  | zero => intro i; rfl
  | succ m ih => intro i; rcases i with i|i <;> simp [D,ih]

theorem T_lower (m : ℕ) : (T m).IsLowerTriangular := by
  intro i j hij
  have h : i<j := hij
  simp [T,ne_of_lt h,D_lower m hij]

theorem T_diag (m : ℕ) : ∀ i,T m i i=1 := by simp [T,D_diag]

theorem T_succ (m : ℕ) : T (m+1)=Matrix.fromBlocks (T m) 0 1 (T m)⁻¹ := by
  rw [T_inv]
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [T,D,Matrix.one_apply,Matrix.fromBlocks,sub_eq_add_neg]

end ExactFourier.SignedBits

end
end

end Complexity
