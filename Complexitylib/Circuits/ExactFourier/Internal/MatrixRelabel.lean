/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PairFamilies

/-!
# Exact Fourier circuits: matrix relabel

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/MatrixRelabel.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
theorem reindex_mulVec
    {α : Type} {β : Type} {γ : Type} {δ : Type} [Fintype α]  [Fintype γ]  (e : β≃δ) (f : α≃γ) (M
      : Matrix β α ℂ) (x : γ→ℂ) :
 (Matrix.reindex e f M).mulVec x=(M.mulVec (x∘f))∘e.symm := by
 funext i
 simp only [Matrix.mulVec,dotProduct,Matrix.reindex_apply,Matrix.submatrix_apply,
   Function.comp_apply]
 exact (f.sum_comp (fun j=>M (e.symm i) (f.symm j)*x j)).symm.trans (by simp)
end ExactFourier

end

section
noncomputable section
namespace ExactFourier.RadixTwo

/-- The Fourier matrix associated with the specified size and complex root. -/
def dft (n : ℕ) (ω : ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j=>ω^(i.val*j.val)

 /-- The block butterfly matrix combining even and odd Fourier transforms. -/
 def butterfly (n : ℕ) (ω : ℂ) : Matrix (Fin n⊕Fin n) (Fin n⊕Fin n) ℂ :=
 Matrix.fromBlocks 1 (Matrix.diagonal (fun i=>ω^i.val)) 1 (-Matrix.diagonal (fun i=>ω^i.val))

theorem butterfly_layer (n : ℕ) (ω : ℂ) (hω : ω≠0) : Layered (butterfly n ω) 1 := by
 let M := fun i : Fin n=>(!![1,ω^i.val;1,-ω^i.val] : Matrix (Fin 2) (Fin 2) ℂ)
 have hm : ∀ i,IsUnit (M i) := by
  intro i
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_fin_two]
  change 1 * (-ω^i.val) - ω^i.val * 1 ≠ 0
  have hh := pow_ne_zero i.val hω
  intro he; apply hh; linear_combination -1/2 * he
 have h := (Layered.blockDiagonal M 1 (fun i=>Layered.pair (M i) (hm i))).reindex (twoProdEquiv
   (Fin n))
 have he : Matrix.reindex (twoProdEquiv (Fin n)) (twoProdEquiv (Fin n)) (Matrix.blockDiagonal
   M)=butterfly n ω := by
  ext i j
  cases i <;> cases j <;>
   simp [twoProdEquiv,Matrix.reindex_apply,Matrix.blockDiagonal,M,butterfly,Matrix.one_apply,
     Matrix.diagonal_apply]
 rw [he] at h
 exact h

/-- Interleave two coordinate blocks into the even and odd positions. -/
def paritySumEquiv (n : ℕ) : (Fin n⊕Fin n)≃Fin (n+n) :=
 ((twoProdEquiv (Fin n)).symm.trans (Equiv.prodComm _ _)).trans (parityEquiv n)

@[simp] theorem paritySumEquiv_inl (n : ℕ) (i : Fin n) : paritySumEquiv n (.inl i)=evenIndex n i
    := by
 apply Fin.ext; simp [paritySumEquiv,twoProdEquiv,parityEquiv,evenIndex]
@[simp] theorem paritySumEquiv_inr (n : ℕ) (i : Fin n) : paritySumEquiv n (.inr i)=oddIndex n i
    := by
 apply Fin.ext; simp [paritySumEquiv,twoProdEquiv,parityEquiv,oddIndex]

theorem dft_step (n : ℕ) (ω : ℂ) (hω : ω^n = -1) : dft (n+n) ω=
 Matrix.reindex finSumFinEquiv (paritySumEquiv n)
 (butterfly n ω*Matrix.fromBlocks (dft n (ω^2)) 0 0 (dft n (ω^2))) := by
 apply Matrix.mulVec_injective
 funext x
 rw [reindex_mulVec]
 have he := eval_split n ω hω x
 change eval (n+n) ω x=_
 rw [he]
 rw [← Matrix.mulVec_mulVec]
 funext i
 obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
 cases i with
 | inl j =>
  simp only [finSumFinEquiv_apply_left, Fin.addCases_left, Function.comp_apply,
    finSumFinEquiv_symm_apply_castAdd]
  simp [butterfly,dft,eval,evalAt,Matrix.mulVec,dotProduct,Matrix.one_apply,Matrix.diagonal_apply]
 | inr j =>
  simp only [finSumFinEquiv_apply_right, Fin.addCases_right, Function.comp_apply,
    finSumFinEquiv_symm_apply_natAdd]
  simp [butterfly,dft,eval,evalAt,Matrix.mulVec,dotProduct,Matrix.one_apply,
    Matrix.diagonal_apply, sub_eq_add_neg]

theorem dft_layers (k : ℕ) (ω : ℂ) (hω : IsPrimitiveRoot ω (2^k)) :
 Layered (dft (2^k) ω) (2*k) := by
 induction k generalizing ω with
 | zero =>
  change Layered (dft 1 ω) 0
  have he : dft 1 ω=(1 : Matrix (Fin 1) (Fin 1) ℂ) := by
   ext i j; fin_cases i; fin_cases j
   simp [dft]
  rw [he]
  exact Layered.identity
 | succ k ih =>
  have hs : IsPrimitiveRoot (ω^2) (2^k) :=
   IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ]; omega)
  have hh : ω^(2^k) = -1 :=
   (IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ])).eq_neg_one_of_two_right
  have hF := (ih (ω^2) hs).sum (ih (ω^2) hs)
  have hB := butterfly_layer (2^k) ω (hω.ne_zero (by positivity))
  have h := (hB.mul hF).two_reindex finSumFinEquiv (paritySumEquiv (2^k))
  rw [← dft_step (2^k) ω hh] at h
  have he : 2^(k+1)=2^k+2^k := by rw [pow_succ]; omega
  rw [he]
  simpa only [show 1+2*k+1=2*(k+1) by omega] using h
end ExactFourier.RadixTwo

end
end

section
noncomputable section
namespace ExactFourier.NewtonFourier
open scoped BigOperators
open Polynomial

/-- The Newton basis polynomial with roots at the first `k` powers of `ω`. -/
def newton (ω : ℂ) (k : ℕ) : ℂ[X] := ∏ j∈Finset.range k,(X-C (ω^j))
/-- The product of `1 - ω^j` for exponents from one through `i`. -/
def H (ω : ℂ) (i : ℕ) : ℂ := ∏ j∈Finset.range i,(1-ω^(j+1))
/-- The product of the negatives of the first `k` powers of `ω`. -/
def scale (ω : ℂ) (k : ℕ) : ℂ := ∏ j∈Finset.range k,(-ω^j)
/-- Evaluate the Newton basis at successive powers of `ω`. -/
def N (n : ℕ) (ω : ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i k=>(newton ω k.val).eval (ω^i.val)
/-- The coefficient matrix expressing the Newton basis in the monomial basis. -/
def P (n : ℕ) (ω : ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i k=>(newton ω k.val).coeff i.val

@[simp] theorem newton_zero (ω : ℂ) : newton ω 0=1 := by simp [newton]
theorem newton_succ (ω : ℂ) (k : ℕ) : newton ω (k+1)=newton ω k*(X-C (ω^k)) := by
 simp [newton,Finset.prod_range_succ]
@[simp] theorem H_zero (ω : ℂ) : H ω 0=1 := by simp [H]
theorem H_succ (ω : ℂ) (i : ℕ) : H ω (i+1)=H ω i*(1-ω^(i+1)) := by simp [H,Finset.prod_range_succ]
@[simp] theorem scale_zero (ω : ℂ) : scale ω 0=1 := by simp [scale]
theorem scale_succ (ω : ℂ) (k : ℕ) : scale ω (k+1)=scale ω k*(-ω^k) := by
  simp [scale,Finset.prod_range_succ]

theorem newton_monic (ω : ℂ) (k : ℕ) : (newton ω k).Monic := monic_prod_X_sub_C _ _
@[simp] theorem newton_natDegree (ω : ℂ) (k : ℕ) : (newton ω k).natDegree=k := by
 induction k with
 | zero => simp
 | succ k ih =>
   rw [newton_succ,natDegree_mul (newton_monic ω k).ne_zero (monic_X_sub_C
     _).ne_zero,ih,natDegree_X_sub_C]

theorem newton_eval_zero (ω : ℂ) (i k : ℕ) (h : i < k) : (newton ω k).eval (ω^i)=0 := by
 simp only [newton,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
 exact Finset.prod_eq_zero (Finset.mem_range.mpr h) (sub_self _)

theorem eval_factor (ω : ℂ) (i k : ℕ) (hki : k ≤ i) :
 (newton ω k).eval (ω^i)*H ω (i-k)=scale ω k*H ω i := by
 induction k with
 | zero => simp
 | succ k ih =>
  have hik : k ≤ i := by omega
  have hs : i-k=(i-(k+1))+1 := by omega
  have hpow : ω^i=ω^k*ω^(i-k) := by rw [← pow_add,Nat.add_sub_of_le hik]
  have hh := ih hik
  rw [hs,H_succ] at hh
  rw [newton_succ,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    scale_succ]
  rw [hpow,hs]
  rw [hpow,hs] at hh
  linear_combination (-ω^k)*hh

theorem H_ne_zero {ω : ℂ} {n : ℕ} (hω : IsPrimitiveRoot ω n) {i : ℕ} (hi : i < n) : H ω i ≠ 0 := by
 apply Finset.prod_ne_zero_iff.mpr
 intro j hj
 apply sub_ne_zero.mpr
 have hjlt := Finset.mem_range.mp hj
 exact (hω.pow_ne_one_of_pos_of_lt (by lia : j+1 ≠ 0) (by lia)).symm

theorem scale_ne_zero {ω : ℂ} (hω : ω ≠ 0) (k : ℕ) : scale ω k ≠ 0 := by
 apply Finset.prod_ne_zero_iff.mpr
 intro j hj
 exact neg_ne_zero.mpr (pow_ne_zero j hω)

theorem N_lower (n : ℕ) (ω : ℂ) : (N n ω).IsLowerTriangular := by
 intro i j hij
 exact newton_eval_zero ω i.val j.val hij

theorem P_upper (n : ℕ) (ω : ℂ) : (P n ω).IsUpperTriangular := by
 intro i j hij
 exact coeff_eq_zero_of_natDegree_lt (by simpa using hij)

theorem dft_mul_P (n : ℕ) (ω : ℂ) : RadixTwo.dft n ω * P n ω=N n ω := by
 have hh := Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
  (fun i : Fin n=>ω^i.val) (fun k : Fin n=>newton ω k.val) (fun k=>by simp)
 have he : Matrix.vandermonde (fun i : Fin n=>ω^i.val)=RadixTwo.dft n ω := by
  ext i j; simp [Matrix.vandermonde,RadixTwo.dft,pow_mul]
 rw [he] at hh
 exact hh.symm
end ExactFourier.NewtonFourier

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem inverse {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : Layered M⁻¹ d := by
 induction h with
 | identity => simpa using (Layered.identity (α := _))
 | mono M hM => exact Layered.mono _ hM.inverse
 | pair M hM => exact Layered.pair _ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
 | mul hM hN ihM ihN =>
  rw [Matrix.mul_inv_rev]
  simpa only [Nat.add_comm] using ihN.mul ihM
 | reindex f hM ih =>
  rw [MatrixSymmetry.inverse_reindex f _ hM.unit]
  exact ih.reindex f
 | sum hM hN ihM ihN =>
  rw [MatrixSymmetry.inverse_sum _ _ hM.unit hN.unit]
  exact ihM.sum ihN
 | weaken h hde ih => exact ih.weaken hde

theorem conjugate {M N : Matrix α α ℂ} {d e : ℕ} (hM : Layered M d) (hN : Layered N e) :
 Layered (M*N*M⁻¹) (2*d+e) := by
 simpa only [show d+e+d=2*d+e by omega] using (hM.mul hN).mul hM.inverse
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem rect_diagonal (c : α→ℂ) : Layered (rectangularShear (Matrix.diagonal c)) 1 := by
 let M := fun i : α=>(!![1,c i;0,1] : Matrix (Fin 2) (Fin 2) ℂ)
 have hm : ∀ i,IsUnit (M i) := by
  intro i
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit ((!![1,c i;0,1] : Matrix (Fin 2) (Fin 2) ℂ).det)
  simp
 have h := (blockDiagonal M 1 (fun i=>Layered.pair (M i) (hm i))).reindex (twoProdEquiv α)
 have he : Matrix.reindex (twoProdEquiv α) (twoProdEquiv α) (Matrix.blockDiagonal M)=
  rectangularShear (Matrix.diagonal c) := by
  ext i j
  cases i <;> cases j <;>
   simp [twoProdEquiv,Matrix.reindex_apply,Matrix.blockDiagonal,M,rectangularShear,
     Matrix.one_apply,Matrix.diagonal_apply]
 rw [he] at h
 exact h

theorem rect_add {G H : Matrix α β ℂ} {d e : ℕ}
 (hG : Layered (rectangularShear G) d) (hH : Layered (rectangularShear H) e) :
 Layered (rectangularShear (G+H)) (d+e) := by
 rw [← rectangularShear_mul]
 exact hG.mul hH

theorem rect_neg {G : Matrix α β ℂ} {d : ℕ}
 (hG : Layered (rectangularShear G) d) : Layered (rectangularShear (-G)) d := by
 rw [← rectangularShear_inv]
 exact hG.inverse

theorem rect_mul_left {M : Matrix α α ℂ} {G : Matrix α β ℂ} {d e : ℕ}
 (hM : Layered M d) (hG : Layered (rectangularShear G) e) :
 Layered (rectangularShear (M*G)) (2*d+e) := by
 have h := (hM.sum (identity.weaken (Nat.zero_le d))).conjugate hG
 have he : Matrix.fromBlocks M 0 0 (1 : Matrix β β ℂ) * rectangularShear G *
  (Matrix.fromBlocks M 0 0 (1 : Matrix β β ℂ))⁻¹=rectangularShear (M*G) := by
  rw [MatrixSymmetry.inverse_sum _ _ hM.unit isUnit_one]
  simp [rectangularShear,Matrix.fromBlocks_multiply,Matrix.mul_nonsing_inv _
    (Matrix.isUnit_iff_isUnit_det _ |>.mp hM.unit)]
 rw [he] at h
 exact h

theorem rect_mul_right {M : Matrix β β ℂ} {G : Matrix α β ℂ} {d e : ℕ}
 (hM : Layered M d) (hG : Layered (rectangularShear G) e) :
 Layered (rectangularShear (G*M)) (2*d+e) := by
 let := hM.unit.invertible
 have h := ((identity.weaken (Nat.zero_le d)).sum hM.inverse).conjugate hG
 have he : Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 M⁻¹ * rectangularShear G *
  (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 M⁻¹)⁻¹=rectangularShear (G*M) := by
  rw [MatrixSymmetry.inverse_sum _ _ isUnit_one hM.inverse.unit,Matrix.inv_inv_of_invertible]
  simp [rectangularShear,Matrix.fromBlocks_multiply,Matrix.nonsing_inv_mul _
    (Matrix.isUnit_iff_isUnit_det _ |>.mp hM.unit)]
 rw [he] at h
 exact h
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Reassociate three coordinate blocks and exchange the last two. -/
def swapLast : ((α⊕γ)⊕β)≃(α⊕(β⊕γ)) :=
 (Equiv.sumAssoc α γ β).trans (Equiv.sumCongr (Equiv.refl α) (Equiv.sumComm γ β))

theorem rect_first
    {α : Type} {β : Type} {γ : Type}    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (G :
      Matrix α β ℂ) :
 Matrix.reindex (Equiv.sumAssoc α β γ) (Equiv.sumAssoc α β γ)
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix γ γ ℂ)) =
 rectangularShear (Matrix.fromCols G (0 : Matrix α γ ℂ)) := by
 ext i j
 rcases i with i|(i|i) <;> rcases j with j|(j|j) <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply]

theorem rect_last
    {α : Type} {β : Type} {γ : Type}    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (G :
      Matrix α γ ℂ) :
 Matrix.reindex (swapLast (α := α) (β := β) (γ := γ)) (swapLast (α := α) (β := β) (γ := γ))
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix β β ℂ)) =
 rectangularShear (Matrix.fromCols (0 : Matrix α β ℂ) G) := by
 ext i j
 rcases i with i|(i|i) <;> rcases j with j|(j|j) <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,swapLast]

theorem commutator_identity (G : Matrix α β ℂ) (H : Matrix β γ ℂ) :
 rectangularShear (Matrix.fromCols G (0 : Matrix α γ ℂ)) *
 Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 (rectangularShear H) *
 rectangularShear (Matrix.fromCols (-G) (0 : Matrix α γ ℂ)) *
 Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 (rectangularShear (-H)) =
 rectangularShear (Matrix.fromCols (0 : Matrix α β ℂ) (G*H)) := by
 simp only [rectangularShear,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.one_mul,
  Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
 ext i j
 rcases i with i|(i|i) <;> rcases j with j|(j|j) <;>
  simp [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply,Finset.sum_add_distrib,
    Finset.sum_neg_distrib,add_mul]

theorem rect_product_stable {G : Matrix α β ℂ} {H : Matrix β γ ℂ} {d e : ℕ}
 (hG : Layered (rectangularShear G) d) (hH : Layered (rectangularShear H) e) :
 Layered (Matrix.fromBlocks (rectangularShear (G*H)) 0 0 (1 : Matrix β β ℂ)) (2*(d+e)) := by
 have hu := (hG.sum (identity.weaken (Nat.zero_le d))).reindex (Equiv.sumAssoc α β γ)
 rw [rect_first] at hu
 have hun := (hG.rect_neg.sum (identity.weaken (Nat.zero_le d))).reindex (Equiv.sumAssoc α β γ)
 rw [rect_first] at hun
 have hv := (identity.weaken (Nat.zero_le e) (α := α)).sum hH
 have hvn := (identity.weaken (Nat.zero_le e) (α := α)).sum hH.rect_neg
 have ht := ((hu.mul hv).mul hun).mul hvn
 rw [commutator_identity,←rect_last] at ht
 have hs := ht.reindex (swapLast (α := α) (β := β) (γ := γ)).symm
 simpa only [reindex_inverse,
  show d+e+d+e=2*(d+e) by omega] using hs
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem rect_transpose {G : Matrix α β ℂ} {d : ℕ}
 (hG : Layered (rectangularShear G) d) : Layered (rectangularShear G.transpose) d := by
 have h := hG.transpose.reindex (Equiv.sumComm α β)
 have he : Matrix.reindex (Equiv.sumComm α β) (Equiv.sumComm α β)
  (rectangularShear G).transpose=rectangularShear G.transpose := by
  ext i j
  cases i <;> cases j <;> simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,eq_comm]
 rw [he] at h
 exact h

omit [Fintype α] in
theorem embedded_injection (e : β↪α) :
 Embedded.matrix (e.sumMap (Function.Embedding.refl β))
 (rectangularShear (1 : Matrix β β ℂ)) =
 rectangularShear ((1 : Matrix α α ℂ).submatrix id e) := by
 classical
 let f := e.sumMap (Function.Embedding.refl β)
 have ho (i : α) (hi : i∉Set.range e) : (Sum.inl i : α⊕β)∉Set.range f := by
  rintro ⟨a,h⟩; cases a with
  | inl a => exact hi ⟨a,Sum.inl.inj h⟩
  | inr a => cases h
 ext i j
 rcases i with i|i <;> rcases j with j|j
 · by_cases hi : i∈Set.range e
   · obtain ⟨i,rfl⟩ := hi
     by_cases hj : j∈Set.range e
     · obtain ⟨j,rfl⟩ := hj
       change Embedded.matrix f _ (f (.inl i)) (f (.inl j))=_
       rw [Embedded.matrix_on]
       simp [rectangularShear,Matrix.one_apply,e.injective.eq_iff]
     · rw [Embedded.matrix_off_col f _ _ _ (ho j hj)]
       simp [rectangularShear,Matrix.one_apply]
   · rw [Embedded.matrix_off_row f _ _ _ (ho i hi)]
     simp [rectangularShear,Matrix.one_apply]
 · by_cases hi : i∈Set.range e
   · obtain ⟨i,rfl⟩ := hi
     change Embedded.matrix f _ (f (.inl i)) (f (.inr j))=_
     rw [Embedded.matrix_on]
     simp [rectangularShear,Matrix.one_apply,e.injective.eq_iff]
   · rw [Embedded.matrix_off_row f _ _ _ (ho i hi)]
     have hn : i≠e j := fun h=>hi ⟨j,h.symm⟩
     simp [rectangularShear,hn]
 · by_cases hj : j∈Set.range e
   · obtain ⟨j,rfl⟩ := hj
     change Embedded.matrix f _ (f (.inr i)) (f (.inl j))=_
     rw [Embedded.matrix_on]
     simp [rectangularShear]
   · rw [Embedded.matrix_off_col f _ _ _ (ho j hj)]
     simp [rectangularShear]
 · change Embedded.matrix f _ (f (.inr i)) (f (.inr j))=_
   rw [Embedded.matrix_on]
   simp [rectangularShear]

theorem rect_injection (e : β↪α) : Layered (rectangularShear ((1 : Matrix α α ℂ).submatrix id
    e)) 1 := by
 rw [← embedded_injection e]
 have h := rect_diagonal (fun _ : β=>(1 : ℂ))
 rw [Matrix.diagonal_one] at h
 exact h.embed _

theorem rect_projection (e : β↪α) : Layered (rectangularShear ((1 : Matrix α α ℂ).submatrix e
    id)) 1 := by
 simpa [Matrix.transpose_submatrix] using (rect_injection e).rect_transpose

theorem rect_submatrix_stable {M : Matrix γ γ ℂ} {d : ℕ}
 (hM : Layered M d) (e : α↪γ) (f : β↪γ) :
 Layered (Matrix.fromBlocks (rectangularShear (M.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ)) (4*d+4)
   := by
 have hG := hM.rect_mul_right (rect_projection e)
 have h := hG.rect_product_stable (rect_injection f)
 have he : ((1 : Matrix γ γ ℂ).submatrix e id * M) * (1 : Matrix γ γ ℂ).submatrix id
   f=M.submatrix e f := by
  ext i j
  simp [Matrix.mul_apply,Matrix.one_apply]
 rw [he] at h
 simpa only [show 2*(2*d+1+1)=4*d+4 by omega] using h
end ExactFourier.Layered

end
end

end Complexity
