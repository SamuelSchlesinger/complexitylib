/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.MatrixRelabel

/-!
# Exact Fourier circuits: rect stable algebra

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/RectStableAlgebra.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ σ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq σ]

theorem stable_rect_add {G H : Matrix α β ℂ} {d e : ℕ}
 (hG : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d)
 (hH : Layered (Matrix.fromBlocks (rectangularShear H) 0 0 (1 : Matrix σ σ ℂ)) e) :
 Layered (Matrix.fromBlocks (rectangularShear (G+H)) 0 0 (1 : Matrix σ σ ℂ)) (d+e) := by
 have h := hG.mul hH
 simpa [Matrix.fromBlocks_multiply,rectangularShear_mul] using h

theorem stable_rect_transpose {G : Matrix α β ℂ} {d : ℕ}
 (hG : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d) :
 Layered (Matrix.fromBlocks (rectangularShear G.transpose) 0 0 (1 : Matrix σ σ ℂ)) d := by
 have h := hG.transpose.reindex ((Equiv.sumComm α β).sumCongr (Equiv.refl σ))
 have he : Matrix.reindex ((Equiv.sumComm α β).sumCongr (Equiv.refl σ))
   ((Equiv.sumComm α β).sumCongr (Equiv.refl σ))
   (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)).transpose=
   Matrix.fromBlocks (rectangularShear G.transpose) 0 0 (1 : Matrix σ σ ℂ) := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,eq_comm]
 rw [he] at h
 exact h

/-- Regroup four coordinate blocks to put the two data blocks first. -/
def splitRowsLeft : ((α⊕γ)⊕(β⊕σ))≃(((α⊕β)⊕γ)⊕σ) where
 toFun := fun x=>match x with
  | .inl (.inl a)=>.inl (.inl (.inl a))
  | .inl (.inr c)=>.inl (.inr c)
  | .inr (.inl b)=>.inl (.inl (.inr b))
  | .inr (.inr s)=>.inr s
 invFun := fun x=>match x with
  | .inl (.inl (.inl a))=>.inl (.inl a)
  | .inl (.inl (.inr b))=>.inr (.inl b)
  | .inl (.inr c)=>.inl (.inr c)
  | .inr s=>.inr (.inr s)
 left_inv := by rintro ((a|c)|(b|s)) <;> rfl
 right_inv := by rintro (((a|b)|c)|s) <;> rfl

/-- Regroup four coordinate blocks and restore the common order of the data blocks. -/
def splitRowsRight : ((β⊕γ)⊕(α⊕σ))≃(((α⊕β)⊕γ)⊕σ) :=
 (splitRowsLeft (α := β) (β := α) (γ := γ) (σ := σ)).trans
 (((Equiv.sumComm β α).sumCongr (Equiv.refl γ)).sumCongr (Equiv.refl σ))

theorem split_rows_left_matrix
    {α : Type} {β : Type} {γ : Type} {σ : Type}     [DecidableEq α] [DecidableEq β] [DecidableEq
      γ] [DecidableEq σ] (G : Matrix α γ ℂ) :
 Matrix.reindex (splitRowsLeft (β := β) (σ := σ)) (splitRowsLeft (β := β) (σ := σ))
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (β⊕σ) (β⊕σ) ℂ))=
 Matrix.fromBlocks (rectangularShear (Matrix.fromRows G (0 : Matrix β γ ℂ))) 0 0 (1 : Matrix σ σ
   ℂ) := by
 ext i j
 rcases i with ((i|i)|i)|i <;> rcases j with ((j|j)|j)|j <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,splitRowsLeft]

theorem split_rows_right_matrix
    {α : Type} {β : Type} {γ : Type} {σ : Type}     [DecidableEq α] [DecidableEq β] [DecidableEq
      γ] [DecidableEq σ] (H : Matrix β γ ℂ) :
 Matrix.reindex (splitRowsRight (α := α) (σ := σ)) (splitRowsRight (α := α) (σ := σ))
  (Matrix.fromBlocks (rectangularShear H) 0 0 (1 : Matrix (α⊕σ) (α⊕σ) ℂ))=
 Matrix.fromBlocks (rectangularShear (Matrix.fromRows (0 : Matrix α γ ℂ) H)) 0 0 (1 : Matrix σ σ
   ℂ) := by
 ext i j
 rcases i with ((i|i)|i)|i <;> rcases j with ((j|j)|j)|j <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,splitRowsLeft,splitRowsRight]

theorem stable_rect_split_rows {G : Matrix α γ ℂ} {H : Matrix β γ ℂ} {d e : ℕ}
 (hG : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (β⊕σ) (β⊕σ) ℂ)) d)
 (hH : Layered (Matrix.fromBlocks (rectangularShear H) 0 0 (1 : Matrix (α⊕σ) (α⊕σ) ℂ)) e) :
 Layered (Matrix.fromBlocks (rectangularShear (Matrix.fromRows G H)) 0 0 (1 : Matrix σ σ ℂ))
   (d+e) := by
 have h1 := hG.reindex (splitRowsLeft (β := β) (σ := σ))
 have h2 := hH.reindex (splitRowsRight (α := α) (σ := σ))
 rw [split_rows_left_matrix] at h1
 rw [split_rows_right_matrix] at h2
 have h := h1.stable_rect_add h2
 have he : Matrix.fromRows G (0 : Matrix β γ ℂ)+Matrix.fromRows (0 : Matrix α γ ℂ) H=
  Matrix.fromRows G H := by ext i j; cases i <;> simp
 rw [he] at h
 exact h
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β σ τ α' β' σ' : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype τ]
 [Fintype α'] [Fintype β'] [Fintype σ']
 [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq τ]
 [DecidableEq α'] [DecidableEq β'] [DecidableEq σ']

theorem stable_reindex {G : Matrix α β ℂ} {d : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d)
 (e : α≃α') (f : β≃β') (g : σ≃σ') :
 Layered (Matrix.fromBlocks (rectangularShear (Matrix.reindex e f G)) 0 0 (1 : Matrix σ' σ' ℂ))
   d := by
 have hh := h.reindex ((e.sumCongr f).sumCongr g)
 have he : Matrix.reindex ((e.sumCongr f).sumCongr g) ((e.sumCongr f).sumCongr g)
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ))=
  Matrix.fromBlocks (rectangularShear (Matrix.reindex e f G)) 0 0 (1 : Matrix σ' σ' ℂ) := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
   simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply]
 rw [he] at hh
 exact hh

theorem stable_extra {G : Matrix α β ℂ} {d : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (σ⊕τ) (σ⊕τ) ℂ)) d := by
 have hh := (h.sum (identity.weaken (Nat.zero_le d))).reindex (Equiv.sumAssoc (α⊕β) σ τ)
 have he : Matrix.reindex (Equiv.sumAssoc (α⊕β) σ τ) (Equiv.sumAssoc (α⊕β) σ τ)
  (Matrix.fromBlocks (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) 0 0
   (1 : Matrix τ τ ℂ))=Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (σ⊕τ) (σ⊕τ) ℂ) := by
  ext i j
  rcases i with i|i|i <;> rcases j with j|j|j <;>
   simp [Matrix.reindex_apply,Matrix.one_apply]
 rw [he] at hh
 exact hh

theorem stable_scratch_mono {G : Matrix α β ℂ} {d s t : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) d)
 (hst : s≤t) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin t) (Fin t) ℂ)) d := by
 have hh := (h.stable_extra (τ := Fin (t-s))).stable_reindex (Equiv.refl α) (Equiv.refl β)
  (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hst)))
 simpa using hh

theorem stable_zero {G : Matrix α β ℂ} {d : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin 0) (Fin 0) ℂ)) d) :
 Layered (rectangularShear G) d := by
 have hh := h.reindex (Equiv.sumEmpty (α⊕β) (Fin 0))
 have he : Matrix.reindex (Equiv.sumEmpty (α⊕β) (Fin 0)) (Equiv.sumEmpty (α⊕β) (Fin 0))
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin 0) (Fin 0) ℂ))=rectangularShear G
    := by
  ext i j; rfl
 rw [he] at hh
 exact hh

theorem stable_empty_rows (G : Matrix (Fin 0) β ℂ) (d : ℕ) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d := by
 have he : Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)=1 := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [rectangularShear,Matrix.one_apply] ; exact Fin.elim0 ‹Fin 0›
 rw [he]
 exact identity.weaken (Nat.zero_le d)

theorem stable_empty_cols (G : Matrix α (Fin 0) ℂ) (d : ℕ) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d := by
 exact (stable_empty_rows G.transpose d (σ := σ)).stable_rect_transpose

theorem stable_rows_nat {a b e s d f : ℕ} (M : ℕ→ℕ→ℂ)
 (hG : Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin (b+s)) (Fin (b+s)) ℂ)) d)
 (hH : Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin b=>fun j : Fin e=>M (a+i.val)
   j.val))
  0 0 (1 : Matrix (Fin (a+s)) (Fin (a+s)) ℂ)) f) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin (a+b)=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (d+f) := by
 have h1 := hG.stable_reindex (Equiv.refl _) (Equiv.refl _) finSumFinEquiv.symm
 have h2 := hH.stable_reindex (Equiv.refl _) (Equiv.refl _) finSumFinEquiv.symm
 change Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin b⊕Fin s) (Fin b⊕Fin s) ℂ)) d at h1
 change Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin b=>fun j : Fin e=>M (a+i.val)
   j.val))
  0 0 (1 : Matrix (Fin a⊕Fin s) (Fin a⊕Fin s) ℂ)) f at h2
 have hh := (h1.stable_rect_split_rows h2).stable_reindex finSumFinEquiv (Equiv.refl _)
   (Equiv.refl _)
 have he : Matrix.reindex finSumFinEquiv (Equiv.refl (Fin e))
  (Matrix.fromRows (fun i : Fin a=>fun j : Fin e=>M i.val j.val)
   (fun i : Fin b=>fun j : Fin e=>M (a+i.val) j.val))=
  (fun i : Fin (a+b)=>fun j : Fin e=>M i.val j.val) := by
  ext i j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [Matrix.reindex_apply,Matrix.fromRows]
 rw [he] at hh
 exact hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- A sum of at most `c` matrices, each realizable in `d` parallel layers. -/
def SumLayered (M : Matrix α α ℂ) (d c : ℕ) : Prop :=
 ∃ L : List (Matrix α α ℂ), L.length≤c ∧ L.sum=M ∧ ∀ N∈L,Layered N d

namespace SumLayered
 theorem single {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : SumLayered M d 1 := by
  exact ⟨[M],by simp,by simp,by simpa⟩
 theorem weaken {M : Matrix α α ℂ} {d e c f : ℕ} (h : SumLayered M d c)
  (hde : d≤e) (hcf : c≤f) : SumLayered M e f := by
  obtain ⟨L,hL,he,hd⟩ := h
  exact ⟨L,hL.trans hcf,he,fun N hn=>(hd N hn).weaken hde⟩
 theorem add {M N : Matrix α α ℂ} {d c e : ℕ} (hM : SumLayered M d c) (hN : SumLayered N d e) :
  SumLayered (M+N) d (c+e) := by
  obtain ⟨L,hL,rfl,hd⟩ := hM
  obtain ⟨K,hK,rfl,he⟩ := hN
  refine ⟨L++K, ?_,by simp,?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hL hK
  · intro M h; rcases List.mem_append.mp h with h|h
    · exact hd M h
    · exact he M h
 theorem transpose {M : Matrix α α ℂ} {d c : ℕ} (hM : SumLayered M d c) :
  SumLayered M.transpose d c := by
  obtain ⟨L,hL,rfl,hd⟩ := hM
  refine ⟨L.map Matrix.transpose,by simpa using hL,?_,?_⟩
  · clear hL hd
    induction L with
    | nil => simp
    | cons A L ih => simp [ih,Matrix.transpose_add]
  · intro M h; obtain ⟨N,hN,rfl⟩:=List.mem_map.mp h
    exact (hd N hN).transpose
 theorem mul {M N : Matrix α α ℂ} {d e c f : ℕ} (hM : SumLayered M d c) (hN : SumLayered N e f) :
  SumLayered (M*N) (d+e) (c*f) := by
  obtain ⟨L,hL,rfl,hd⟩ := hM
  obtain ⟨K,hK,rfl,he⟩ := hN
  let P := L.flatMap (fun A=>K.map (fun B=>A*B))
  have hlen : P.length=L.length*K.length := by
   dsimp [P]; induction L with
   | nil => simp
   | cons A L ih => simp [Nat.add_mul,Nat.add_comm]
  refine ⟨P,hlen.le.trans (Nat.mul_le_mul hL hK),?_,?_⟩
  · dsimp [P]
    clear hL hd hlen P hK he
    have hm (A : Matrix α α ℂ) : (K.map (fun B=>A*B)).sum=A*K.sum := by
     induction K with
     | nil => simp
     | cons B K ih => simp_all [mul_add]
    induction L with
    | nil => simp
    | cons A L ih => simp [ih,hm,add_mul]
  · intro M h
    obtain ⟨A,hA,h⟩:=List.mem_flatMap.mp h
    obtain ⟨B,hB,rfl⟩:=List.mem_map.mp h
    exact (hd A hA).mul (he B hB)

 theorem diagonal (c : α→ℂ) : SumLayered (Matrix.diagonal c) 1 2 := by
  classical
  obtain ⟨lam,hlam⟩ := Infinite.exists_notMem_finset (insert 0 (Finset.univ.image c))
  simp only [Finset.mem_insert,not_or] at hlam
  have h0 : lam≠0 := hlam.1
  have hc : ∀ i,c i-lam≠0 := by
   intro i h; apply hlam.2
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,sub_eq_zero.mp h⟩
  let A := Matrix.diagonal (fun i=>c i-lam)
  let B := Matrix.diagonal (fun _ : α=>lam)
  have he : A+B=Matrix.diagonal c := by ext i j; by_cases h : i=j <;> simp [A,B,h]
  rw [←he]
  exact (single (Layered.mono A (MonomialMatrix.diagonal _ hc))).add
    (single (Layered.mono B (MonomialMatrix.diagonal _ (fun _=>h0))))

 theorem submatrix_stable {M : Matrix γ γ ℂ} {d c : ℕ} (hM : SumLayered M d c)
  (e : α↪γ) (f : β↪γ) :
  Layered (Matrix.fromBlocks (rectangularShear (M.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ))
    (c*(4*d+4)) := by
  obtain ⟨L,hL,rfl,hd⟩:=hM
  have hh : ∀ L : List (Matrix γ γ ℂ), (∀ M∈L,Layered M d) →
   Layered (Matrix.fromBlocks (rectangularShear (L.sum.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ))
     (L.length*(4*d+4)) := by
   intro L h
   induction L with
   | nil =>
    simpa [rectangularShear] using (Layered.identity (α := (α⊕β)⊕γ))
   | cons M L ih =>
    have hM := (h M (by simp)).rect_submatrix_stable e f
    have hL := ih (fun N hn=>h N (by simp [hn]))
    have ht := hM.mul hL
    have he : Matrix.fromBlocks (rectangularShear (M.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ) *
      Matrix.fromBlocks (rectangularShear (L.sum.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ)=
      Matrix.fromBlocks (rectangularShear ((M+L.sum).submatrix e f)) 0 0 (1 : Matrix γ γ ℂ) := by
     simp [Matrix.fromBlocks_multiply,rectangularShear_mul,Matrix.submatrix_add]
    rw [he] at ht
    simpa [Nat.add_mul,Nat.add_comm] using ht
  exact (hh L hd).weaken (Nat.mul_le_mul_right _ hL)
end SumLayered
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.RadixTwo
open Polynomial
open scoped BigOperators

/-- Cyclic convolution expressed as inverse Fourier, diagonal scaling, and Fourier factors. -/
def convolutionMatrix (k : ℕ) (f : ℂ[X]) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
 let ω := zeta (2^k)
 dft (2^k) ω⁻¹ * Matrix.diagonal (fun i=>((2^k : ℕ) : ℂ)⁻¹*f.eval (ω^i.val)) * dft (2^k) ω

theorem convolution_sumLayered (k : ℕ) (f : ℂ[X]) : SumLayered (convolutionMatrix k f) (4*k+1) 2
    := by
 have hω : IsPrimitiveRoot (zeta (2^k)) (2^k) := Complex.isPrimitiveRoot_exp _ (by positivity)
 have h := ((SumLayered.single (dft_layers k _ hω.inv)).mul
  (SumLayered.diagonal (fun i : Fin (2^k)=>((2^k : ℕ) : ℂ)⁻¹*f.eval ((zeta (2^k))^i.val)))).mul
  (SumLayered.single (dft_layers k _ hω))
 simpa only [convolutionMatrix,show 2*k+1+2*k=4*k+1 by omega, Nat.one_mul,Nat.mul_one] using h

theorem convolution_mulVec (k : ℕ) (f : ℂ[X]) (x : Fin (2^k)→ℂ)
 (hx : (f*Polynomial.ofFn (2^k) x).natDegree < 2^k) :
 (convolutionMatrix k f).mulVec x =fun i=>(f*Polynomial.ofFn (2^k) x).coeff i.val := by
 have hω : IsPrimitiveRoot (zeta (2^k)) (2^k) := Complex.isPrimitiveRoot_exp _ (by positivity)
 have h := convolution_formula (by positivity : 0 < 2^k) _ hω f (Polynomial.ofFn (2^k) x) hx
 change eval (2^k) (zeta (2^k))⁻¹ _ = _ at h
 dsimp only [convolutionMatrix]
 rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
 change eval (2^k) (zeta (2^k))⁻¹ _=_
 rw [←h]
 congr 1
 funext i
 rw [Matrix.mulVec_diagonal]
 change _*eval (2^k) (zeta (2^k)) x i=_
 rw [eval_ofFn]

theorem ofFn_single {n : ℕ} (j : Fin n) :
 Polynomial.ofFn n (Pi.single j (1 : ℂ))=Polynomial.monomial j.val 1 := by
 ext i
 by_cases hi : i < n
 · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
   simp [Polynomial.coeff_monomial,Pi.single_apply,Fin.ext_iff,eq_comm]
 · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
   have hn : j.val≠i := by have := j.isLt; omega
   simp [Polynomial.coeff_monomial,hn]

theorem convolution_entry (k : ℕ) (f : ℂ[X]) (i j : Fin (2^k))
 (hj : f.natDegree+j.val < 2^k) :
 convolutionMatrix k f i j=if j.val ≤ i.val then f.coeff (i.val-j.val) else 0 := by
 have hx : (f*Polynomial.ofFn (2^k) (Pi.single j (1 : ℂ))).natDegree < 2^k := by
  rw [ofFn_single]
  exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left
    (Polynomial.natDegree_monomial_le (1 : ℂ)) _)).trans_lt hj
 have h := congrFun (convolution_mulVec k f (Pi.single j 1) hx) i
 rw [Matrix.mulVec_single_one,ofFn_single] at h
 change convolutionMatrix k f i j = _ at h
 rw [h]
 rw [Polynomial.monomial_one_right_eq_X_pow,Polynomial.coeff_mul_X_pow']
end ExactFourier.RadixTwo

end
end

section
noncomputable section
namespace ExactFourier
open scoped BigOperators

/-- Embed an initial finite interval into a larger one without changing index values. -/
def initialEmbedding {a n : ℕ} (h : a≤n) : Fin a↪Fin n :=
 ⟨fun i=>⟨i.val,lt_of_lt_of_le i.isLt h⟩,by intro i j he; exact Fin.ext (congrArg (fun x : Fin
   n=>x.val) he)⟩

@[simp] theorem initialEmbedding_val {a n : ℕ} (h : a≤n) (i : Fin a) :
 (initialEmbedding h i).val=i.val := rfl

theorem sum_initial {a n : ℕ} (h : a≤n) (f : Fin n→ℂ) :
 (∑i : Fin n,if i.val<a then f i else 0)=∑i : Fin a,f (initialEmbedding h i) := by
 classical
 let e:=initialEmbedding h
 have hi : Function.Injective e:=e.injective
 have hr : ∀ j : Fin n,j∈Finset.univ.image e ↔ j.val<a := by
  intro j
  constructor
  · intro hj; obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj; exact i.isLt
  · intro hj; exact Finset.mem_image.mpr ⟨⟨j.val,hj⟩,Finset.mem_univ _,rfl⟩
 rw [←Finset.sum_image (fun i _ j _ he=>hi he)]
 rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
 · apply Finset.sum_congr rfl
   intro j hj
   rw [ite_eq_left ((hr j).mp hj)]
 · intro j hj hn
   rw [ite_eq_right (mt ((hr j).mpr) hn)]

theorem compress_product {a b e n : ℕ} (ha : a≤n) (hb : b≤n) (he : e≤n)
 (M N : Matrix (Fin n) (Fin n) ℂ) :
 (M * Matrix.diagonal (fun i : Fin n=>if i.val<e then (1 : ℂ) else 0) * N).submatrix
  (initialEmbedding ha) (initialEmbedding hb)=
 (M.submatrix (initialEmbedding ha) (initialEmbedding he)) *
 (N.submatrix (initialEmbedding he) (initialEmbedding hb)) := by
 ext i j
 rw [Matrix.submatrix_apply,Matrix.mul_apply]
 simp only [Matrix.mul_diagonal]
 have h := sum_initial he (fun l=>M (initialEmbedding ha i) l*N l (initialEmbedding hb j))
 simpa [Matrix.mul_apply,Matrix.submatrix_apply,ite_mul,mul_ite] using h
end ExactFourier

end
end

end Complexity
