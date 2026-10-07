/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.MonomialFeedback

/-!
# Exact Fourier circuits: monomial tools

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/MonomialTools.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier.MonomialMatrix
open scoped Kronecker
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem mul {A B : Matrix α α ℂ} (hA : MonomialMatrix A) (hB : MonomialMatrix B) :
    MonomialMatrix (A*B) := by
  classical
  obtain ⟨σ,d,hd,ha⟩ := hA
  obtain ⟨τ,e,he,hb⟩ := hB
  refine ⟨τ.trans σ,fun j => d (τ j)*e j,fun j => mul_ne_zero (hd _) (he _),?_⟩
  intro i j
  rw [Matrix.mul_apply]
  simp_rw [hb,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,ha,Equiv.trans_apply]
  split_ifs <;> simp_all

theorem unit (A : Matrix α α ℂ) (hA : MonomialMatrix A) : IsUnit A := by
  classical
  obtain ⟨σ,d,hd,ha⟩ := hA
  have he : A=(Matrix.diagonal d).submatrix σ.symm (Equiv.refl _) := by
    ext i j
    rw [ha]
    simp only [Matrix.submatrix_apply,Matrix.diagonal_apply,Equiv.refl_apply]
    by_cases h : i=σ j
    · subst i; simp
    · have hj : σ.symm i≠j := by intro hj; apply h; simpa using congrArg σ hj
      simp [h,hj]
  rw [he]
  exact (Matrix.isUnit_submatrix_equiv σ.symm (Equiv.refl _)).mpr
    (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hd i))))

theorem pow {A : Matrix α α ℂ} (hA : MonomialMatrix A) (n : ℕ) : MonomialMatrix (A^n) := by
  induction n with
  | zero => simpa using (one (ι := α))
  | succ n ih => simpa [pow_succ] using ih.mul hA

theorem tensor
    {α : Type} {β : Type}   [DecidableEq α] [DecidableEq β] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : MonomialMatrix A) (hB : MonomialMatrix B) : MonomialMatrix (A⊗ₖB) := by
  obtain ⟨σ,d,hd,ha⟩ := hA
  obtain ⟨τ,e,he,hb⟩ := hB
  refine ⟨σ.prodCongr τ,fun j => d j.1*e j.2,fun j => mul_ne_zero (hd _) (he _),?_⟩
  rintro ⟨i,k⟩ ⟨j,l⟩
  simp only [Matrix.kronecker_apply,ha,hb,Equiv.prodCongr_apply]
  split_ifs <;> simp_all

/-- A direct sum of signed monomials, indexed in (internal,block) order. -/
theorem blockDiagonal
    {α : Type} {β : Type}   [DecidableEq α] [DecidableEq β] (A : β → Matrix α α ℂ) (hA : ∀ b,
      MonomialMatrix (A b)) :
    MonomialMatrix (Matrix.blockDiagonal A) := by
  classical
  choose σ d hd ha using hA
  let e : Equiv.Perm (α×β) :=
    { toFun := fun x => (σ x.2 x.1,x.2)
      invFun := fun x => ((σ x.2).symm x.1,x.2)
      left_inv := by rintro ⟨a,b⟩; simp
      right_inv := by rintro ⟨a,b⟩; simp }
  refine ⟨e,fun j => d j.2 j.1,fun j => hd _ _,?_⟩
  rintro ⟨i,k⟩ ⟨j,l⟩
  by_cases hk : k=l
  · subst l
    simp [Matrix.blockDiagonal_apply,ha,e]
  · simp [Matrix.blockDiagonal_apply,e,hk]

end ExactFourier.MonomialMatrix

end

section
noncomputable section
namespace ExactFourier
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The permutation matrix sending column `j` to row `e j`. -/
def permM (e : Equiv.Perm α) : Matrix α α ℂ := fun i j=>if i=e j then 1 else 0

theorem permM_monomial
    {α : Type}  [DecidableEq α] (e : Equiv.Perm α) : MonomialMatrix (permM e) :=
  ⟨e,fun _=>1,by simp,by intro i j; rfl⟩

theorem permM_mul_apply (e : Equiv.Perm α) (X : Matrix α α ℂ) (i j : α) :
    (permM e*X) i j=X (e.symm i) j := by
  rw [Matrix.mul_apply]
  have he : ∀ k,i=e k ↔ k=e.symm i := by
    intro k
    constructor
    · intro h; simpa using (congrArg e.symm h).symm
    · intro h; simpa using (congrArg e h).symm
  simp only [permM,he,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem mul_permM_apply (e : Equiv.Perm α) (X : Matrix α α ℂ) (i j : α) :
    (X*permM e) i j=X i (e j) := by
  rw [Matrix.mul_apply]
  simp only [permM,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem permM_inv (e : Equiv.Perm α) : (permM e)⁻¹=permM e.symm := by
  apply Matrix.inv_eq_left_inv
  ext i j
  rw [permM_mul_apply]
  simp [permM,Matrix.one_apply]

theorem permM_conj (e : Equiv.Perm α) (X : Matrix α α ℂ) :
    permM e*X*(permM e)⁻¹=X.submatrix e.symm e.symm := by
  rw [permM_inv]
  ext i j
  rw [mul_permM_apply,permM_mul_apply]
  rfl

theorem permM_conj_single (e : Equiv.Perm α) (i j : α) :
    permM e*Matrix.single i j (1:ℂ)*(permM e)⁻¹=Matrix.single (e i) (e j) 1 := by
  rw [permM_conj]
  ext a b
  simp only [Matrix.submatrix_apply,Matrix.single]
  have hi : i=e.symm a ↔ e i=a := e.eq_symm_apply
  have hj : j=e.symm b ↔ e j=b := e.eq_symm_apply
  simp [hi,hj]

theorem exists_perm_pair
    {α : Type}  [DecidableEq α] (i j a b : α) (hij : i≠j) (hab : a≠b) :
    ∃ e : Equiv.Perm α,e i=a ∧ e j=b := by
  let s := Equiv.swap i a
  have hs : s j≠a := by
    have he : s i=a := Equiv.swap_apply_left i a
    rw [← he]
    exact s.injective.ne hij.symm
  let e := s.trans (Equiv.swap (s j) b)
  refine ⟨e,?_,?_⟩
  · change Equiv.swap (s j) b (s i)=a
    rw [show s i=a from Equiv.swap_apply_left i a,Equiv.swap_apply_of_ne_of_ne hs.symm hab]
  · exact Equiv.swap_apply_left (s j) b

end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

@[simp] theorem matrix_coordinates
    {α : Type} {β : Type}     (e : β ↪ α) (A : Matrix β β ℂ)
    (i j : β⊕complement e) :
    matrix e A (coordinates e i) (coordinates e j)=
      Matrix.fromBlocks A 0 0 (1 : Matrix (complement e) (complement e) ℂ) i j := by
  simp [matrix,Matrix.reindex_apply]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
@[simp] theorem matrix_on (e : β ↪ α) (A : Matrix β β ℂ) (i j : β) :
    matrix e A (e i) (e j)=A i j := by
  exact matrix_coordinates e A (Sum.inl i) (Sum.inl j)

omit [Fintype α] [Fintype β] [DecidableEq β] in
theorem matrix_off_row (e : β ↪ α) (A : Matrix β β ℂ) (i j : α)
    (hi : i∉Set.range e) : matrix e A i j=if i=j then 1 else 0 := by
  obtain ⟨j,rfl⟩ := (coordinates e).surjective j
  have he : i=coordinates e (Sum.inr ⟨i,hi⟩) := rfl
  rw [he,matrix_coordinates]
  cases j with
  | inl j =>
    have hn : i≠e j := fun h=>hi ⟨j,h.symm⟩
    simp [hn]
  | inr j => simp [Matrix.one_apply,Subtype.ext_iff] ; rfl

omit [Fintype α] [Fintype β] [DecidableEq β] in
theorem matrix_off_col (e : β ↪ α) (A : Matrix β β ℂ) (i j : α)
    (hj : j∉Set.range e) : matrix e A i j=if i=j then 1 else 0 := by
  obtain ⟨i,rfl⟩ := (coordinates e).surjective i
  have he : j=coordinates e (Sum.inr ⟨j,hj⟩) := rfl
  rw [he,matrix_coordinates]
  cases i with
  | inl i =>
    have hn : e i≠j := fun h=>hj ⟨i,h⟩
    simp [hn]
  | inr i => simp [Matrix.one_apply,Subtype.ext_iff] ; rfl

@[simp] theorem matrix_one (e : β ↪ α) : matrix e (1 : Matrix β β ℂ)=1 := by
  rw [matrix,Matrix.fromBlocks_one]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (coordinates e)).map_one

theorem matrix_mul (e : β ↪ α) (A B : Matrix β β ℂ) :
    matrix e (A*B)=matrix e A*matrix e B := by
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (coordinates e)
  change φ (Matrix.fromBlocks (A*B) 0 0 1)=φ (Matrix.fromBlocks A 0 0 1)*φ (Matrix.fromBlocks B
    0 0 1)
  rw [← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

omit [Fintype α] [DecidableEq γ] in
theorem matrix_comp (e : γ ↪ β) (f : β ↪ α) (A : Matrix γ γ ℂ) :
    matrix f (matrix e A)=matrix (e.trans f) A := by
  classical
  ext i j
  by_cases hi : i∈Set.range f
  · obtain ⟨a,rfl⟩ := hi
    by_cases hj : j∈Set.range f
    · obtain ⟨b,rfl⟩ := hj
      rw [matrix_on]
      by_cases ha : a∈Set.range e
      · obtain ⟨a,rfl⟩ := ha
        by_cases hb : b∈Set.range e
        · obtain ⟨b,rfl⟩ := hb
          exact (matrix_on e A a b).trans (matrix_on (e.trans f) A a b).symm
        · rw [matrix_off_col e A _ _ hb,matrix_off_col (e.trans f) A]
          · simp only [f.injective.eq_iff]
          · rintro ⟨b',hb'⟩; exact hb ⟨b',f.injective hb'⟩
      · rw [matrix_off_row e A _ _ ha,matrix_off_row (e.trans f) A]
        · simp only [f.injective.eq_iff]
        · rintro ⟨a',ha'⟩; exact ha ⟨a',f.injective ha'⟩
    · rw [matrix_off_col f _ _ _ hj,matrix_off_col (e.trans f) A]
      rintro ⟨b,hb⟩; exact hj ⟨e b,hb⟩
  · rw [matrix_off_row f _ _ _ hi,matrix_off_row (e.trans f) A]
    rintro ⟨a,ha⟩; exact hi ⟨e a,ha⟩

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
@[simp] theorem matrix_equiv (e : β≃α) (A : Matrix β β ℂ) :
    matrix e.toEmbedding A=Matrix.reindex e e A := by
  ext i j
  obtain ⟨i,rfl⟩ := e.surjective i
  obtain ⟨j,rfl⟩ := e.surjective j
  change matrix e.toEmbedding A (e.toEmbedding i) (e.toEmbedding j)=_
  rw [matrix_on]
  simp [Matrix.reindex_apply]

end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.MonomialMatrix
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem reindex
    {α : Type} {β : Type}   [DecidableEq α] [DecidableEq β] (e : α≃β) {A : Matrix α α ℂ} (hA :
      MonomialMatrix A) :
    MonomialMatrix (Matrix.reindex e e A) := by
  obtain ⟨s,d,hd,hs⟩ := hA
  refine ⟨e.symm.trans (s.trans e),fun j=>d (e.symm j),fun j=>hd _,?_⟩
  intro i j
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,hs,Equiv.trans_apply]
  have hh : e.symm i=s (e.symm j) ↔ i=e (s (e.symm j)) := e.symm_apply_eq
  simp only [hh]
  rfl

theorem directSum
    {α : Type} {β : Type}   [DecidableEq α] [DecidableEq β] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : MonomialMatrix A) (hB : MonomialMatrix B) :
    MonomialMatrix (Matrix.fromBlocks A 0 0 B) := by
  obtain ⟨s,d,hd,hs⟩ := hA
  obtain ⟨t,e,he,ht⟩ := hB
  refine ⟨s.sumCongr t,Sum.elim d e,?_,?_⟩
  · intro j; cases j <;> simp [hd,he]
  · intro i j; cases i <;> cases j <;> simp [hs,ht]

theorem blockDiagonal' {π : Type}  [DecidableEq π]
    {β : π→Type}  [∀ i,DecidableEq (β i)]
    (A : ∀ i,Matrix (β i) (β i) ℂ) (hA : ∀ i,MonomialMatrix (A i)) :
    MonomialMatrix (Matrix.blockDiagonal' A) := by
  classical
  choose s d hd hs using hA
  refine ⟨Equiv.sigmaCongrRight s,fun j=>d j.1 j.2,fun j=>hd _ _,?_⟩
  rintro ⟨i,a⟩ ⟨j,b⟩
  by_cases h : i=j
  · subst j
    simp [hs]
  · simp [Matrix.blockDiagonal'_apply,h,Equiv.sigmaCongrRight_apply]

omit [Fintype α] [Fintype β] in
theorem embed (e : β ↪ α) {A : Matrix β β ℂ} (hA : MonomialMatrix A) :
    MonomialMatrix (Embedded.matrix e A) :=
  reindex _ (hA.directSum one)

end ExactFourier.MonomialMatrix

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Exact positive pattern: k forward calls, interleaved with arbitrary monomials. -/
inductive Pattern (A : Matrix α α ℂ) : ℕ → Matrix α α ℂ → Prop
  | zero (M) (hM : MonomialMatrix M) : Pattern A 0 M
  | succ {k H} (hH : Pattern A k H) (M) (hM : MonomialMatrix M) : Pattern A (k+1) (H*A*M)

/-- Every nonmonomial invertible matrix generates all invertible matrices at one bounded positive
length. -/
def Statement : Prop := ∀ (A : Matrix α α ℂ),IsUnit A → ¬MonomialMatrix A →
  ∃ h : ℕ,0<h ∧ ∀ H : Matrix α α ℂ,IsUnit H → Pattern A h H

theorem pattern_unit {A H : Matrix α α ℂ} {k : ℕ} (hA : IsUnit A) (h : Pattern A k H) : IsUnit H
    := by
  induction h with
  | zero M hM => exact MonomialMatrix.unit M hM
  | succ h M hM ih => exact (ih.mul hA).mul (MonomialMatrix.unit M hM)

/-- If every column projector is diagonal, the matrix is monomial. -/
theorem monomial_of_projectors (A : Matrix α α ℂ) (hA : IsUnit A)
    (hp : ∀ k i j,i≠j → A i k*A⁻¹ k j=0) : MonomialMatrix A := by
  classical
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hi := Matrix.nonsing_inv_mul A hdet
  have hc : ∀ k,∃ i,A⁻¹ k i*A i k≠0 := by
    intro k
    have he := congrArg (fun M : Matrix α α ℂ=>M k k) hi
    simp only [Matrix.mul_apply,Matrix.one_apply,ite_true] at he
    by_contra hn
    push Not at hn
    rw [Finset.sum_eq_zero (fun i _=>hn i)] at he
    exact zero_ne_one he
  choose σ hσ using hc
  have hc₁ : ∀ k,A⁻¹ k (σ k)≠0 := fun k => (mul_ne_zero_iff.mp (hσ k)).1
  have hc₂ : ∀ k,A (σ k) k≠0 := fun k => (mul_ne_zero_iff.mp (hσ k)).2
  have hz : ∀ k i,i≠σ k → A i k=0 := by
    intro k i hik
    exact (mul_eq_zero.mp (hp k i (σ k) hik)).resolve_right (hc₁ k)
  have he : ∀ i k,A i k=if i=σ k then A (σ k) k else 0 := by
    intro i k; split_ifs with h
    · subst i; rfl
    · exact hz k i h
  have hinj : Function.Injective σ := by
    intro k l hkl
    by_contra hne
    have hh := congrArg (fun M : Matrix α α ℂ=>M k l) hi
    simp only [Matrix.mul_apply,Matrix.one_apply,ite_eq_right hne] at hh
    have hsum : (∑ i,A⁻¹ k i*A i l)=A⁻¹ k (σ l)*A (σ l) l := by
      apply Finset.sum_eq_single (σ l)
      · intro i _ hne; rw [hz l i hne,mul_zero]
      · simp
    rw [hsum] at hh
    apply (mul_ne_zero (hc₁ k) (hc₂ l))
    simpa only [hkl] using hh
  let e : Equiv.Perm α := Equiv.ofBijective σ (⟨hinj,Finite.surjective_of_injective hinj⟩)
  exact ⟨e,fun k=>A (σ k) k,hc₂,he⟩

theorem exists_nondiagonal_projector (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    ∃ k i j,i≠j ∧ A i k*A⁻¹ k j≠0 := by
  by_contra h
  apply hn
  apply monomial_of_projectors A hA
  push Not at h
  exact h

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Negate one selected coordinate and leave every other coordinate unchanged. -/
def changeSign (i : α) : Matrix α α ℂ := Matrix.diagonal (fun j=>if j=i then -1 else 1)
/-- Double one selected coordinate and leave every other coordinate unchanged. -/
def doubleCoord (i : α) : Matrix α α ℂ := Matrix.diagonal (fun j=>if j=i then 2 else 1)

theorem changeSign_square (i : α) : changeSign i*changeSign i=1 := by
  rw [changeSign,Matrix.diagonal_mul_diagonal]
  ext a b; by_cases h : a=i <;> simp [Matrix.diagonal_apply,Matrix.one_apply,h]

theorem changeSign_inv (i : α) : (changeSign i)⁻¹=changeSign i := Matrix.inv_eq_left_inv
    (changeSign_square i)

theorem changeSign_monomial
    {α : Type}  [DecidableEq α] (i : α) : MonomialMatrix (changeSign i) :=
  MonomialMatrix.diagonal _ (by intro j; split_ifs <;> norm_num)

theorem doubleCoord_monomial
    {α : Type}  [DecidableEq α] (i : α) : MonomialMatrix (doubleCoord i) :=
  MonomialMatrix.diagonal _ (by intro j; split_ifs <;> norm_num)

theorem doubleCoord_inv (i : α) : (doubleCoord i)⁻¹=Matrix.diagonal (fun j=>if j=i then (1/2:ℂ)
    else 1) := by
  apply Matrix.inv_eq_left_inv
  rw [doubleCoord,Matrix.diagonal_mul_diagonal]
  ext a b; by_cases h : a=i <;> simp [Matrix.diagonal_apply,Matrix.one_apply,h]

/-- Subtract a sign-conjugate to isolate the selected row and column off the diagonal. -/
def cut (i : α) (X : Matrix α α ℂ) := X-changeSign i*X*changeSign i

theorem cut_apply (i a b : α) (X : Matrix α α ℂ) :
    cut i X a b=if (a=i ∧ b≠i) ∨ (a≠i ∧ b=i) then 2*X a b else 0 := by
  simp only [cut,Matrix.sub_apply,changeSign,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases ha : a=i <;> by_cases hb : b=i <;> simp [ha,hb] <;> ring

theorem double_cut (i j : α) (hij : i≠j) (X : Matrix α α ℂ) :
    cut i (cut j X)=(4:ℂ)•(X i j•Matrix.single i j 1+X j i•Matrix.single j i 1) := by
  ext a b
  simp only [cut_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.single]
  by_cases hai : a=i <;> by_cases haj : a=j <;> by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [eq_comm] <;> ring

theorem isolate_identity (i j : α) (hij : i≠j) (X : Matrix α α ℂ) :
    doubleCoord i*cut i (cut j X)*(doubleCoord i)⁻¹-(1/2:ℂ)•cut i (cut j X)=
      (6*X i j)•Matrix.single i j 1 := by
  rw [double_cut i j hij X,doubleCoord_inv]
  ext a b
  simp only [doubleCoord,Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.single]
  by_cases hai : a=i <;> by_cases haj : a=j <;> by_cases hbi : b=i <;> by_cases hbj : b=j <;>
    simp_all [eq_comm] <;> ring

theorem single_mem_of_offdiagonal (V : Submodule ℂ (Matrix α α ℂ))
    (hc : ∀ M : Matrix α α ℂ,MonomialMatrix M → ∀ X∈V,M*X*M⁻¹∈V)
    {X : Matrix α α ℂ} (hX : X∈V) (i j : α) (hij : i≠j) (hx : X i j≠0) :
    Matrix.single i j (1:ℂ)∈V := by
  have hcut : ∀ i X,X∈V → cut i X∈V := by
    intro i X hX
    apply V.sub_mem hX
    simpa only [changeSign_inv] using hc (changeSign i) (changeSign_monomial i) X hX
  have hy := hcut i _ (hcut j X hX)
  have hz := V.sub_mem (hc (doubleCoord i) (doubleCoord_monomial i) _ hy) (V.smul_mem (1/2:ℂ) hy)
  rw [isolate_identity i j hij X] at hz
  have hh := V.smul_mem ((6*X i j)⁻¹) hz
  have hn : (6:ℂ)*X i j≠0 := mul_ne_zero (by norm_num) hx
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hh

end ExactFourier.PositiveGeneration

end
end

end Complexity
