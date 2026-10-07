/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.SignedPrice

/-!
# Exact Fourier circuits: symmetric laplacian

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/SymmetricLaplacian.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.SymLap
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The tensor difference `G ⊗ 1 - 1 ⊗ G`. -/
def lap (G : Matrix α α ℂ) : Matrix (α×α) (α×α) ℂ := G⊗ₖ1-(1 : Matrix α α ℂ)⊗ₖG
/-- The tensor square of the matrix `G`. -/
def tensor (G : Matrix α α ℂ) : Matrix (α×α) (α×α) ℂ := G⊗ₖG
/-- Multiply the tensor difference by the tensor square of the symmetrizing matrix. -/
def symmetrized (G J : Matrix α α ℂ) : Matrix (α×α) (α×α) ℂ := (J⊗ₖJ)*lap G

theorem tensor_square (G : Matrix α α ℂ) (hG : G*G=1) : tensor G*tensor G=1 := by
  rw [tensor,← Matrix.mul_kronecker_mul,hG,Matrix.one_kronecker_one]

theorem lap_factor (G : Matrix α α ℂ) (hG : G*G=1) :
    lap G=(G⊗ₖ(1 : Matrix α α ℂ))*(1-tensor G) := by
  rw [mul_sub,mul_one,tensor,← Matrix.mul_kronecker_mul,hG,one_mul]
  rfl

theorem lap_kill (G : Matrix α α ℂ) (hG : G*G=1) : lap G*(1+tensor G)=0 := by
  rw [lap_factor G hG]
  have hm := tensor_square G hG
  calc
    _ = (G⊗ₖ(1 : Matrix α α ℂ))*(1-tensor G*tensor G) := by noncomm_ring
    _ = 0 := by rw [hm,sub_self,mul_zero]

theorem symmetric (G J : Matrix α α ℂ) (s : ℂ) (hs : s*s=1)
    (hJ : J.transpose=s•J) (hc : J*G=G.transpose*J) : (symmetrized G J).IsSymm := by
  change (symmetrized G J).transpose=symmetrized G J
  have hJJ : (J⊗ₖJ).transpose=J⊗ₖJ := by
    rw [← Matrix.kroneckerMap_transpose,hJ,Matrix.smul_kronecker,Matrix.kronecker_smul,
      smul_smul,hs,one_smul]
  have hh : (lap G).transpose*(J⊗ₖJ)=(J⊗ₖJ)*lap G := by
    simp only [lap,Matrix.transpose_sub,← Matrix.kroneckerMap_transpose,Matrix.transpose_one,
      sub_mul,mul_sub,← Matrix.mul_kronecker_mul,one_mul,mul_one,← hc]
  rw [symmetrized,Matrix.transpose_mul,hJJ,hh]

theorem real_entries (G J : Matrix α α ℂ) (hG : ∀ i j,star (G i j)=G i j)
    (hJ : ∀ i j,star (J i j)=J i j) : ∀ i j,star (symmetrized G J i j)=symmetrized G J i j := by
  intro i j
  change (starRingEnd ℂ) (symmetrized G J i j)=symmetrized G J i j
  have hg : ∀ i j,(starRingEnd ℂ) (G i j)=G i j := hG
  have hj : ∀ i j,(starRingEnd ℂ) (J i j)=J i j := hJ
  simp only [symmetrized,Matrix.mul_apply,lap,Matrix.sub_apply,Matrix.kroneckerMap_apply,
    Matrix.one_apply, map_sum, map_mul, map_sub, apply_ite, map_one, map_zero, hg,hj]

theorem support_bound (G J : Matrix α α ℂ) (hJ : MonomialMatrix J) :
    nnz (symmetrized G J)≤2*nnz G*Fintype.card α := by
  rw [symmetrized,nnz_monomial_mul _ _ (hJ.tensor hJ)]
  have hh := nnz_sub_le (G⊗ₖ(1 : Matrix α α ℂ)) ((1 : Matrix α α ℂ)⊗ₖG)
  rw [nnz_kronecker,nnz_kronecker,nnz_one] at hh
  change nnz (lap G)≤_ at hh
  nlinarith [hh]

end ExactFourier.SymLap

end
end

section
namespace ExactFourier
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

theorem det_ne_zero_of_eval_unit (G : Matrix α α (Polynomial ℂ)) (z0 : ℂ)
    (hG : IsUnit (G.map (eval z0))) : G.det≠0 := by
  intro he
  have hdu := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG)
  apply hdu
  have hh := RingHom.map_det (evalRingHom z0) G
  rw [he,map_zero] at hh
  exact hh.symm

theorem unit_eval_of_not_mem_roots (G : Matrix α α (Polynomial ℂ)) (hG : G.det≠0)
    (s : ℂ) (hs : s∉G.det.roots.toFinset) : IsUnit (G.map (eval s)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro he
  apply hs
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hG).mpr
  exact (RingHom.map_det (evalRingHom s) G).trans he

end ExactFourier

end

section
noncomputable section
namespace ExactFourier.LinearProduct
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The polynomial matrix `1 + X • A` associated with one linear factor. -/
def factor (A : Matrix α α ℂ) : Matrix α α (Polynomial ℂ) := 1+(X : Polynomial ℂ)•A.map Polynomial.C

/-- Multiply the polynomial factors `1 + X • A` in list order. -/
def product : List (Matrix α α ℂ) → Matrix α α (Polynomial ℂ)
  | [] => 1
  | a::L => factor a*product L

theorem eval_factor
    {α : Type}  [DecidableEq α] (A : Matrix α α ℂ) (s : ℂ) :
    (factor A).map (evalRingHom s)=1+s•A := by
  rw [factor,Matrix.map_add _ (map_add (evalRingHom s)),CellPoly.map_smul]
  ext i j
  simp [Matrix.one_apply]

omit [Fintype α] in
@[simp] theorem coeff_zero_factor (A : Matrix α α ℂ) :
    (factor A).map (fun f => f.coeff 0)=1 := by
  have he : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by
    funext f; exact coeff_zero_eq_eval_zero f
  rw [he,eval_factor]; simp

@[simp] theorem coeff_one_factor
    {α : Type}  [DecidableEq α] (A : Matrix α α ℂ) :
    (factor A).map (fun f => f.coeff 1)=A := by
  ext i j
  by_cases h : i=j
  · subst j; simp [factor,Polynomial.coeff_one]
  · simp [factor,h]

theorem coeff_one_mul
    {α : Type} [Fintype α]  (A B : Matrix α α (Polynomial ℂ)) :
    (A*B).map (fun f => f.coeff 1)=
      A.map (fun f => f.coeff 0)*B.map (fun f => f.coeff 1)+
      A.map (fun f => f.coeff 1)*B.map (fun f => f.coeff 0) := by
  ext i j
  simp [Matrix.mul_apply,Polynomial.finsetSum_coeff,Polynomial.coeff_mul,
    Finset.Nat.antidiagonal_succ,Finset.sum_add_distrib]

theorem eval_zero_product (L : List (Matrix α α ℂ)) :
    (product L).map (evalRingHom 0)=1 := by
  induction L with
  | nil => simp [product]
  | cons a L ih => rw [product,Matrix.map_mul,eval_factor,ih]; simp

@[simp] theorem coeff_zero_product (L : List (Matrix α α ℂ)) :
    (product L).map (fun f => f.coeff 0)=1 := by
  have he : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by
    funext f; exact coeff_zero_eq_eval_zero f
  rw [he,eval_zero_product]

@[simp] theorem coeff_one_product (L : List (Matrix α α ℂ)) :
    (product L).map (fun f => f.coeff 1)=L.sum := by
  induction L with
  | nil => ext i j; by_cases h : i=j <;> simp [product,h,Polynomial.coeff_one]
  | cons a L ih =>
    rw [product,coeff_one_mul,coeff_zero_factor,coeff_one_factor,coeff_zero_product,
      ih,one_mul,mul_one,List.sum_cons,add_comm]

/-- Remove the constant coefficient and divide each entry of the product by `X`. -/
def quotient (L : List (Matrix α α ℂ)) : Matrix α α (Polynomial ℂ) := (product L).map
    Polynomial.divX

theorem eval_zero_quotient (L : List (Matrix α α ℂ)) :
    (quotient L).map (evalRingHom 0)=L.sum := by
  have hh := coeff_one_product L
  ext i j
  have he := congrFun (congrFun hh i) j
  change ((product L i j).divX).eval 0=_
  rw [← coeff_zero_eq_eval_zero,Polynomial.coeff_divX]
  exact he

theorem split_product (L : List (Matrix α α ℂ)) : product L=1+(X : Polynomial ℂ)•quotient L := by
  have hh := coeff_zero_product L
  apply Matrix.ext; intro i j
  have he := congrFun (congrFun hh i) j
  have hp : (X : Polynomial ℂ) * (product L i j).divX + Polynomial.C ((product L i j).coeff
    0)=product L i j := Polynomial.X_mul_divX_add (product L i j)
  change product L i j=(1 : Matrix α α (Polynomial ℂ)) i j+X*(product L i j).divX
  calc
    _ = X*(product L i j).divX+Polynomial.C ((product L i j).coeff 0) := hp.symm
    _ = _ := by
      rw [add_comm]
      congr 1
      change Polynomial.C ((product L).map (fun f => f.coeff 0) i j)=_
      rw [hh]
      by_cases h : i=j <;> simp [Matrix.one_apply,h]

theorem eval_product_cost (p : MatrixPrice) (L : List (Matrix α α ℂ))
    (c : Matrix α α ℂ → ℝ) (s : ℂ)
    (hL : ∀ a∈L,IsUnit (1+s•a) ∧ p.value (1+s•a)≤c a) :
    IsUnit ((product L).map (evalRingHom s)) ∧
    p.value ((product L).map (evalRingHom s))≤(L.map c).sum := by
  induction L with
  | nil => simp [product,p.one]
  | cons a L ih =>
    obtain ⟨ha,hpa⟩ := hL a (by simp)
    obtain ⟨hbu,hbp⟩ := ih (fun b hb => hL b (by simp [hb]))
    rw [product,Matrix.map_mul,eval_factor]
    refine ⟨ha.mul hbu,?_⟩
    exact (p.mul_le _ _ ha hbu).trans (by simpa using add_le_add hpa hbp)

end ExactFourier.LinearProduct

end
end

section
noncomputable section
namespace ExactFourier.SparseReflection
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Two distinct coordinates with nonzero coefficients for their opposing off-diagonal entries. -/
structure PairTerm (α : Type) where
  /-- The first coordinate of the off-diagonal pair. -/
  i : α
  /-- The second coordinate, distinct from the first. -/
  j : α
  hij : i≠j
  /-- The nonzero coefficient in the first-to-second matrix position. -/
  a : ℂ
  /-- The nonzero coefficient in the second-to-first matrix position. -/
  b : ℂ
  ha : a≠0
  hb : b≠0

/-- The matrix supported on the two specified off-diagonal positions. -/
def PairTerm.direction (u : PairTerm α) : Matrix α α ℂ :=
  Matrix.single u.i u.j u.a+Matrix.single u.j u.i u.b

/-- The quadratic polynomial controlling invertibility of this pair perturbation. -/
def PairTerm.den (u : PairTerm α) : Polynomial ℂ := 1-X^2*Polynomial.C (u.a*u.b)

theorem PairTerm.den_ne
    {α : Type}   (u : PairTerm α) : u.den≠0 := by
  intro h
  have hh := congrArg (Polynomial.eval 0) h
  simp [PairTerm.den] at hh

/-- Zero and the roots of the pair's invertibility polynomial. -/
def PairTerm.bad (u : PairTerm α) : Finset ℂ := insert 0 u.den.roots.toFinset

theorem PairTerm.price (p : MatrixPrice) (u : PairTerm α) (s : ℂ) (hs : s∉u.bad) :
    IsUnit (1+s•u.direction) ∧ p.value (1+s•u.direction)≤(3:ℝ)/2 := by
  classical
  have hs0 : s≠0 := by intro h; apply hs; simp [PairTerm.bad,h]
  have hd : 1-(s*u.a)*(s*u.b)≠0 := by
    intro h
    apply hs
    apply Finset.mem_insert_of_mem
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots u.den_ne).mpr
    change u.den.eval s=0
    simp only [PairTerm.den,eval_sub,eval_one,eval_mul,eval_pow,eval_X,eval_C]
    convert h using 1 ; ring
  have he : 1+s•u.direction=1+Matrix.single u.i u.j (s*u.a)+Matrix.single u.j u.i (s*u.b) := by
    ext i j
    simp [PairTerm.direction,Matrix.single,smul_eq_mul,mul_ite,add_assoc]
  rw [he]
  exact Embedded.pair_price p u.i u.j u.hij (s*u.a) (s*u.b)
    (mul_ne_zero hs0 u.ha) (mul_ne_zero hs0 u.hb) hd

theorem pair_list_cost (p : MatrixPrice) (L : List (PairTerm α)) :
    ∃ E : Finset ℂ,∀ s : ℂ,s∉E →
      IsUnit ((LinearProduct.product (L.map PairTerm.direction)).map (evalRingHom s)) ∧
      p.value ((LinearProduct.product (L.map PairTerm.direction)).map (evalRingHom
        s))≤(3:ℝ)/2*L.length := by
  classical
  induction L with
  | nil => exact ⟨∅,by intro s hs; simp [LinearProduct.product,p.one]⟩
  | cons u L ih =>
    obtain ⟨E,hE⟩ := ih
    refine ⟨u.bad∪E,?_⟩
    intro s hs
    have hsu : s∉u.bad := fun h => hs (Finset.mem_union_left _ h)
    have hse : s∉E := fun h => hs (Finset.mem_union_right _ h)
    obtain ⟨hu,hpu⟩ := u.price p s hsu
    obtain ⟨hL,hpL⟩ := hE s hse
    rw [List.map_cons,LinearProduct.product,Matrix.map_mul,LinearProduct.eval_factor]
    refine ⟨hu.mul hL,?_⟩
    have hh := (p.mul_le _ _ hu hL).trans (add_le_add hpu hpL)
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_comm] using hh

theorem diagonal_family (p : MatrixPrice) (d : α → ℂ) :
    ∃ E : Finset ℂ,∀ s : ℂ,s∉E → IsUnit (1+s•Matrix.diagonal d) ∧ p.value (1+s•Matrix.diagonal
      d)=0 := by
  classical
  let q : Polynomial ℂ := ∏ i, (1+X*Polynomial.C (d i))
  have hq0 : q.eval 0=1 := by simp only [q,Polynomial.eval_prod]; simp
  have hq : q≠0 := by intro h; simp [h] at hq0
  refine ⟨q.roots.toFinset,?_⟩
  intro s hs
  have hqs : q.eval s≠0 := by
    intro h; exact hs (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr h))
  have hd : ∀ i,1+s*d i≠0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp (show (∏ j, (1+s*d j))≠0 by simpa only [q,
      Polynomial.eval_prod,eval_add,eval_one,eval_mul,eval_X,eval_C] using hqs)) i
      (Finset.mem_univ i)
  have he : 1+s•Matrix.diagonal d=Matrix.diagonal (fun i=>1+s*d i) := by
    ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]
  rw [he]
  have hm := MonomialMatrix.diagonal _ hd
  have hu := MonomialMatrix.unit _ hm
  exact ⟨hu,(p.zero_iff _ hu).mpr hm⟩

/-- The exact polynomial tangent used in the first sparse-reflection specialization. -/
theorem exists_tangent (p : MatrixPrice) (d : α → ℂ) (L : List (PairTerm α)) :
    ∃ Q : Matrix α α (Polynomial ℂ),∃ E : Finset ℂ,
      Q.map (evalRingHom 0)=Matrix.diagonal d+(L.map PairTerm.direction).sum ∧
      ∀ s : ℂ,s∉E → IsUnit (1+s•Q.map (evalRingHom s)) ∧
        p.value (1+s•Q.map (evalRingHom s))≤(3:ℝ)/2*L.length := by
  classical
  obtain ⟨E1,hE1⟩ := diagonal_family p d
  obtain ⟨E2,hE2⟩ := pair_list_cost p L
  let W := Matrix.diagonal d::L.map PairTerm.direction
  refine ⟨LinearProduct.quotient W,E1∪E2,?_,?_⟩
  · rw [LinearProduct.eval_zero_quotient]; rfl
  · intro s hs
    have hs1 : s∉E1 := fun h => hs (Finset.mem_union_left _ h)
    have hs2 : s∉E2 := fun h => hs (Finset.mem_union_right _ h)
    obtain ⟨hD,hpD⟩ := hE1 s hs1
    obtain ⟨hL,hpL⟩ := hE2 s hs2
    have he : (LinearProduct.product W).map (evalRingHom s)=
        1+s•(LinearProduct.quotient W).map (evalRingHom s) := by
      rw [LinearProduct.split_product,Matrix.map_add _ (map_add (evalRingHom s)),CellPoly.map_smul]
      simp
    rw [← he]
    dsimp only [W,LinearProduct.product]
    rw [Matrix.map_mul,LinearProduct.eval_factor]
    refine ⟨hD.mul hL,?_⟩
    have hh := p.mul_le _ _ hD hL
    rw [hpD,zero_add] at hh
    exact hh.trans hpL

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.MatrixPrice
open scoped Matrix
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The matrix Cayley transform `(1 + t • A) * (1 - t • A)⁻¹`. -/
def cayley (A : Matrix α α ℂ) (t : ℂ) : Matrix α α ℂ :=
  (1+t•A)*(1-t•A)⁻¹

theorem cayley_unit (A : Matrix α α ℂ) (t : ℂ)
    (hp : IsUnit (1+t•A)) (hm : IsUnit (1-t•A)) : IsUnit (cayley A t) :=
  hp.mul (Matrix.isUnit_nonsing_inv_iff.mpr hm)

theorem cayley_denominator
    {α : Type}  [DecidableEq α] (A : Matrix α α ℂ) (e t : ℂ) (het : e+t≠0) :
    1-(t/(e+t))•(1+e•A)=(e/(e+t))•(1-t•A) := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ; ring

theorem cayley_response (A : Matrix α α ℂ) (e t : ℂ)
    (he : e≠0) (het : e+t≠0) (hm : IsUnit (1-t•A)) :
    CellPoly.feedback ((e-t)•1) (1+e•A) ((2*e)•1) (1+e•A) (t/(e+t))=
      (e+t)•cayley A t := by
  let K := 1+e•A
  let W := 1-(t/(e+t))•K
  have heq : W=(e/(e+t))•(1-t•A) := cayley_denominator A e t het
  have hu : IsUnit W := by rw [heq]; exact scalar_unit _ hm _ (div_ne_zero he het)
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  apply hu.mul_right_cancel
  change CellPoly.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t))*W=_
  have hL : CellPoly.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t))*W=
      (e-t)•W+((t/(e+t))*(2*e))•K := by
    simp only [CellPoly.feedback,add_mul,Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul,smul_smul]
    change (e-t)•W+((t/(e+t))*(2*e))•(K*W⁻¹*W)=_
    rw [Matrix.nonsing_inv_mul_cancel_right _ _ hd]
  rw [hL,heq,cayley,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hm),mul_one,smul_smul]
  ext i j
  simp only [K,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ; ring

theorem cayley_feedback (p : MatrixPrice) (A : Matrix α α ℂ) (e t : ℂ)
    (he : e≠0) (hep : e+t≠0) (hem : e-t≠0)
    (hK : IsUnit (1+e•A)) (hp : IsUnit (1+t•A)) (hm : IsUnit (1-t•A)) :
    p.value (cayley A t)≤p.value (1+e•A)+2*Fintype.card α := by
  let K := 1+e•A
  let P : Matrix (Fin 2) (Fin 2) ℂ := !![e-t,1;2*e,1]
  have hP : IsUnit P := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    have hd : P.det=-(e+t) := by simp [P,Matrix.det_fin_two]; ring
    rw [hd]; exact neg_ne_zero.mpr hep
  let F := Matrix.fromBlocks ((e-t)•(1 : Matrix α α ℂ)) K ((2*e)•1) K
  have hf : F=pairLayer P*Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 K := by
    simp [F,pairLayer_eq,P,Matrix.fromBlocks_multiply]
  have hF : IsUnit F := by
    rw [hf]; exact (pairLayer_unit P hP).mul (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,hK⟩)
  have hM : IsUnit ((e-t)•(1 : Matrix α α ℂ)) := scalar_unit _ isUnit_one _ hem
  have hW : IsUnit (1-(t/(e+t))•K) := by
    rw [cayley_denominator A e t hep]; exact scalar_unit _ hm _ (div_ne_zero he hep)
  have hr := cayley_response A e t he hep hm
  have hCu := cayley_unit A t hp hm
  have hH : IsUnit (CellPoly.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t))) := by
    rw [hr]; exact scalar_unit _ hCu _ hep
  have hb := p.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t)) hM hF hW hH
  rw [hr,p.scalar _ hCu _ hep] at hb
  have hc := p.mul_le (pairLayer (β := α) P) (Matrix.fromBlocks 1 0 0 K)
    (pairLayer_unit P hP) (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,hK⟩)
  rw [← hf,p.directSum _ _ isUnit_one hK,p.one,zero_add] at hc
  have hl := p.pair_layer (β := α) P hP
  linarith

end ExactFourier.MatrixPrice

end
end

end Complexity
