/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PositiveReach
public import Mathlib.Analysis.Matrix.Normed

/-!
# Exact Fourier circuits: parameter algebra

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/ParameterAlgebra.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α κ : Type} [Fintype α] [DecidableEq α]

/-- Evaluate a matrix of multivariate polynomials at one parameter vector. -/
def evalMatrix (F : Matrix α α (MvPolynomial κ ℂ)) (x : κ→ℂ) : Matrix α α ℂ :=
  (aeval x).mapMatrix F

@[simp] theorem evalMatrix_apply (F : Matrix α α (MvPolynomial κ ℂ)) (x : κ→ℂ) (i j : α) :
    evalMatrix F x i j=aeval x (F i j) := rfl

@[simp] theorem evalMatrix_mul (F G : Matrix α α (MvPolynomial κ ℂ)) (x : κ→ℂ) :
    evalMatrix (F*G) x=evalMatrix F x*evalMatrix G x := map_mul _ _ _

theorem evalMatrix_const (M : Matrix α α ℂ) (x : κ→ℂ) :
    evalMatrix (C.mapMatrix M) x=M := by ext i j; simp [evalMatrix]

theorem evalMatrix_rename {τ : Type} (e : κ→τ)
    (F : Matrix α α (MvPolynomial κ ℂ)) (x : τ→ℂ) :
    evalMatrix ((rename e).mapMatrix F) x=evalMatrix F (x∘e) := by
  ext i j
  exact aeval_rename e x (F i j)

@[simp] theorem evalMatrix_diag (d : α→MvPolynomial κ ℂ) (x : κ→ℂ) :
    evalMatrix (Matrix.diagonal d) x=Matrix.diagonal (fun i=>aeval x (d i)) := by
  exact Matrix.diagonal_map (map_zero _)

/-- Form a diagonal matrix as a continuous complex linear map. -/
def diagCLM : (α→ℂ) →L[ℂ] Matrix α α ℂ := diagLinear.toContinuousLinearMap
@[simp] theorem diagCLM_apply (x : α→ℂ) : diagCLM x=Matrix.diagonal x := rfl

/-- Project a vector on a sum of coordinate types to its left block. -/
def leftProj  : (κ⊕α→ℂ) →L[ℂ] (κ→ℂ) :=
  ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (Sum.inl i))
/-- Project a vector on a sum of coordinate types to its right block. -/
def rightProj  : (κ⊕α→ℂ) →L[ℂ] (α→ℂ) :=
  ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (Sum.inr i))
@[simp] theorem leftProj_apply
    {α κ : Type} (x : κ⊕α→ℂ) : leftProj x=x∘Sum.inl := rfl
@[simp] theorem rightProj_apply
    {α κ : Type} (x : κ⊕α→ℂ) : rightProj x=x∘Sum.inr := rfl

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

/-- A fixed positive word with polynomial diagonal parameters and its exact derivative. -/
structure Param (A p : Matrix α α ℂ) (U : Submodule ℂ (Matrix α α ℂ)) where
  /-- The finite parameter-coordinate type of the polynomial family. -/
  Vars : Type
  finiteVars : Fintype Vars
  /-- The matrix of polynomials describing the parameterized positive words. -/
  poly : Matrix α α (MvPolynomial Vars ℂ)
  /-- The fixed number of calls to `A` in every nonzero-parameter instance. -/
  calls : ℕ
  base : evalMatrix poly (fun _=>1)=p
  pattern : ∀ x : Vars→ℂ,(∀ i,x i≠0) → Pattern A calls (evalMatrix poly x)
  /-- The derivative of the polynomial family at the all-ones parameter vector. -/
  derivative : letI := finiteVars; (Vars→ℂ) →L[ℂ] Matrix α α ℂ
  deriv : letI := finiteVars; HasStrictFDerivAt (evalMatrix poly) derivative (fun _=>1)
  spans : ∀ X∈U,∃ x : Vars→ℂ,derivative x=X*p

attribute [instance] Param.finiteVars

/-- The initial diagonal polynomial family with no calls to `A`. -/
def Param.nil (A : Matrix α α ℂ) : Param A 1 (diagConj 1) where
  Vars := α
  finiteVars := inferInstance
  poly := Matrix.diagonal X
  calls := 0
  base := by simp
  pattern x hx := by
    simpa using Pattern.zero (A := A) (Matrix.diagonal x) (MonomialMatrix.diagonal x hx)
  derivative := diagCLM
  deriv := by
    convert! (diagCLM (α := α)).hasStrictFDerivAt (x := fun _=>1) using 1
    funext x
    change evalMatrix (Matrix.diagonal X) x=Matrix.diagonal x
    simp only [evalMatrix_diag,aeval_X]
  spans X hX := by
    obtain ⟨d,hd⟩ := hX
    refine ⟨d,?_⟩
    change 1*Matrix.diagonal d*1⁻¹=X at hd
    simpa using hd

/-- Append a fixed matrix and a fresh diagonal parameter block to the family. -/
def Param.nextPoly {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ) :
    Matrix α α (MvPolynomial (P.Vars⊕α) ℂ) :=
  (rename Sum.inl).mapMatrix P.poly*C.mapMatrix s*Matrix.diagonal (fun i=>X (Sum.inr i))

@[simp] theorem Param.eval_nextPoly {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ)
    (x : P.Vars⊕α→ℂ) :
    evalMatrix (P.nextPoly s) x=evalMatrix P.poly (x∘Sum.inl)*s*Matrix.diagonal (x∘Sum.inr) := by
  simp only [Param.nextPoly,evalMatrix_mul,evalMatrix_rename,evalMatrix_const,evalMatrix_diag,
    aeval_X]
  rfl

/-- The product-rule derivative after appending a matrix and diagonal parameters. -/
def Param.nextDerivative {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ) :
    (P.Vars⊕α→ℂ) →L[ℂ] Matrix α α ℂ :=
  ((ContinuousLinearMap.mulLeftRight ℂ (Matrix α α ℂ) 1 s).comp P.derivative).comp leftProj +
  ((ContinuousLinearMap.mulLeftRight ℂ (Matrix α α ℂ) (p*s) 1).comp diagCLM).comp rightProj

@[simp] theorem Param.nextDerivative_apply {A p U} (P : Param (α := α) A p U)
    (s : Matrix α α ℂ) (x : P.Vars⊕α→ℂ) :
    P.nextDerivative s x=P.derivative (x∘Sum.inl)*s+(p*s)*Matrix.diagonal (x∘Sum.inr) := by
  change 1*P.derivative (x∘Sum.inl)*s+(p*s)*Matrix.diagonal (x∘Sum.inr)*1=_
  simp only [one_mul,mul_one]

theorem Param.next_deriv {A p U} (P : Param (α := α) A p U) (s : Matrix α α ℂ) :
    HasStrictFDerivAt (evalMatrix (P.nextPoly s)) (P.nextDerivative s) (fun _=>1) := by
  have h1 := (P.deriv.comp (fun _ : P.Vars⊕α=> (1:ℂ))
    (leftProj (κ := P.Vars) (α := α)).hasStrictFDerivAt).mul_const' s
  have h2 := (diagCLM (α := α)).hasStrictFDerivAt.comp (fun _ : P.Vars⊕α=> (1:ℂ))
    (rightProj (κ := P.Vars) (α := α)).hasStrictFDerivAt
  convert! h1.mul' h2 using 1
  · funext x
    change evalMatrix (P.nextPoly s) x=evalMatrix P.poly (x∘Sum.inl)*s*Matrix.diagonal (x∘Sum.inr)
    exact P.eval_nextPoly s x
  · ext1 x
    change P.nextDerivative s x=(evalMatrix P.poly (fun _=>1)*s)*Matrix.diagonal (x∘Sum.inr)+
      (P.derivative (x∘Sum.inl)*s)*Matrix.diagonal (fun _=>1)
    rw [P.base,Matrix.diagonal_one,mul_one,P.nextDerivative_apply,add_comm]

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Param.base_unit {A p U} (P : Param (α := α) A p U) (hA : IsUnit A) : IsUnit p := by
  have hu := pattern_unit hA (P.pattern (fun _=>1) (by simp))
  rwa [P.base] at hu

/-- Extend a parameterized family by a reachable matrix and its diagonal directions. -/
def Param.snoc {A p U} (P : Param (α := α) A p U) (hA : IsUnit A)
    (s : Matrix α α ℂ) (hs : Reach A s) : Param A (p*s) (U⊔diagConj (p*s)) where
  Vars := P.Vars⊕α
  finiteVars := inferInstance
  poly := P.nextPoly s
  calls := P.calls+Classical.choose hs
  base := by simp only [Param.eval_nextPoly,Function.comp_def,P.base,Matrix.diagonal_one,mul_one]
  pattern x hx := by
    rw [Param.eval_nextPoly]
    exact ((P.pattern (x∘Sum.inl) (fun i=>hx (Sum.inl i))).mul (Classical.choose_spec
      hs)).monomial_right
      _ (MonomialMatrix.diagonal _ (fun i=>hx (Sum.inr i)))
  derivative := P.nextDerivative s
  deriv := P.next_deriv s
  spans X hX := by
    obtain ⟨Y,hY,Z,hZ,rfl⟩ := Submodule.mem_sup.mp hX
    obtain ⟨u,hu⟩ := P.spans Y hY
    obtain ⟨d,hd⟩ := mem_diagConj _ _ |>.mp hZ
    refine ⟨Sum.elim u d,?_⟩
    rw [Param.nextDerivative_apply]
    have hu' : (Sum.elim u d)∘Sum.inl=u := rfl
    have hd' : (Sum.elim u d)∘Sum.inr=d := rfl
    rw [hu',hd',hu]
    have hi := Matrix.nonsing_inv_mul (p*s)
      ((Matrix.isUnit_iff_isUnit_det _).mp ((P.base_unit hA).mul (hs.unit hA)))
    calc
      _ = Y*(p*s)+(p*s)*Matrix.diagonal d := by noncomm_ring
      _ = Y*(p*s)+Z*(p*s) := by
        congr 1
        rw [← hd]
        simp only [mul_assoc,hi,mul_one]
      _ = (Y+Z)*(p*s) := (add_mul _ _ _).symm

theorem Chain.parameterization {A p U} (h : Chain (α := α) A p U) (hA : IsUnit A) :
    Nonempty (Param A p U) := by
  induction h with
  | nil => exact ⟨Param.nil A⟩
  | @snoc p U s h hs ih =>
    obtain ⟨P⟩ := ih
    exact ⟨P.snoc hA s hs⟩

theorem Param.derivative_surjective {A p} (P : Param (α := α) A p ⊤) (hA : IsUnit A) :
    Function.Surjective P.derivative := by
  intro X
  obtain ⟨x,hx⟩ := P.spans (X*p⁻¹) Submodule.mem_top
  refine ⟨x,?_⟩
  rw [mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (P.base_unit hA)),
    mul_one] at hx
  exact hx

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Identify a matrix with the vector of entries indexed by pairs of coordinates. -/
def flatten : Matrix α α ℂ ≃ₗ[ℂ] (α×α→ℂ) where
  toFun M ij := M ij.1 ij.2
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous linear equivalence flattening a finite matrix into its entries. -/
def flatCLM : Matrix α α ℂ ≃L[ℂ] (α×α→ℂ) := flatten.toContinuousLinearEquiv

@[simp] theorem flatCLM_apply
    {α : Type} [Fintype α]  (M : Matrix α α ℂ) (ij : α×α) : flatCLM M ij=M ij.1 ij.2 := rfl

/-- The polynomial substitution homomorphism defined by the parameterized matrix entries. -/
def Param.hom {A p U} (P : Param (α := α) A p U) :
    MvPolynomial (α×α) ℂ →ₐ[ℂ] MvPolynomial P.Vars ℂ := aeval (fun ij=>P.poly ij.1 ij.2)

@[simp] theorem Param.polynomialMap_hom {A p U} (P : Param (α := α) A p U) (x : P.Vars→ℂ) :
    polynomialMap P.hom x=flatCLM (evalMatrix P.poly x) := by
  funext ij
  simp [polynomialMap,Param.hom]

theorem Param.hom_injective {A p} (P : Param (α := α) A p ⊤) (hA : IsUnit A) :
    Function.Injective P.hom := by
  let d := flatCLM.toContinuousLinearMap.comp P.derivative
  apply injective_of_submersion P.hom (fun _=>1) d
  · have hh := (flatCLM (α := α)).toContinuousLinearMap.hasStrictFDerivAt.comp (fun _ : P.Vars=>
    (1:ℂ)) P.deriv
    convert! hh using 1
    funext x
    exact P.polynomialMap_hom x
  · apply LinearMap.range_eq_top.mpr
    exact flatCLM.surjective.comp (P.derivative_surjective hA)

theorem Param.open_word {A p} (P : Param (α := α) A p ⊤) (hA : IsUnit A) :
    ∃ g : MvPolynomial (α×α) ℂ,g≠0 ∧ ∀ H : Matrix α α ℂ,
      aeval (flatCLM H) g≠0 → Pattern A P.calls H := by
  classical
  let q : MvPolynomial P.Vars ℂ := ∏ i,X i
  have hq : q≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>X_ne_zero i)
  obtain ⟨g,hg,hgi⟩ := polynomial_open_image P.hom (P.hom_injective hA) q hq
  refine ⟨g,hg,?_⟩
  intro H hH
  obtain ⟨x,hx,hxH⟩ := hgi (flatCLM H) hH
  have hxn : ∀ i,x i≠0 := by
    have hh : (∏ i,x i)≠0 := by simpa [q,map_prod,aeval_X] using hx
    exact fun i=>Finset.prod_ne_zero_iff.mp hh i (Finset.mem_univ i)
  have he : evalMatrix P.poly x=H := by
    ext i j
    have ht := hxH (i,j)
    simpa [Param.hom] using ht
  rw [← he]
  exact P.pattern x hxn

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial Filter Topology
variable {ι : Type} [Fintype ι]

/-- Nonempty Zariski basic opens in complex affine space are Euclidean dense. -/
theorem polynomial_nonzero_dense (g : MvPolynomial ι ℂ) (hg : g≠0) :
    Dense {y : ι→ℂ | aeval y g≠0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra h
  obtain ⟨z,hz⟩ := hne
  have hzero : (fun y : ι→ℂ=>aeval y g)=ᶠ[𝓝 z] 0 := by
    filter_upwards [hU.mem_nhds hz] with y hy
    by_contra hn
    exact h ⟨y,hy,hn⟩
  have hall := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ)
    g).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) hzero
  apply hg
  apply MvPolynomial.funext
  intro y
  simpa using hall (Set.mem_univ y)

theorem polynomial_nonzero_open (g : MvPolynomial ι ℂ) :
    IsOpen {y : ι→ℂ | aeval y g≠0} := by
  apply isOpen_ne_fun _ continuous_const
  exact continuousOn_univ.mp (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) g).continuousOn

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial Filter Topology
open scoped Matrix.Norms.Operator
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Pattern.zero_iff (A H : Matrix α α ℂ) : Pattern A 0 H ↔ MonomialMatrix H := by
  constructor
  · intro h; cases h with | zero M hM => exact hM
  · exact Pattern.zero H

/-- Positive generation, with a common strictly positive number of forward calls. -/
theorem positive_generation (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    ∃ h : ℕ,0<h ∧ ∀ H : Matrix α α ℂ,IsUnit H → Pattern A h H := by
  obtain ⟨p,hp⟩ := exists_full_chain A hA hn
  obtain ⟨P⟩ := hp.parameterization hA
  obtain ⟨g,hg,hgi⟩ := P.open_word hA
  let S : Set (Matrix α α ℂ) := {H | aeval (flatCLM H) g≠0}
  have hSd : Dense S := (polynomial_nonzero_dense g hg).preimage flatCLM.toHomeomorph.isOpenMap
  have hSo : IsOpen S := (polynomial_nonzero_open g).preimage flatCLM.continuous
  have hpat : ∀ H∈S,Pattern A P.calls H := hgi
  obtain ⟨W,hW⟩ := hSd.nonempty
  have hWu : IsUnit W := pattern_unit hA (hpat W hW)
  have hall : ∀ H : Matrix α α ℂ,IsUnit H → Pattern A (P.calls+P.calls) H := by
    intro H hH
    let V₀ := H*W⁻¹
    have hVu : IsUnit V₀ := hH.mul (Matrix.isUnit_nonsing_inv_iff.mpr hWu)
    let f : Matrix α α ℂ → Matrix α α ℂ := fun V=>Ring.inverse V*H
    have hf : ContinuousAt f V₀ := by
      exact ((hVu.unit_spec ▸ NormedRing.inverse_continuousAt hVu.unit)).mul continuousAt_const
    have hfV : f V₀=W := by
      change Ring.inverse (H*W⁻¹)*H=W
      rw [← Matrix.nonsing_inv_eq_ringInverse,Matrix.mul_inv_rev,Matrix.nonsing_inv_nonsing_inv
        _ ((Matrix.isUnit_iff_isUnit_det _).mp hWu)]
      rw [mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hH),mul_one]
    have hnh : f⁻¹' S∈𝓝 V₀ := hf.preimage_mem_nhds (hSo.mem_nhds (hfV ▸ hW))
    obtain ⟨V,hV,hfVS⟩ := hSd.inter_nhds_nonempty hnh
    have hVp := hpat V hV
    have hVi := Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det _).mp (pattern_unit hA hVp))
    have hh := hVp.mul (hpat (f V) hfVS)
    have he : V*f V=H := by
      change V*(Ring.inverse V*H)=H
      rw [← Matrix.nonsing_inv_eq_ringInverse,← mul_assoc,hVi,one_mul]
    rwa [he] at hh
  refine ⟨P.calls+P.calls,?_,hall⟩
  by_contra h
  have hz : P.calls+P.calls=0 := Nat.eq_zero_of_not_pos h
  exact hn ((Pattern.zero_iff A A).mp (hz ▸ hall A hA))

end ExactFourier.PositiveGeneration

end
end

end Complexity
