/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.MonomialTools
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Exact Fourier circuits: positive reach

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PositiveReach.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Pattern.monomial_right {A H : Matrix α α ℂ} {k : ℕ} (h : Pattern A k H)
    (M : Matrix α α ℂ) (hM : MonomialMatrix M) : Pattern A k (H*M) := by
  induction h with
  | zero N hN => exact .zero _ (hN.mul hM)
  | succ h N hN ih => simpa only [mul_assoc] using Pattern.succ h (N*M) (hN.mul hM)

theorem Pattern.mul {A H K : Matrix α α ℂ} {k l : ℕ} (hH : Pattern A k H) (hK : Pattern A l K) :
    Pattern A (k+l) (H*K) := by
  induction hK with
  | zero M hM => simpa using hH.monomial_right M hM
  | @succ l K h M hM ih => simpa only [Nat.add_assoc,mul_assoc] using Pattern.succ ih M hM

/-- The matrix is realized by some positive word in `A` and monomial matrices. -/
def Reach (A H : Matrix α α ℂ) : Prop := ∃ k,Pattern A k H

theorem Reach.one (A : Matrix α α ℂ) : Reach A 1 := ⟨0,.zero 1 MonomialMatrix.one⟩
theorem Reach.monomial (A M : Matrix α α ℂ) (hM : MonomialMatrix M) : Reach A M := ⟨0,.zero M hM⟩
theorem Reach.self (A : Matrix α α ℂ) : Reach A A := by
  refine ⟨1,?_⟩
  simpa using Pattern.succ (Pattern.zero (A := A) 1 MonomialMatrix.one) 1 MonomialMatrix.one

theorem Reach.mul {A H K : Matrix α α ℂ} (hH : Reach A H) (hK : Reach A K) : Reach A (H*K) := by
  obtain ⟨k,hk⟩ := hH
  obtain ⟨l,hl⟩ := hK
  exact ⟨k+l,hk.mul hl⟩

theorem Reach.unit {A H : Matrix α α ℂ} (hA : IsUnit A) (hH : Reach A H) : IsUnit H := by
  obtain ⟨k,hk⟩ := hH
  exact pattern_unit hA hk

/-- Diagonal directions conjugated by matrices reachable from `A`. -/
def directions (A : Matrix α α ℂ) : Set (Matrix α α ℂ) :=
  {X | ∃ (s : Matrix α α ℂ),Reach A s ∧ ∃ d : α→ℂ,X=s*Matrix.diagonal d*s⁻¹}

/-- The complex linear span of all reachable conjugated diagonal directions. -/
def tangentSpan (A : Matrix α α ℂ) : Submodule ℂ (Matrix α α ℂ) := Submodule.span ℂ (directions A)

theorem direction_mem (A s : Matrix α α ℂ) (hs : Reach A s) (d : α→ℂ) :
    s*Matrix.diagonal d*s⁻¹∈tangentSpan A := Submodule.subset_span ⟨s,hs,d,rfl⟩

theorem diagonal_mem (A : Matrix α α ℂ) (d : α→ℂ) : Matrix.diagonal d∈tangentSpan A := by
  simpa using direction_mem A 1 (Reach.one A) d

theorem tangent_conj (A s : Matrix α α ℂ) (hs : Reach A s) {X : Matrix α α ℂ}
    (hX : X∈tangentSpan A) : s*X*s⁻¹∈tangentSpan A := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨t,ht,d,rfl⟩ := hX
    have hh := direction_mem A (s*t) (hs.mul ht) d
    simpa only [Matrix.mul_inv_rev,mul_assoc] using hh
  | zero => simp
  | add X Y hX hY ihX ihY => simpa only [mul_add,add_mul] using (tangentSpan A).add_mem ihX ihY
  | smul c X hX ih =>
    simpa only [Matrix.mul_smul,Matrix.smul_mul] using (tangentSpan
      A).smul_mem c ih

theorem tangent_monomial_conj (A M : Matrix α α ℂ) (hM : MonomialMatrix M)
    (X : Matrix α α ℂ) (hX : X∈tangentSpan A) : M*X*M⁻¹∈tangentSpan A :=
  tangent_conj A M (Reach.monomial A M hM) hX

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

theorem single_diagonal
    {α : Type}  [DecidableEq α] (k : α) : Matrix.diagonal (Pi.single k (1:ℂ))=Matrix.single k k
      1 := by
  ext i j
  by_cases hi : i=k <;> by_cases hj : j=k <;>
    simp [Matrix.diagonal_apply,Matrix.single,hi,hj] <;> aesop

theorem projector_apply (A : Matrix α α ℂ) (k i j : α) :
    (A*Matrix.single k k (1:ℂ)*A⁻¹) i j=A i k*A⁻¹ k j := by
  simp [Matrix.mul_apply,Matrix.single,ite_and]

theorem tangent_top (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    tangentSpan A=⊤ := by
  obtain ⟨k,i,j,hij,hx⟩ := exists_nondiagonal_projector A hA hn
  have hp := direction_mem A A (Reach.self A) (Pi.single k 1)
  rw [single_diagonal] at hp
  have hx' : (A*Matrix.single k k (1:ℂ)*A⁻¹) i j≠0 := by rw [projector_apply]; exact hx
  have he := single_mem_of_offdiagonal (tangentSpan A) (tangent_monomial_conj A) hp i j hij hx'
  have hall : ∀ a b,Matrix.single a b (1:ℂ)∈tangentSpan A := by
    intro a b
    by_cases hab : a=b
    · subst b
      rw [← single_diagonal]
      exact diagonal_mem A _
    · obtain ⟨e,hei,hej⟩ := exists_perm_pair i j a b hij hab
      have ht := tangent_monomial_conj A (permM e) (permM_monomial e) _ he
      rwa [permM_conj_single,hei,hej] at ht
  apply Submodule.eq_top_iff'.mpr
  intro X
  have hdec : X=∑ a,∑ b,X a b•Matrix.single a b (1:ℂ) := by
    ext i j
    simp [Matrix.sum_apply,Matrix.single,ite_and]
  rw [hdec]
  exact (tangentSpan A).sum_mem (fun a _ => (tangentSpan A).sum_mem (fun b _ => (tangentSpan
    A).smul_mem _ (hall a b)))

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The linear map sending `X` to `p * X * p⁻¹`. -/
def conjLinear (p : Matrix α α ℂ) : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ where
  toFun X := p*X*p⁻¹
  map_add' _ _ := by simp [mul_add,add_mul]
  map_smul' _ _ := by simp

/-- The complex linear map forming a diagonal matrix from its entries. -/
def diagLinear : (α→ℂ) →ₗ[ℂ] Matrix α α ℂ where
  toFun := Matrix.diagonal
  map_add' _ _ := (Matrix.diagonal_add _ _).symm
  map_smul' _ _ := Matrix.diagonal_smul _ _

/-- The subspace of diagonal matrices conjugated by `p`. -/
def diagConj (p : Matrix α α ℂ) : Submodule ℂ (Matrix α α ℂ) :=
  LinearMap.range ((conjLinear p).comp diagLinear)

@[simp] theorem mem_diagConj (p X : Matrix α α ℂ) :
    X∈diagConj p ↔ ∃ d : α→ℂ,p*Matrix.diagonal d*p⁻¹=X := Iff.rfl

/-- A sequence of reachable products and the diagonal directions accumulated along it. -/
inductive Chain (A : Matrix α α ℂ) : Matrix α α ℂ → Submodule ℂ (Matrix α α ℂ) → Prop
 | nil : Chain A 1 (diagConj 1)
 | snoc {p U s} : Chain A p U → Reach A s → Chain A (p*s) (U⊔diagConj (p*s))

theorem Chain.reach {A p : Matrix α α ℂ} {U} (h : Chain A p U) : Reach A p := by
  induction h with
  | nil => exact Reach.one A
  | snoc h hs ih => exact ih.mul hs

theorem directions_after_span (A p : Matrix α α ℂ) (hA : IsUnit A)
    (hn : ¬MonomialMatrix A) (hp : IsUnit p) (U : Submodule ℂ (Matrix α α ℂ))
    (h : ∀ s,Reach A s → diagConj (p*s)≤U) : U=⊤ := by
  have hh : ∀ X∈tangentSpan A,p*X*p⁻¹∈U := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨s,hs,d,rfl⟩ := hX
      have he : (p*s)*Matrix.diagonal d*(p*s)⁻¹∈U := h s hs ⟨d,rfl⟩
      simpa only [Matrix.mul_inv_rev,mul_assoc] using he
    | zero => simp
    | add X Y hX hY ihX ihY => simpa only [mul_add,add_mul] using U.add_mem ihX ihY
    | smul c X hX ih => simpa only [Matrix.mul_smul,Matrix.smul_mul] using U.smul_mem c ih
  rw [tangent_top A hA hn] at hh
  apply Submodule.eq_top_iff'.mpr
  intro X
  have ht := hh (p⁻¹*X*p) (Submodule.mem_top)
  have hi := Matrix.mul_nonsing_inv p ((Matrix.isUnit_iff_isUnit_det _).mp hp)
  have he : p*(p⁻¹*X*p)*p⁻¹=X := by
    calc
      _ = (p*p⁻¹)*X*(p*p⁻¹) := by noncomm_ring
      _ = X := by rw [hi]; simp
  rwa [he] at ht

theorem exists_full_chain (A : Matrix α α ℂ) (hA : IsUnit A) (hn : ¬MonomialMatrix A) :
    ∃ p,Chain A p ⊤ := by
  let P : Submodule ℂ (Matrix α α ℂ) → Prop := fun U=>∃ p,Chain A p U
  obtain ⟨U,hU,hmax⟩ := exists_maximal_of_wellFoundedGT P ⟨diagConj 1,1,Chain.nil⟩
  obtain ⟨p,hp⟩ := hU
  have htop : U=⊤ := by
    apply directions_after_span A p hA hn (hp.reach.unit hA) U
    intro s hs
    have hh : P (U⊔diagConj (p*s)) := ⟨p*s,Chain.snoc hp hs⟩
    exact le_trans le_sup_right (hmax hh le_sup_left)
  exact ⟨p,htop ▸ hp⟩

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open Topology
variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- The point of an integral domain's prime spectrum corresponding to the zero ideal. -/
def genericPoint (R : Type*) [CommRing R] [IsDomain R] : PrimeSpectrum R := ⟨⊥,inferInstance⟩

theorem generic_mem_open {U : Set (PrimeSpectrum R)} (hU : IsOpen U) (hne : U.Nonempty) :
    genericPoint R∈U := by
  obtain ⟨x,hx⟩ := hne
  rw [PrimeSpectrum.eq_biUnion_of_isOpen hU] at hx
  obtain ⟨p,hp,hxp⟩ := Set.mem_iUnion₂.mp hx
  apply hp
  change p∉(⊥ : Ideal R)
  intro hz
  have hpz : p=0 := hz
  exact hxp (hpz ▸ x.asIdeal.zero_mem)

theorem constructible_generic_nhds {T : Set (PrimeSpectrum R)} (hT : IsConstructible T) :
    ∃ U : Set (PrimeSpectrum R),IsOpen U ∧ genericPoint R∈U ∧
      ∀ x∈U,(x∈T ↔ genericPoint R∈T) := by
  induction hT using IsConstructible.empty_union_induction with
  | open_retrocompact V hV hc =>
    by_cases hg : genericPoint R∈V
    · exact ⟨V,hV,hg,fun x hx=>⟨fun _=>hg,fun _=>hx⟩⟩
    · have hv : V=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun x hx=>hg (generic_mem_open hV ⟨x,
      hx⟩))
      subst V
      exact ⟨Set.univ,isOpen_univ,Set.mem_univ _,by simp⟩
  | union V hV W hW ihV ihW =>
    obtain ⟨U,hU,hg,hue⟩ := ihV
    obtain ⟨Z,hZ,hgz,hze⟩ := ihW
    exact ⟨U∩Z,hU.inter hZ,⟨hg,hgz⟩,fun x hx=>or_congr (hue x hx.1) (hze x hx.2)⟩
  | compl V hV ih =>
    obtain ⟨U,hU,hg,he⟩ := ih
    exact ⟨U,hU,hg,fun x hx=>not_congr (he x hx)⟩

theorem constructible_contains_basic {T : Set (PrimeSpectrum R)} (hT : IsConstructible T)
    (hg : genericPoint R∈T) : ∃ g : R,g≠0 ∧ (PrimeSpectrum.basicOpen g : Set _)⊆T := by
  obtain ⟨U,hU,hu,he⟩ := constructible_generic_nhds hT
  rw [PrimeSpectrum.eq_biUnion_of_isOpen hU] at hu
  obtain ⟨g,hgU,hgg⟩ := Set.mem_iUnion₂.mp hu
  refine ⟨g,?_,fun x hx=>(he x (hgU hx)).mpr hg⟩
  simpa [genericPoint] using hgg

/-- A dominant finite-presentation map meets an actual nonempty basic open,
not merely its closure. This is the open-image step in positive generation. -/
theorem dominant_open_image (f : R →+* S) (hf : f.FinitePresentation)
    (hinj : Function.Injective f) (p : S) (hp : p≠0) :
    ∃ g : R,g≠0 ∧ (PrimeSpectrum.basicOpen g : Set _)⊆
      PrimeSpectrum.comap f '' (PrimeSpectrum.basicOpen p : Set _) := by
  apply constructible_contains_basic
    (PrimeSpectrum.isConstructible_comap_image hf PrimeSpectrum.isConstructible_basicOpen)
  refine ⟨genericPoint S,?_,?_⟩
  · simpa [genericPoint] using hp
  · apply PrimeSpectrum.ext
    change Ideal.comap f ⊥=⊥
    ext x
    change f x=0 ↔ x=0
    exact map_eq_zero_iff f hinj

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial
variable {ι κ : Type} [Finite ι] [Finite κ]

theorem polynomial_hom_finitePresentation
    (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ) : f.toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial ι ℂ))
  change (f.toRingHom.comp (algebraMap ℂ (MvPolynomial ι ℂ))).FiniteType
  have he : f.toRingHom.comp (algebraMap ℂ (MvPolynomial ι ℂ)) =
      algebraMap ℂ (MvPolynomial κ ℂ) := by ext1 c; exact f.commutes c
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem maximal_avoiding {R : Type*} [CommRing R] [IsJacobsonRing R]
    (I : Ideal R) (hI : I.IsPrime) (p : R) (hp : p∉I) :
    ∃ J : Ideal R,J.IsMaximal ∧ I≤J ∧ p∉J := by
  by_contra h
  push Not at h
  apply hp
  rw [← IsJacobsonRing.out (inferInstance : IsJacobsonRing R) hI.isRadical]
  rw [Ideal.jacobson,Ideal.mem_sInf]
  intro J hJ
  exact h J hJ.2 hJ.1

/-- Point-level consequence of Chevalley and the Nullstellensatz. -/
theorem polynomial_open_image (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ)
    (hinj : Function.Injective f) (p : MvPolynomial κ ℂ) (hp : p≠0) :
    ∃ g : MvPolynomial ι ℂ,g≠0 ∧ ∀ y : ι→ℂ,aeval y g≠0 →
      ∃ x : κ→ℂ,aeval x p≠0 ∧ ∀ i,aeval x (f (X i))=y i := by
  obtain ⟨g,hg,hgi⟩ := dominant_open_image f.toRingHom (polynomial_hom_finitePresentation f)
    hinj p hp
  refine ⟨g,hg,?_⟩
  intro y hy
  have hyp : pointToPoint (k := ℂ) y∈PrimeSpectrum.basicOpen g := by
    change g∉vanishingIdeal ℂ {y}
    simpa only [mem_vanishingIdeal_singleton_iff] using hy
  obtain ⟨q,hqp,hq⟩ := hgi hyp
  obtain ⟨J,hJ,hqJ,hpJ⟩ := maximal_avoiding q.asIdeal q.isPrime p hqp
  have hcontract : Ideal.comap f.toRingHom J=vanishingIdeal ℂ {y} := by
    symm
    apply Ideal.IsMaximal.eq_of_le (inferInstance : (vanishingIdeal ℂ {y}).IsMaximal)
      (Ideal.comap_ne_top _ hJ.ne_top)
    have he := congrArg PrimeSpectrum.asIdeal hq
    change Ideal.comap f.toRingHom q.asIdeal=vanishingIdeal ℂ {y} at he
    rw [← he]
    exact Ideal.comap_mono hqJ
  obtain ⟨x,hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hJ
  refine ⟨x,?_,?_⟩
  · rw [hx] at hpJ
    simpa only [mem_vanishingIdeal_singleton_iff] using hpJ
  · intro i
    have hpoly : X i-C (y i)∈vanishingIdeal ℂ {y} := by
      rw [mem_vanishingIdeal_singleton_iff]; simp
    rw [← hcontract] at hpoly
    change f (X i-C (y i))∈J at hpoly
    rw [hx,mem_vanishingIdeal_singleton_iff] at hpoly
    apply sub_eq_zero.mp
    simpa using hpoly

end ExactFourier.PositiveGeneration

end
end

section
noncomputable section
namespace ExactFourier.PositiveGeneration
open MvPolynomial Filter Topology
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The map on complex coordinate spaces induced by a polynomial substitution. -/
def polynomialMap (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ) (x : κ→ℂ) : ι→ℂ :=
  fun i=>aeval x (f (X i))

theorem eval_polynomialMap
    {ι : Type} {κ : Type}   (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ)
    (x : κ→ℂ) (p : MvPolynomial ι ℂ) :
    aeval (polynomialMap f x) p=aeval x (f p) := by
  have he : (aeval x).comp f=aeval (polynomialMap f x) := by ext; simp [polynomialMap]
  exact (AlgHom.congr_fun he p).symm

/-- A surjective strict derivative certifies dominance, with no dimension
reduction or extra algebraic hypotheses. -/
theorem injective_of_submersion (f : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ)
    (x : κ→ℂ) (d : (κ→ℂ) →L[ℂ] (ι→ℂ))
    (hd : HasStrictFDerivAt (polynomialMap f) d x) (hs : d.range=⊤) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro p hp
  have hzero : (fun y : ι→ℂ=>aeval y p)=ᶠ[𝓝 (polynomialMap f x)] 0 := by
    rw [← hd.map_nhds_eq_of_surj hs]
    change ∀ᶠ y in 𝓝 x,aeval (polynomialMap f y) p=0
    exact Filter.Eventually.of_forall (fun y=>by rw [eval_polynomialMap,hp,map_zero])
  have hall := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ)
    p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ (polynomialMap f x)) hzero
  apply MvPolynomial.funext
  intro y
  simpa using hall (Set.mem_univ y)

end ExactFourier.PositiveGeneration

end
end

end Complexity
