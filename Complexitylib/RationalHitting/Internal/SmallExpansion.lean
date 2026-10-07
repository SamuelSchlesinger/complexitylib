/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.LaurentReduction
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Rational hitting lists: small expansion

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/SmallExpansion.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.SmallExpansion
open Module Polynomial
open scoped BigOperators
open LaurentReduction Expansion
noncomputable section
variable {K : Type*} [Field K]

/-- The coefficient realization of P_M(K), with its exact degree bound. -/
def polynomialMap (M : ℕ) : (Fin M → K) →ₗ[K] K[X] :=
  (Polynomial.degreeLT K M).subtype.comp (Polynomial.degreeLTEquiv K M).symm.toLinearMap

lemma polynomialMap_injective (M : ℕ) : Function.Injective (polynomialMap (K := K) M) :=
  Subtype.val_injective.comp (Polynomial.degreeLTEquiv K M).symm.injective

@[simp] lemma polynomialMap_coeff (M : ℕ) (x : Fin M → K) (j : Fin M) :
    (polynomialMap M x).coeff j = x j := by
  exact congrFun ((Polynomial.degreeLTEquiv K M).apply_symm_apply x) j

lemma polynomialMap_mem (M : ℕ) (x : Fin M → K) :
    polynomialMap M x ∈ Polynomial.degreeLT K M :=
  ((Polynomial.degreeLTEquiv K M).symm x).property

lemma polynomialMap_coeff_high (M : ℕ) (x : Fin M → K) (j : ℕ) (hj : M ≤ j) :
    (polynomialMap M x).coeff j = 0 := by
  apply coeff_eq_zero_of_degree_lt
  exact (Polynomial.mem_degreeLT.mp (polynomialMap_mem M x)).trans_le (by exact_mod_cast hj)

/-- The polynomial subspace corresponding to a subspace of coefficient vectors. -/
def polynomialSpace {M : ℕ} (V : Submodule K (Fin M → K)) : Submodule K K[X] :=
  V.map (polynomialMap M)

lemma finrank_polynomialSpace {M : ℕ} (V : Submodule K (Fin M → K)) :
    finrank K (polynomialSpace V) = finrank K V :=
  finrank_map_injective _ (polynomialMap_injective M) V

lemma polynomialSpace_bound {M : ℕ} (V : Submodule K (Fin M → K)) :
    ∀ f ∈ polynomialSpace V, f ≠ 0 → f.natDegree < M := by
  rintro f ⟨x, hx, rfl⟩ hn
  exact (natDegree_lt_iff_degree_lt hn).mpr (Polynomial.mem_degreeLT.mp (polynomialMap_mem M x))

/-- Change coefficient vectors to Taylor coordinates at the specified point. -/
def taylorCoordinates (M : ℕ) (a : K) : (Fin M → K) ≃ₗ[K] (Fin M → K) :=
  (Polynomial.degreeLTEquiv K M).symm.trans
    ((Polynomial.taylorLinearEquiv a M).trans (Polynomial.degreeLTEquiv K M))

lemma taylorCoordinates_apply (M : ℕ) (a : K) (x : Fin M → K) (j : Fin M) :
    taylorCoordinates M a x j = (taylor a (polynomialMap M x)).coeff j := rfl

/-- Reverse the order of a finite coefficient vector. -/
def reverseCoordinates (M : ℕ) : (Fin M → K) ≃ₗ[K] (Fin M → K) where
  toFun x j := x j.rev
  invFun x j := x j.rev
  left_inv := by intro x; funext j; simp
  right_inv := by intro x; funext j; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Take Taylor coordinates and reverse their order. -/
def reverseTaylorCoordinates (M : ℕ) (a : K) : (Fin M → K) ≃ₗ[K] (Fin M → K) :=
  (taylorCoordinates M a).trans (reverseCoordinates M)

/-- The reverse-Taylor test on bounded-degree polynomials multiplies each
Taylor coefficient by t^a and places it in output degree M-1-a. -/
def testMap (M : ℕ) (a : K) : (Fin M → F K) →ₗ[F K] (Fin M → F K) :=
  conjugatedWeight (taylorCoordinates M a) (reverseTaylorCoordinates M a) Fin.val

lemma testMap_injective (M : ℕ) (a : K) : Function.Injective (testMap M a) :=
  conjugatedWeight_injective _ _ _

/-- Kernel of the low Taylor projection is precisely the vanishing filtration. -/
lemma map_taylor_projection_kernel (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) :
    (V ⊓ ((lowProjection Fin.val A).comp (taylorCoordinates M a).toLinearMap).ker).map
      (polynomialMap M) = vanishingFiltration (polynomialSpace V) a (A+1) := by
  ext f
  constructor
  · rintro ⟨x, ⟨hxV, hx⟩, rfl⟩
    refine ⟨⟨x, hxV, rfl⟩, ?_⟩
    intro j hj
    by_cases hjM : j < M
    · have he := congrFun hx (⟨⟨j, hjM⟩, by change j ≤ A; omega⟩ : {i : Fin M // i.val ≤ A})
      exact he
    · apply coeff_eq_zero_of_degree_lt
      have hdeg := Polynomial.mem_degreeLT.mp (polynomialMap_mem M x)
      rw [degree_taylor]
      exact hdeg.trans_le (by exact_mod_cast (Nat.le_of_not_gt hjM))
  · rintro ⟨⟨x, hxV, rfl⟩, hx⟩
    refine ⟨x, ⟨hxV, ?_⟩, rfl⟩
    change (lowProjection Fin.val A) (taylorCoordinates M a x) = 0
    funext j
    exact hx j.val.val (by have := j.property; omega)

/-- The output-side low reverse coordinates mean high ordinary Taylor order. -/
lemma map_reverseTaylor_lowSupported (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) :
    ((V.map (reverseTaylorCoordinates M a).toLinearMap) ⊓ lowSupported Fin.val A).map
      ((polynomialMap M).comp (reverseTaylorCoordinates M a).symm.toLinearMap) =
      vanishingFiltration (polynomialSpace V) a (M-1-A) := by
  ext f
  constructor
  · rintro ⟨y, ⟨⟨x, hxV, rfl⟩, hy⟩, rfl⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    refine ⟨⟨x, hxV, rfl⟩, ?_⟩
    intro j hj
    have hjM : j < M := by omega
    have hh := hy (Fin.rev ⟨j, hjM⟩) (by simp only [Fin.val_rev]; omega)
    change taylorCoordinates M a x ((Fin.rev ⟨j, hjM⟩).rev) = 0 at hh
    simpa only [Fin.rev_rev, taylorCoordinates_apply] using hh
  · rintro ⟨⟨x, hxV, rfl⟩, hx⟩
    refine ⟨reverseTaylorCoordinates M a x, ⟨⟨x, hxV, rfl⟩, ?_⟩, ?_⟩
    · intro j hj
      change taylorCoordinates M a x j.rev = 0
      exact hx j.rev.val (by simp only [Fin.val_rev]; omega)
    · simp


lemma finrank_lowTaylor (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) {h : ℕ}
    (b : Basis (Fin h) K (polynomialSpace V))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a)) :
    finrank K ((V.map (taylorCoordinates M a).toLinearMap).map (lowProjection Fin.val A)) =
      Fintype.card {j : Fin h // (b j : K[X]).rootMultiplicity a ≤ A} := by
  classical
  have hd := finrank_map_add_finrank_inf_ker
    ((lowProjection Fin.val A).comp (taylorCoordinates M a).toLinearMap) V
  have hk := finrank_map_injective (polynomialMap M) (polynomialMap_injective M)
    (V ⊓ ((lowProjection Fin.val A).comp (taylorCoordinates M a).toLinearMap).ker)
  rw [map_taylor_projection_kernel, finrank_vanishingFiltration b a hb] at hk
  have hdim : finrank K V = h := by
    rw [← finrank_polynomialSpace, Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [Submodule.map_comp, ← hk, hdim] at hd
  have hc : Fintype.card {j : Fin h // (b j : K[X]).rootMultiplicity a ≤ A} +
      Fintype.card {j : Fin h // A+1 ≤ (b j : K[X]).rootMultiplicity a} = h := by
    simp only [Fintype.card_subtype, Nat.add_one_le_iff, ← not_le]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun j : Fin h => (b j : K[X]).rootMultiplicity a ≤ A)
  omega

lemma finrank_reverseTaylor (M : ℕ) (a : K) (A : ℕ)
    (V : Submodule K (Fin M → K)) {h : ℕ}
    (b : Basis (Fin h) K (polynomialSpace V))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a)) :
    finrank K ↥((V.map (reverseTaylorCoordinates M a).toLinearMap) ⊓ lowSupported Fin.val A) =
      Fintype.card {j : Fin h // M-1-A ≤ (b j : K[X]).rootMultiplicity a} := by
  rw [← finrank_map_injective ((polynomialMap M).comp (reverseTaylorCoordinates M
    a).symm.toLinearMap)
    ((polynomialMap_injective M).comp (reverseTaylorCoordinates M a).symm.injective),
    map_reverseTaylor_lowSupported, finrank_vanishingFiltration b a hb]

/-- The rank form of order reversal, at every threshold. -/
theorem order_reversal_counts (M : ℕ) (a : K) (A : ℕ)
    (U W : Submodule (F K) (Fin M → F K)) (hW : U.map (testMap M a) ≤ W)
    {k l : ℕ} (b : Basis (Fin k) K (polynomialSpace (reducedSubspace U)))
    (c : Basis (Fin l) K (polynomialSpace (reducedSubspace W)))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (hc : Function.Injective (fun j => (c j : K[X]).rootMultiplicity a)) :
    Fintype.card {j : Fin k // (b j : K[X]).rootMultiplicity a ≤ A} ≤
      Fintype.card {j : Fin l // M-1-A ≤ (c j : K[X]).rootMultiplicity a} := by
  have hh := conjugated_filtration_rank (taylorCoordinates M a) (reverseTaylorCoordinates M a)
    Fin.val A U W hW
  rwa [finrank_lowTaylor M a A _ b hb, finrank_reverseTaylor M a A _ c hc] at hh

/-- Counting all thresholds counts each order with its exact multiplicity. -/
lemma sum_threshold_counts {h : ℕ} (d : Fin h → ℕ) (L : ℕ) :
    (∑ A ∈ Finset.range L, Fintype.card {j : Fin h // d j ≤ A}) =
      ∑ j, (L - d j) := by
  classical
  simp only [Fintype.card_subtype]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : (Finset.range L).filter (fun A => d j ≤ A) = Finset.Ico (d j) L := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [← Finset.card_filter, he, Nat.card_Ico]

lemma sum_reversed_counts {h : ℕ} (d : Fin h → ℕ) (L : ℕ) (hd : ∀ j, d j ≤ L) :
    (∑ A ∈ Finset.range L, Fintype.card {j : Fin h // L-A ≤ d j}) = ∑ j, d j := by
  have he : ∀ A, (fun j : Fin h => L-A ≤ d j) = (fun j : Fin h => L-d j ≤ A) := by
    intro A
    funext j
    exact propext (by omega)
  simp_rw [he]
  rw [sum_threshold_counts]
  apply Finset.sum_congr rfl
  intro j _
  have := hd j
  omega

/-- Summation of order reversal, without selecting incompatible auxiliary
subspaces: all inequalities concern the fixed filtration of the same W. -/
theorem order_reversal_sum (M : ℕ) (a : K)
    (U W : Submodule (F K) (Fin M → F K)) (hW : U.map (testMap M a) ≤ W)
    {k l : ℕ} (b : Basis (Fin k) K (polynomialSpace (reducedSubspace U)))
    (c : Basis (Fin l) K (polynomialSpace (reducedSubspace W)))
    (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (hc : Function.Injective (fun j => (c j : K[X]).rootMultiplicity a)) :
    k * (M-1) ≤ (∑ j, (b j : K[X]).rootMultiplicity a) +
      (∑ j, (c j : K[X]).rootMultiplicity a) := by
  classical
  have hbd : ∀ j, (b j : K[X]).rootMultiplicity a ≤ M-1 := by
    intro j
    have hle : (b j : K[X]).rootMultiplicity a ≤ (b j : K[X]).natDegree := by
      rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
      exact (natTrailingDegree_le_natDegree _).trans (le_of_eq (natDegree_taylor _ _))
    apply hle.trans
    have hh := polynomialSpace_bound (reducedSubspace U) _ (b j).property
      (fun hz => b.ne_zero j (Subtype.ext hz))
    omega
  have hcd : ∀ j, (c j : K[X]).rootMultiplicity a ≤ M-1 := by
    intro j
    have hle : (c j : K[X]).rootMultiplicity a ≤ (c j : K[X]).natDegree := by
      rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
      exact (natTrailingDegree_le_natDegree _).trans (le_of_eq (natDegree_taylor _ _))
    apply hle.trans
    have hh := polynomialSpace_bound (reducedSubspace W) _ (c j).property
      (fun hz => c.ne_zero j (Subtype.ext hz))
    omega
  have hh := Finset.sum_le_sum (s := Finset.range (M-1))
    (fun A _ => order_reversal_counts M a A U W hW b c hb hc)
  rw [sum_threshold_counts, sum_reversed_counts _ _ hcd] at hh
  have he : (∑ j, (M-1 - (b j : K[X]).rootMultiplicity a)) +
      (∑ j, (b j : K[X]).rootMultiplicity a) = k * (M-1) := by
    rw [← Finset.sum_add_distrib]
    simp only [Nat.sub_add_cancel (hbd _), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  omega


lemma sum_fin_val_le_square (h : ℕ) : (∑ j : Fin h, j.val) ≤ h*h := by
  calc
    _ ≤ ∑ _j : Fin h, h := Finset.sum_le_sum fun j _ => Nat.le_of_lt j.isLt
    _ = h*h := by simp

lemma expansion_numeric (w B M N k l : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2*w^3*B) (hk : 1 ≤ k) (hkB : k ≤ B)
    (hh : w * (k*(M-1)) ≤ k*(N-1) + w*(∑ j : Fin k, j.val) +
      (l*(M-1) + w*(∑ j : Fin l, j.val))) :
    (w-1)*k < l := by
  by_contra! hl
  have hk2 := sum_fin_val_le_square k
  have hl2 := sum_fin_val_le_square l
  have hh' : w*(k*(M-1)) ≤ k*(N-1) + w*(k*k) +
      (l*(M-1) + w*(l*l)) := by
    exact hh.trans (by gcongr)
  have hgap : M-1 = N-1 + 2*w^3*B := by omega
  have hw' : w-1+1 = w := by omega
  have hmul := Nat.mul_le_mul_right (M-1) hl
  have hlSq : l*l ≤ ((w-1)*k)*((w-1)*k) := Nat.mul_self_le_mul_self hl
  have hwSq : (w-1)*(w-1)+1 ≤ w*w := by nlinarith
  have hsq : k*k + l*l ≤ w*w*(k*k) := by
    have hm := Nat.mul_le_mul_right (k*k) hwSq
    nlinarith
  have hkSq : k*k ≤ B*k := Nat.mul_le_mul_right k hkB
  have hfinal : w*(k*k + l*l) ≤ w^3*B*k := by
    calc
      _ ≤ w*(w*w*(k*k)) := Nat.mul_le_mul_left w hsq
      _ ≤ w*(w*w*(B*k)) := by gcongr
      _ = w^3*B*k := by ring
  have hB : 0 < B := by omega
  have hpos : 0 < w^3*B*k := by positivity
  have hbase : k*(M-1) ≤ k*(N-1)+w*(k*k+l*l) := by
    have he : w*(k*(M-1)) = k*(M-1) + (w-1)*k*(M-1) := by
      calc
        _ = (1+(w-1))*(k*(M-1)) := by congr 1; omega
        _ = _ := by ring
    have hb : w*(k*(M-1)) ≤ k*(N-1)+w*(k*k+l*l)+(w-1)*k*(M-1) := by
      calc
        _ ≤ k*(N-1)+w*(k*k)+((w-1)*k*(M-1)+w*(l*l)) :=
          hh'.trans (by gcongr)
        _ = _ := by ring
    rw [he] at hb
    exact Nat.le_of_add_le_add_right hb
  have hneed : k*(2*w^3*B) ≤ w*(k*k+l*l) := by
    rw [hgap] at hbase
    nlinarith only [hbase]
  nlinarith

lemma reduced_degree_bound {M N : ℕ} (U : Submodule (F K) (Fin M → F K))
    (hU : ∀ x ∈ U, ∀ j : Fin M, N ≤ j.val → x j = 0) :
    ∀ f ∈ polynomialSpace (reducedSubspace U), f ≠ 0 → f.natDegree < N := by
  have hr : ∀ y ∈ reducedSubspace U, ∀ j : Fin M, N ≤ j.val → y j = 0 := by
    intro y hy
    obtain ⟨b⟩ := exists_integralFrame U
    have hyy : y ∈ reducedSet U := by
      rw [reducedSet_eq_span b]
      rwa [reducedSubspace_eq_span b] at hy
    obtain ⟨x, hx, hI, rfl⟩ := hyy
    intro j hj
    simp only [reduce, hU x hx j hj, reduction_zero]
  rintro f ⟨x, hx, rfl⟩ hn
  apply (natDegree_lt_iff_degree_lt hn).mpr
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  by_cases hjM : j < M
  · exact (polynomialMap_coeff M x ⟨j, hjM⟩).trans (hr x hx ⟨j, hjM⟩ hj)
  · exact polynomialMap_coeff_high M x j (Nat.le_of_not_gt hjM)

/-- Small-subspace expansion in monomial coordinates in a common output space.
The input subspace is restricted to degrees < N, not changed by padding. -/

theorem small_expansion [CharZero K] (w B M N : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2*w^3*B) (points : Fin w → K) (hp : Function.Injective points)
    (U W : Submodule (F K) (Fin M → F K))
    (hU : ∀ x ∈ U, ∀ j : Fin M, N ≤ j.val → x j = 0)
    (hW : ∀ i, U.map (testMap M (points i)) ≤ W)
    (hk : 1 ≤ finrank (F K) U) (hkB : finrank (F K) U ≤ B) :
    (w-1) * finrank (F K) U < finrank (F K) W := by
  classical
  let k := finrank (F K) U
  let l := finrank (F K) W
  let V := polynomialSpace (reducedSubspace U)
  let Z := polynomialSpace (reducedSubspace W)
  let : Module.Finite K V := by
    dsimp [V, polynomialSpace]
    exact Module.Finite.map (reducedSubspace U) (polynomialMap M)
  let : Module.Finite K Z := by
    dsimp [Z, polynomialSpace]
    exact Module.Finite.map (reducedSubspace W) (polynomialMap M)
  have hVdim : finrank K V = k := by
    rw [finrank_polynomialSpace, finrank_reducedSubspace]
  have hZdim : finrank K Z = l := by
    rw [finrank_polynomialSpace, finrank_reducedSubspace]
  let b : Basis (Fin k) K V := (Module.finBasis K V).reindex (finCongr hVdim)
  let c : Basis (Fin l) K Z := (Module.finBasis K Z).reindex (finCongr hZdim)
  have hV := reduced_degree_bound U hU
  have hZ := polynomialSpace_bound (reducedSubspace W)
  choose be hbe using (fun i : Fin w => exists_echelon_basis_at N V b hV (points i))
  choose ce hce using (fun i : Fin w => exists_echelon_basis_at M Z c hZ (points i))
  have horder := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => order_reversal_sum M (points i) U W (hW i) (be i) (ce i) (hbe i) (hce i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib] at horder
  have hWrU := wronskian_order_bound N b points hp be hV hbe
  have hWrW := wronskian_order_bound M c points hp ce hZ hce
  exact expansion_numeric w B M N k l hw hN hMN hk hkB
    (horder.trans (Nat.add_le_add hWrU hWrW))

end
end RationalHitting.SmallExpansion

end Complexity
