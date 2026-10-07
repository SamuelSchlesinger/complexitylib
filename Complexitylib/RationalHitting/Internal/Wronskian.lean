/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Affine

/-!
# Rational hitting lists: wronskian

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Wronskian.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.Expansion
open Polynomial Module
open scoped BigOperators Polynomial

noncomputable section

/-- The Wronskian with derivative orders 0, ..., h - 1. -/
def wronskian {K : Type*} [CommRing K] {h : ℕ} (f : Fin h → K[X]) : K[X] :=
  Matrix.det (Matrix.of fun i j : Fin h => derivative^[i.val] (f j))

lemma coeff_prod_sum_degrees {K ι : Type*} [CommSemiring K] (s : Finset ι)
    (f : ι → K[X]) (d : ι → ℕ) (hd : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
      coeff_mul_add_eq_of_natDegree_le (hd a (Finset.mem_insert_self _ _))]
    · rw [ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))]
    · exact (natDegree_prod_le s f).trans
        (Finset.sum_le_sum fun i hi => hd i (Finset.mem_insert_of_mem hi))

lemma coeff_det_column_degrees {K ι : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K[X]) (d : ι → ℕ)
    (hd : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.coeff (∑ j, d j) = Matrix.det (Matrix.of fun i j => (A i j).coeff (d j)) := by
  simp only [Matrix.det_apply, finsetSum_coeff, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro g _
  rw [coeff_smul, coeff_prod_sum_degrees _ _ d (fun j _ => hd (g j) j)]

lemma natDegree_scaled_derivative_le {K : Type*} [CommRing K]
    (f : K[X]) (r : ℕ) :
    (X ^ r * derivative^[r] f).natDegree ≤ f.natDegree := by
  by_cases hr : r ≤ f.natDegree
  · calc
      (X ^ r * derivative^[r] f).natDegree
          ≤ (X ^ r : K[X]).natDegree + (derivative^[r] f).natDegree := natDegree_mul_le
      _ ≤ r + (f.natDegree - r) := Nat.add_le_add (natDegree_X_pow_le r)
        (natDegree_iterate_derivative f r)
      _ = f.natDegree := Nat.add_sub_of_le hr
  · rw [iterate_derivative_eq_zero (Nat.lt_of_not_ge hr), mul_zero, natDegree_zero]
    exact Nat.zero_le _

lemma coeff_scaled_derivative {K : Type*} [CommRing K]
    (f : K[X]) (r : ℕ) :
    (X ^ r * derivative^[r] f).coeff f.natDegree =
      (f.natDegree.descFactorial r : K) * f.leadingCoeff := by
  by_cases hr : r ≤ f.natDegree
  · rw [coeff_X_pow_mul', ite_eq_left hr, coeff_iterate_derivative,
      Nat.sub_add_cancel hr, nsmul_eq_mul, coeff_natDegree]
  · rw [iterate_derivative_eq_zero (Nat.lt_of_not_ge hr), mul_zero, coeff_zero,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hr), Nat.cast_zero, zero_mul]

lemma wronskian_ne_zero_of_distinct_degrees {K : Type*} [Field K] [CharZero K]
    {h : ℕ} (f : Fin h → K[X]) (hf : ∀ j, f j ≠ 0)
    (hd : Function.Injective (fun j => (f j).natDegree)) :
    wronskian f ≠ 0 := by
  let A : Matrix (Fin h) (Fin h) K[X] :=
    Matrix.of fun i j => X ^ i.val * derivative^[i.val] (f j)
  have hcoeff : A.det.coeff (∑ j, (f j).natDegree) =
      Matrix.det (Matrix.of fun i j : Fin h => ((f j).natDegree.descFactorial i.val : K) *
        (f j).leadingCoeff) := by
    rw [coeff_det_column_degrees A (fun j => (f j).natDegree)
      (fun i j => natDegree_scaled_derivative_le (f j) i.val)]
    congr 1
    ext i j
    exact coeff_scaled_derivative (f j) i.val
  have hfall : Matrix.det (Matrix.of fun i j : Fin h => ((f j).natDegree.descFactorial i.val :
    K)) ≠ 0 := by
    let p : Fin h → K[X] := fun j => descPochhammer K j.val
    have hp := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun j : Fin h => ((f j).natDegree : K)) p
      (fun j => by simp [p]) (fun j => monic_descPochhammer K j.val)
    have he : (Matrix.of fun i j : Fin h => ((f j).natDegree.descFactorial i.val : K)) =
        (Matrix.of fun i j : Fin h => (p j).eval ((f i).natDegree : K)).transpose := by
      ext i j
      simp [p, descPochhammer_eval_eq_descFactorial]
    rw [he, Matrix.det_transpose, ← hp, Matrix.det_vandermonde_ne_zero_iff]
    exact (Nat.cast_injective (R := K)).comp hd
  have htop : A.det.coeff (∑ j, (f j).natDegree) ≠ 0 := by
    rw [hcoeff]
    have he : (Matrix.of fun i j : Fin h => ((f j).natDegree.descFactorial i.val : K) *
        (f j).leadingCoeff) =
        Matrix.of (fun i j : Fin h => (f j).leadingCoeff *
          ((f j).natDegree.descFactorial i.val : K)) := by
      ext i j
      exact mul_comm _ _
    rw [he]
    have hscale := Matrix.det_mul_row (fun j => (f j).leadingCoeff)
      (Matrix.of fun i j : Fin h => ((f j).natDegree.descFactorial i.val : K))
    simp only [Matrix.of_apply] at hscale
    rw [hscale]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => leadingCoeff_ne_zero.mpr (hf j)) hfall
  intro hw
  apply htop
  have hz : A.det = 0 := by
    change Matrix.det (Matrix.of fun i j : Fin h => (X : K[X]) ^ i.val * derivative^[i.val] (f
      j)) = 0
    have hscale := Matrix.det_mul_column (fun i : Fin h => (X : K[X]) ^ i.val)
      (Matrix.of fun i j : Fin h => derivative^[i.val] (f j))
    simp only [Matrix.of_apply] at hscale
    rw [hscale]
    change (∏ i : Fin h, (X : K[X]) ^ i.val) * wronskian f = 0
    rw [hw, mul_zero]
  rw [hz, coeff_zero]


/-- Factoring prescribed powers from the columns keeps track of the first
possible coefficient of a determinant. -/
lemma det_factor_column_orders {K ι : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K[X]) (d : ι → ℕ)
    (hd : ∀ i j, X ^ d j ∣ A i j) :
    ∃ B : Matrix ι ι K[X],
      A.det = X ^ (∑ j, d j) * B.det ∧
      (∀ i j, (B i j).coeff 0 = (A i j).coeff (d j)) := by
  classical
  choose B hB using hd
  refine ⟨Matrix.of B, ?_, ?_⟩
  · have hA : A = Matrix.of (fun i j => X ^ d j * (Matrix.of B) i j) := by
      apply Matrix.ext
      intro i j
      exact hB i j
    rw [hA, Matrix.det_mul_row, ← Finset.prod_pow_eq_pow_sum]
  · intro i j
    simp only [Matrix.of_apply]
    rw [hB i j, coeff_X_pow_mul']
    simp

lemma coeff_scaled_derivative_at {K : Type*} [CommRing K]
    (f : K[X]) (r d : ℕ) :
    (X ^ r * derivative^[r] f).coeff d =
      (d.descFactorial r : K) * f.coeff d := by
  by_cases hr : r ≤ d
  · rw [coeff_X_pow_mul', ite_eq_left hr, coeff_iterate_derivative,
      Nat.sub_add_cancel hr, nsmul_eq_mul]
  · rw [coeff_X_pow_mul', ite_eq_right hr,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hr), Nat.cast_zero, zero_mul]

lemma scaled_derivative_order {K : Type*} [CommRing K]
    (f : K[X]) (r : ℕ) : X ^ f.natTrailingDegree ∣ X ^ r * derivative^[r] f := by
  apply X_pow_dvd_iff.mpr
  intro a ha
  rw [coeff_scaled_derivative_at, coeff_eq_zero_of_lt_natTrailingDegree ha, mul_zero]

/-- The local order formula at zero, before translation to an arbitrary point.
The sum of the row numbers is C(h,2). -/
lemma wronskian_order_of_distinct_orders {K : Type*} [Field K] [CharZero K]
    {h : ℕ} (f : Fin h → K[X]) (hf : ∀ j, f j ≠ 0)
    (hd : Function.Injective (fun j => (f j).natTrailingDegree)) :
    wronskian f ≠ 0 ∧
      (wronskian f).natTrailingDegree + (∑ i : Fin h, i.val) =
        ∑ j, (f j).natTrailingDegree := by
  let A : Matrix (Fin h) (Fin h) K[X] :=
    Matrix.of fun i j => X ^ i.val * derivative^[i.val] (f j)
  obtain ⟨B, hdet, hB⟩ := det_factor_column_orders A
    (fun j => (f j).natTrailingDegree) (fun i j => scaled_derivative_order (f j) i.val)
  have hfall : Matrix.det (Matrix.of fun i j : Fin h =>
      ((f j).natTrailingDegree.descFactorial i.val : K)) ≠ 0 := by
    let p : Fin h → K[X] := fun j => descPochhammer K j.val
    have hp := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun j : Fin h => ((f j).natTrailingDegree : K)) p
      (fun j => by simp [p]) (fun j => monic_descPochhammer K j.val)
    have he : (Matrix.of fun i j : Fin h =>
        ((f j).natTrailingDegree.descFactorial i.val : K)) =
        (Matrix.of fun i j : Fin h => (p j).eval ((f i).natTrailingDegree : K)).transpose := by
      ext i j
      simp [p, descPochhammer_eval_eq_descFactorial]
    rw [he, Matrix.det_transpose, ← hp, Matrix.det_vandermonde_ne_zero_iff]
    exact (Nat.cast_injective (R := K)).comp hd
  have hBc : B.det.coeff 0 ≠ 0 := by
    have he : B.map (evalRingHom (0 : K)) =
        Matrix.of (fun i j : Fin h => (f j).trailingCoeff *
          ((f j).natTrailingDegree.descFactorial i.val : K)) := by
      ext i j
      change eval (0 : K) (B i j) = _
      rw [← coeff_zero_eq_eval_zero, hB i j]
      change (X ^ i.val * derivative^[i.val] (f j)).coeff (f j).natTrailingDegree = _
      rw [coeff_scaled_derivative_at]
      exact mul_comm _ _
    rw [coeff_zero_eq_eval_zero]
    change (evalRingHom (0 : K)) B.det ≠ 0
    rw [RingHom.map_det]
    change (B.map (evalRingHom (0 : K))).det ≠ 0
    rw [he]
    have hscale := Matrix.det_mul_row (fun j => (f j).trailingCoeff)
      (Matrix.of fun i j : Fin h => ((f j).natTrailingDegree.descFactorial i.val : K))
    simp only [Matrix.of_apply] at hscale
    rw [hscale]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
      trailingCoeff_nonzero_iff_nonzero.mpr (hf j)) hfall
  have hB0 : B.det ≠ 0 := by intro hz; simp [hz] at hBc
  have hA0 : A.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hB0
  have hscale : A.det = X ^ (∑ i : Fin h, i.val) * wronskian f := by
    have he := Matrix.det_mul_column (fun i : Fin h => (X : K[X]) ^ i.val)
      (Matrix.of fun i j : Fin h => derivative^[i.val] (f j))
    simp only [Matrix.of_apply] at he
    change _ = _ * Matrix.det (Matrix.of fun i j : Fin h => derivative^[i.val] (f j))
    rw [← Finset.prod_pow_eq_pow_sum]
    exact he
  have hw : wronskian f ≠ 0 := by
    intro hz
    rw [hscale, hz, mul_zero] at hA0
    exact hA0 rfl
  refine ⟨hw, ?_⟩
  have ho : A.det.natTrailingDegree = ∑ j, (f j).natTrailingDegree := by
    rw [hdet, mul_comm, natTrailingDegree_mul_X_pow hB0,
      natTrailingDegree_eq_zero.mpr (Or.inr hBc), zero_add]
  rw [hscale, mul_comm, natTrailingDegree_mul_X_pow hw] at ho
  exact ho


/-- Polynomial row reduction, derived rather than assumed: every bounded-degree
subspace has a basis with distinct largest degrees. -/
lemma exists_degree_echelon_family {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X])
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    ∃ (h : ℕ) (f : Fin h → K[X]), LinearIndependent K f ∧
      Submodule.span K (Set.range f) = V ∧
      Function.Injective (fun i => (f i).natDegree) := by
  classical
  induction d generalizing V with
  | zero =>
    have hzero : V = ⊥ := by
      apply le_antisymm _ bot_le
      intro f hf
      change f = 0
      by_contra hn
      exact Nat.not_lt_zero _ (hV f hf hn)
    refine ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, ?_⟩
    · simp [hzero]
    · intro i; exact Fin.elim0 i
  | succ d ih =>
    by_cases hall : ∀ f ∈ V, f.coeff d = 0
    · apply ih V
      intro f hf hn
      have hl := hV f hf hn
      have hne : f.natDegree ≠ d := by
        intro he
        have hc := hall f hf
        rw [← he, coeff_natDegree] at hc
        exact (leadingCoeff_ne_zero.mpr hn) hc
      omega
    · push Not at hall
      obtain ⟨f, hfV, hfc⟩ := hall
      have hf0 : f ≠ 0 := by intro hz; simp [hz] at hfc
      have hfd : f.natDegree = d := by
        have hl := hV f hfV hf0
        have hr := le_natDegree_of_ne_zero hfc
        omega
      let W : Submodule K K[X] := V ⊓ LinearMap.ker (lcoeff K d)
      have hW : ∀ g ∈ W, g ≠ 0 → g.natDegree < d := by
        intro g hg hn
        have hl := hV g hg.1 hn
        have hc : g.coeff d = 0 := hg.2
        have hne : g.natDegree ≠ d := by
          intro he
          rw [← he, coeff_natDegree] at hc
          exact (leadingCoeff_ne_zero.mpr hn) hc
        omega
      obtain ⟨h, g, hgLI, hgspan, hgdeg⟩ := ih W hW
      have hgmem : ∀ j, g j ∈ W := by
        intro j
        rw [← hgspan]
        exact Submodule.subset_span ⟨j, rfl⟩
      have hnot : f ∉ Submodule.span K (Set.range g) := by
        rw [hgspan]
        exact fun hh => hfc hh.2
      refine ⟨h + 1, Fin.cons f g, hgLI.finCons hnot, ?_, ?_⟩
      · apply le_antisymm
        · apply Submodule.span_le.mpr
          rintro _ ⟨j, rfl⟩
          refine Fin.cases ?_ (fun i => ?_) j
          · exact hfV
          · exact (hgmem i).1
        · intro u hu
          let c : K := u.coeff d / f.coeff d
          have hr : u - c • f ∈ W := by
            refine ⟨V.sub_mem hu (V.smul_mem c hfV), ?_⟩
            change (u - c • f).coeff d = 0
            simp [c, coeff_sub, coeff_smul, div_mul_cancel₀ _ hfc]
          have hsub : W ≤ Submodule.span K (Set.range (Fin.cons f g)) := by
            rw [← hgspan]
            apply Submodule.span_mono
            rw [Fin.range_cons]
            exact Set.subset_insert f _
          have hfj : f ∈ Submodule.span K (Set.range (Fin.cons f g)) :=
            Submodule.subset_span ⟨0, by simp⟩
          have hh := (Submodule.span K (Set.range (Fin.cons f g))).add_mem
            (hsub hr) ((Submodule.span K (Set.range (Fin.cons f g))).smul_mem c hfj)
          simpa only [sub_add_cancel] using hh
      · have he : (fun i => ((Fin.cons f g : Fin (h + 1) → K[X]) i).natDegree) =
            Fin.cons f.natDegree (fun i => (g i).natDegree) := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        rw [he]
        apply Fin.cons_injective_of_injective ?_ hgdeg
        rintro ⟨j, hj⟩
        change (g j).natDegree = f.natDegree at hj
        have hh := hW (g j) (hgmem j) (hgLI.ne_zero j)
        rw [hfd] at hj
        omega


/-- Fixed-length coefficient reversal is linear, unlike degree-dependent
polynomial reversal. -/
def reflectLinearEquiv (K : Type*) [Field K] (N : ℕ) : K[X] ≃ₗ[K] K[X] where
  toFun := reflect N
  invFun := reflect N
  left_inv := fun _ => reflect_reflect
  right_inv := fun _ => reflect_reflect
  map_add' := fun f g => reflect_add f g N
  map_smul' := by
    intro c f
    simpa only [smul_eq_C_mul, RingHom.id_apply] using reflect_C_mul f c N

lemma order_reflect {K : Type*} [Field K] (N : ℕ) (f : K[X])
    (hf : f ≠ 0) (hd : f.natDegree ≤ N) :
    (reflect N f).natTrailingDegree = N - f.natDegree := by
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_reflect, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hf
  · apply le_natTrailingDegree (reflect_eq_zero_iff.not.mpr hf)
    intro j hj
    rw [coeff_reflect, revAt_le (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

lemma exists_order_echelon_family {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X])
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    ∃ (h : ℕ) (f : Fin h → K[X]), LinearIndependent K f ∧
      Submodule.span K (Set.range f) = V ∧
      Function.Injective (fun i => (f i).natTrailingDegree) := by
  classical
  let e := reflectLinearEquiv K (d - 1)
  let W := V.map e.toLinearMap
  have hW : ∀ g ∈ W, g ≠ 0 → g.natDegree < d := by
    rintro g ⟨f, hfV, rfl⟩ hfn
    have hf : f ≠ 0 := by intro hz; simp [hz] at hfn
    have hd := hV f hfV hf
    have he := natDegree_reflect_le (N := d - 1) (p := f)
    change (reflect (d - 1) f).natDegree < d
    omega
  obtain ⟨h, g, hgLI, hgspan, hgdeg⟩ := exists_degree_echelon_family d W hW
  have hgW : ∀ i, g i ∈ W := by
    intro i
    rw [← hgspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨h, fun i => e.symm (g i), hgLI.map' e.symm.toLinearMap (by simp), ?_, ?_⟩
  · have hs : Submodule.span K (Set.range (fun i => e.symm (g i))) =
        (Submodule.span K (Set.range g)).map e.symm.toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      exact Set.range_comp _ _
    rw [hs, hgspan, ← Submodule.map_comp]
    change (V.map (e.symm.toLinearMap.comp e.toLinearMap)) = V
    simp
  · intro i j hij
    change (reflect (d - 1) (g i)).natTrailingDegree =
      (reflect (d - 1) (g j)).natTrailingDegree at hij
    have hi := hW (g i) (hgW i) (hgLI.ne_zero i)
    have hj := hW (g j) (hgW j) (hgLI.ne_zero j)
    rw [order_reflect _ _ (hgLI.ne_zero i) (by omega),
      order_reflect _ _ (hgLI.ne_zero j) (by omega)] at hij
    apply hgdeg
    change (g i).natDegree = (g j).natDegree
    omega


lemma wronskian_linearCombination {K : Type*} [CommRing K] {h : ℕ}
    (f : Fin h → K[X]) (A : Matrix (Fin h) (Fin h) K) :
    wronskian (fun j => ∑ i, A i j • f i) = wronskian f * C A.det := by
  have he : (Matrix.of fun r j : Fin h =>
        derivative^[r.val] (∑ i, A i j • f i)) =
      (Matrix.of fun r i : Fin h => derivative^[r.val] (f i)) * A.map C := by
    apply Matrix.ext
    intro r j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
    calc
      derivative^[r.val] (∑ i, A i j • f i) =
          ∑ i, derivative^[r.val] (A i j • f i) := by
            simp only [← Module.End.pow_apply, map_sum]
      _ = _ := by
        simp only [iterate_derivative_smul]
        simp only [smul_eq_C_mul, mul_comm]
  unfold wronskian
  rw [he, Matrix.det_mul]
  congr 1
  exact (C.map_det A).symm

lemma basis_toMatrix_det_ne_zero {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {h : ℕ} (b b' : Basis (Fin h) K M) :
    (b.toMatrix b').det ≠ 0 := by
  have hh := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip b')
  rw [Matrix.det_mul, Matrix.det_one] at hh
  exact left_ne_zero_of_mul_eq_one hh

lemma wronskian_basis_change {K : Type*} [Field K] {h : ℕ}
    {V : Submodule K K[X]} (b b' : Basis (Fin h) K V) :
    wronskian (fun j => (b' j : K[X])) =
      wronskian (fun j => (b j : K[X])) * C (b.toMatrix b').det := by
  have he : (fun j => (b' j : K[X])) =
      (fun j => ∑ i, b.toMatrix b' i j • (b i : K[X])) := by
    funext j
    have hh := congrArg (fun v : V => (v : K[X])) (b.sum_repr (b' j))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Basis.toMatrix_apply] using hh.symm
  rw [he, wronskian_linearCombination]

lemma exists_order_echelon_basis {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X]) {h : ℕ} (b : Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    ∃ b' : Basis (Fin h) K V,
      Function.Injective (fun j => (b' j : K[X]).natTrailingDegree) := by
  obtain ⟨k, f, hLI, hspan, hord⟩ := exists_order_echelon_family d V hV
  let b' : Basis (Fin k) K V := (Basis.span hLI).map (LinearEquiv.ofEq _ _ hspan)
  have hb' : ∀ j, (b' j : K[X]) = f j := by
    intro j
    simp only [b', Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  have hk : k = h := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Module.finrank_eq_card_basis b'
    simp only [Fintype.card_fin] at h1 h2
    omega
  subst k
  exact ⟨b', by simpa only [hb'] using hord⟩

lemma wronskian_basis_ne_zero {K : Type*} [Field K] [CharZero K]
    (d : ℕ) {V : Submodule K K[X]} {h : ℕ} (b : Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    wronskian (fun j => (b j : K[X])) ≠ 0 := by
  obtain ⟨b', hord⟩ := exists_order_echelon_basis d V b hV
  have hne : ∀ j, (b' j : K[X]) ≠ 0 := by
    intro j hz
    exact b'.ne_zero j (Subtype.ext hz)
  have hn := (wronskian_order_of_distinct_orders _ hne hord).1
  rw [wronskian_basis_change b b'] at hn
  exact (mul_ne_zero_iff.mp hn).1

lemma derivative_taylor {K : Type*} [CommRing K] (a : K) (f : K[X]) :
    derivative (taylor a f) = taylor a (derivative f) := by
  simp only [taylor_apply, derivative_comp, derivative_add, derivative_X,
    derivative_C, add_zero, one_mul]

lemma iterate_derivative_taylor {K : Type*} [CommRing K] (a : K)
    (f : K[X]) (r : ℕ) :
    derivative^[r] (taylor a f) = taylor a (derivative^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, derivative_taylor, Function.iterate_succ_apply']

lemma wronskian_taylor {K : Type*} [CommRing K] {h : ℕ}
    (a : K) (f : Fin h → K[X]) :
    wronskian (fun j => taylor a (f j)) = taylor a (wronskian f) := by
  unfold wronskian
  have he : (Matrix.of fun i j : Fin h => derivative^[i.val] (taylor a (f j))) =
      (Matrix.of fun i j : Fin h => derivative^[i.val] (f j)).map (taylorEquiv a) := by
    apply Matrix.ext
    intro i j
    exact iterate_derivative_taylor a (f j) i.val
  rw [he]
  exact ((taylorEquiv a).toRingHom.map_det _).symm

lemma natDegree_wronskian_le {K : Type*} [CommRing K] {h : ℕ}
    (f : Fin h → K[X]) (D : ℕ) (hd : ∀ j, (f j).natDegree ≤ D) :
    (wronskian f).natDegree ≤ h * D := by
  unfold wronskian
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro g _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    ∑ j : Fin h, (derivative^[(g j).val] (f j)).natDegree
        ≤ ∑ _j : Fin h, D := Finset.sum_le_sum fun j _ =>
          (natDegree_iterate_derivative _ _).trans ((Nat.sub_le _ _).trans (hd j))
    _ = h * D := by simp

lemma sum_rootMultiplicity_le_natDegree {K : Type*} [Field K]
    (f : K[X]) (s : Finset K) :
    ∑ a ∈ s, f.rootMultiplicity a ≤ f.natDegree := by
  classical
  simp only [← count_roots]
  calc
    ∑ a ∈ s, f.roots.count a ≤ ∑ a ∈ s ∪ f.roots.toFinset, f.roots.count a :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = f.roots.card := Multiset.sum_count_eq_card (fun a ha =>
      Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ f.natDegree := card_roots' f


lemma wronskian_order_at {K : Type*} [Field K] [CharZero K] {h : ℕ}
    (a : K) (f : Fin h → K[X]) (hf : ∀ j, f j ≠ 0)
    (hd : Function.Injective (fun j => (f j).rootMultiplicity a)) :
    (wronskian f).rootMultiplicity a + (∑ i : Fin h, i.val) =
      ∑ j, (f j).rootMultiplicity a := by
  have hn : ∀ j, taylor a (f j) ≠ 0 := by
    intro j hz
    exact hf j ((taylorEquiv a).injective (by simpa using hz))
  have ho : Function.Injective (fun j => (taylor a (f j)).natTrailingDegree) := by
    simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using hd
  have hh := (wronskian_order_of_distinct_orders _ hn ho).2
  rw [wronskian_taylor] at hh
  simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using hh

lemma wronskian_basis_rootMultiplicity {K : Type*} [Field K] [CharZero K]
    (d : ℕ) {V : Submodule K K[X]} {h : ℕ}
    (b b' : Basis (Fin h) K V) (a : K)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) :
    (wronskian (fun j => (b' j : K[X]))).rootMultiplicity a =
      (wronskian (fun j => (b j : K[X]))).rootMultiplicity a := by
  rw [wronskian_basis_change b b', rootMultiplicity_mul
    (mul_ne_zero (wronskian_basis_ne_zero d b hV)
      (C_ne_zero.mpr (basis_toMatrix_det_ne_zero b b'))), rootMultiplicity_C, add_zero]

/-- The Wronskian order bound for distinct points of a characteristic-zero
field and order-echelon bases. The triangular sum is exactly binom(h,2). -/

theorem wronskian_order_bound {K : Type*} [Field K] [CharZero K]
    (d : ℕ) {V : Submodule K K[X]} {h w : ℕ}
    (b : Basis (Fin h) K V) (a : Fin w → K) (ha : Function.Injective a)
    (e : Fin w → Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d)
    (he : ∀ i, Function.Injective (fun j => (e i j : K[X]).rootMultiplicity (a i))) :
    ∑ i, ∑ j, (e i j : K[X]).rootMultiplicity (a i) ≤
      h * (d - 1) + w * (∑ j : Fin h, j.val) := by
  classical
  have localOrder : ∀ i, ∑ j, (e i j : K[X]).rootMultiplicity (a i) =
      (wronskian (fun j => (b j : K[X]))).rootMultiplicity (a i) +
        (∑ j : Fin h, j.val) := by
    intro i
    rw [← wronskian_order_at (a i) _ (fun j hz => (e i).ne_zero j (Subtype.ext hz)) (he i),
      wronskian_basis_rootMultiplicity d b (e i) (a i) hV]
  simp_rw [localOrder]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  apply Nat.add_le_add_right
  let W := wronskian (fun j => (b j : K[X]))
  have hsum : (∑ i, W.rootMultiplicity (a i)) =
      ∑ x ∈ Finset.univ.image a, W.rootMultiplicity x := by
    rw [Finset.sum_image]
    exact fun i _ j _ hij => ha hij
  rw [hsum]
  apply (sum_rootMultiplicity_le_natDegree W _).trans
  apply natDegree_wronskian_le
  intro j
  have hh := hV (b j) (b j).property (fun hz => b.ne_zero j (Subtype.ext hz))
  omega


lemma exists_echelon_basis_at {K : Type*} [Field K]
    (d : ℕ) (V : Submodule K K[X]) {h : ℕ} (b : Basis (Fin h) K V)
    (hV : ∀ f ∈ V, f ≠ 0 → f.natDegree < d) (a : K) :
    ∃ b' : Basis (Fin h) K V,
      Function.Injective (fun j => (b' j : K[X]).rootMultiplicity a) := by
  let e := (taylorEquiv a).toLinearEquiv
  let W := V.map e.toLinearMap
  let eV : V ≃ₗ[K] W := e.submoduleMap V
  have hW : ∀ f ∈ W, f ≠ 0 → f.natDegree < d := by
    rintro g ⟨f, hfV, rfl⟩ hne
    have hf : f ≠ 0 := by intro hz; simp [hz] at hne
    change (taylor a f).natDegree < d
    rw [natDegree_taylor]
    exact hV f hfV hf
  obtain ⟨c, hc⟩ := exists_order_echelon_basis d W (b.map eV) hW
  refine ⟨c.map eV.symm, ?_⟩
  have ht : ∀ j, taylor a ((c.map eV.symm) j : K[X]) = (c j : K[X]) := by
    intro j
    rw [Basis.map_apply]
    change e (e.symm (c j : K[X])) = (c j : K[X])
    exact e.apply_symm_apply _
  intro i j hij
  apply hc
  simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply, ht] using hij

/-- Distinct leading orders make vanishing conditions triangular; no linear
combination can cancel its first nonzero echelon term. -/
lemma low_coefficients_force_zero {K : Type*} [Field K] {h : ℕ}
    (f : Fin h → K[X]) (hf : ∀ j, f j ≠ 0)
    (hd : Function.Injective (fun j => (f j).natTrailingDegree))
    (c : Fin h → K) (r : ℕ)
    (hz : ∀ m < r, (∑ j, c j • f j).coeff m = 0) :
    ∀ j, (f j).natTrailingDegree < r → c j = 0 := by
  classical
  have hi : ∀ m, ∀ j, (f j).natTrailingDegree = m → m < r → c j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hj hmr
      have hs : (∑ k, c k • f k).coeff m = c j * (f j).coeff m := by
        simp only [finsetSum_coeff, coeff_smul, smul_eq_mul]
        apply Finset.sum_eq_single j
        · intro k _ hkj
          by_cases hk : (f k).natTrailingDegree < m
          · rw [ih _ hk k rfl (hk.trans hmr), zero_mul]
          · rw [coeff_eq_zero_of_lt_natTrailingDegree (show m < (f k).natTrailingDegree by
              have hn : (f k).natTrailingDegree ≠ m := by
                intro hh
                exact hkj (hd (hh.trans hj.symm))
              omega), mul_zero]
        · intro hh
          exact (hh (Finset.mem_univ j)).elim
      have htc : (f j).coeff m ≠ 0 := by
        rw [← hj]
        change (f j).trailingCoeff ≠ 0
        exact mt trailingCoeff_eq_zero.mp (hf j)
      exact (mul_eq_zero.mp ((hs.symm.trans (hz m hmr)))).resolve_right htc
  intro j hj
  exact hi _ j rfl hj


/-- The exact vanishing filtration, expressed by low Taylor coefficients. -/
def vanishingFiltration {K : Type*} [Field K] (V : Submodule K K[X])
    (a : K) (r : ℕ) : Submodule K K[X] where
  carrier := {f | f ∈ V ∧ ∀ m < r, (taylor a f).coeff m = 0}
  zero_mem' := ⟨V.zero_mem, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    refine ⟨V.add_mem hf hg, ?_⟩
    intro m hm
    simp [hf0 m hm, hg0 m hm]
  smul_mem' := by
    rintro c f ⟨hf, hf0⟩
    refine ⟨V.smul_mem c hf, ?_⟩
    intro m hm
    simp [hf0 m hm]

lemma mem_vanishingFiltration_iff_dvd {K : Type*} [Field K]
    (V : Submodule K K[X]) (a : K) (r : ℕ) (f : K[X]) :
    f ∈ vanishingFiltration V a r ↔ f ∈ V ∧ (X - C a)^r ∣ f := by
  change (f ∈ V ∧ ∀ m < r, (taylor a f).coeff m = 0) ↔ _
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  rfl

lemma vanishingFiltration_eq_span {K : Type*} [Field K]
    {V : Submodule K K[X]} {h : ℕ} (b : Basis (Fin h) K V)
    (a : K) (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (r : ℕ) :
    vanishingFiltration V a r = Submodule.span K
      (Set.range (fun j : {j : Fin h // r ≤ (b j : K[X]).rootMultiplicity a} =>
        (b j.val : K[X]))) := by
  classical
  apply le_antisymm
  · intro f hf
    let c := b.repr ⟨f, hf.1⟩
    have hs : ∑ j, c j • (b j : K[X]) = f := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg (fun x : V => (x : K[X])) (b.sum_repr ⟨f, hf.1⟩)
    have hne : ∀ j, taylor a (b j : K[X]) ≠ 0 := by
      intro j hz
      exact b.ne_zero j (Subtype.ext ((taylorEquiv a).injective (by simpa using hz)))
    have hinj : Function.Injective (fun j => (taylor a (b j : K[X])).natTrailingDegree) := by
      simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using hb
    have hz : ∀ m < r, (∑ j, c j • taylor a (b j : K[X])).coeff m = 0 := by
      intro m hm
      have ht := congrArg (taylor a) hs
      simp only [map_sum, map_smul] at ht
      rw [ht]
      exact hf.2 m hm
    have hc := low_coefficients_force_zero (fun j => taylor a (b j : K[X]))
      hne hinj c r hz
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨fun j => c j.val, ?_⟩
    have hst := Finset.sum_subtype (F := inferInstance) (p := fun j => r ≤ (b j :
      K[X]).rootMultiplicity a)
      (Finset.univ.filter (fun j => r ≤ (b j : K[X]).rootMultiplicity a))
      (by simp) (fun j => c j • (b j : K[X]))
    rw [← hst]
    rw [Finset.sum_filter]
    calc
      ∑ j, (if r ≤ (b j : K[X]).rootMultiplicity a then c j • (b j : K[X]) else 0) =
          ∑ j, c j • (b j : K[X]) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with hj
        · rfl
        · have hj' : (taylor a (b j : K[X])).natTrailingDegree < r := by
            simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using
              (Nat.lt_of_not_ge hj)
          rw [hc j hj', zero_smul]
      _ = f := hs
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨(b j.val).property, ?_⟩
    intro m hm
    apply coeff_eq_zero_of_lt_natTrailingDegree
    apply hm.trans_le
    simpa only [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply] using j.property

/-- Row reduction exactly describes the whole vanishing filtration,
not only the basis vectors. -/
theorem finrank_vanishingFiltration {K : Type*} [Field K]
    {V : Submodule K K[X]} {h : ℕ} (b : Basis (Fin h) K V)
    (a : K) (hb : Function.Injective (fun j => (b j : K[X]).rootMultiplicity a))
    (r : ℕ) :
    finrank K (vanishingFiltration V a r) =
      Fintype.card {j : Fin h // r ≤ (b j : K[X]).rootMultiplicity a} := by
  rw [vanishingFiltration_eq_span b a hb]
  apply finrank_span_eq_card
  exact (b.linearIndependent.map' V.subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).comp _ Subtype.val_injective

end
end RationalHitting.Expansion


/- An integral frame records integral coordinate functionals, making
saturation explicit. -/

end Complexity
