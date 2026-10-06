/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Arithmetic.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Internal.Component
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor.Internal
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Ranks of the Jacobian and Hessian blocks of matrix multiplication

* **Block-triangular minors** (`sum_min_le_blockRank`). Let the rows `R g i` and columns
  `C g k` of a matrix be grouped by `g`, and order the groups by an injective key. If the
  entries from a group to a group of smaller key vanish and, within a group `g`, the entries
  are those of a totally regular matrix `T g`, then a block containing `P g` rows and `Q g`
  columns of each group has rank at least `∑ g, min (|P g|, |Q g|)`: choose
  `min (|P g|, |Q g|)` rows and columns of each group; the square submatrix is block
  triangular (`Matrix.BlockTriangular.det`) with nonsingular diagonal blocks.
* **The derivatives** (`jacobian_left`, `jacobian_right`, `sum_smul_hessian_left_right`, ...).
  The output `C i k` has derivative `[i = i'] B j k` in `A i' j` and `[k = k'] A i j` in
  `B j k'`; the Hessian of `∑ μ (C i k) C i k` pairs `A i j` with `B j k` through `μ (C i k)`
  and has no other nonzero entries.
* **The Jacobian blocks** (`jacobianRows_le_blockRank`, `jacobianCols_le_blockRank`). At a
  point `(A₀, B₀)` of totally regular matrices, group the outputs of a heavy row `i ∈ H` with
  the inputs `A i j` (entries `B₀ j k`), then the outputs of the light rows in a column `k`
  with the inputs `B j k` (entries `A₀ i j`). An output of a light row has derivative zero
  in the inputs `A i' j` of the other rows, so the groups are triangular.
* **The Hessian block** (`chargeJ_le_blockRank_hessian`). With `μ (C i k) = Λ i k`, the
  cross block of the Hessian is block diagonal over the inner index `j`, with blocks
  `Λ[rows of A, columns of B]` and `Λᵀ[rows of B, columns of A]`, so its rank is at least
  `R_J = chargeJ a b`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.ArithmeticInternal

open Matrix MatMul.Internal Tripartite

variable {n : Nat}

section Blocks

variable {L : Type*} [Field L]

theorem det_submatrix_ne_zero_of_totallyRegular {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Matrix (Fin n) (Fin n) L} (hT : TotallyRegular T) {ρ κ : ι → Fin n}
    (hρ : Function.Injective ρ) (hκ : Function.Injective κ) : (T.submatrix ρ κ).det ≠ 0 := by
  set e := Fintype.equivFin ι
  have h := hT (Fintype.card ι) (ρ ∘ e.symm) (κ ∘ e.symm) (hρ.comp e.symm.injective)
    (hκ.comp e.symm.injective)
  rwa [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self] at h

theorem sum_min_le_blockRank {G : Type*} [Fintype G] [DecidableEq G] (key : G → ℕ)
    (hkey : Function.Injective key) {m N : ℕ} (M : Matrix (Fin m) (Fin N) L)
    (Y : Finset (Fin m)) (X : Finset (Fin N)) (R : G → Fin n → Fin m) (C : G → Fin n → Fin N)
    (T : G → Matrix (Fin n) (Fin n) L) (hT : ∀ g, TotallyRegular (T g))
    (P Q : G → Finset (Fin n)) (hR : ∀ g, ∀ i ∈ P g, R g i ∈ Y)
    (hC : ∀ g, ∀ k ∈ Q g, C g k ∈ X)
    (hzero : ∀ g h, key h < key g → ∀ i ∈ P g, ∀ k ∈ Q h, M (R g i) (C h k) = 0)
    (hdiag : ∀ g, ∀ i ∈ P g, ∀ k ∈ Q g, M (R g i) (C g k) = T g i k) :
    ∑ g, min (P g).card (Q g).card ≤ blockRank M Y X := by
  classical
  let sz : G → ℕ := fun g => min (P g).card (Q g).card
  let pickP : (g : G) → Fin (sz g) → Fin n := fun g t =>
    (P g).orderEmbOfFin rfl (Fin.castLE (min_le_left _ _) t)
  let pickQ : (g : G) → Fin (sz g) → Fin n := fun g t =>
    (Q g).orderEmbOfFin rfl (Fin.castLE (min_le_right _ _) t)
  have memP : ∀ g t, pickP g t ∈ P g := fun g t => Finset.orderEmbOfFin_mem _ _ _
  have memQ : ∀ g t, pickQ g t ∈ Q g := fun g t => Finset.orderEmbOfFin_mem _ _ _
  have injP : ∀ g, Function.Injective (pickP g) := fun g =>
    ((P g).orderEmbOfFin rfl).injective.comp (Fin.castLE_injective _)
  have injQ : ∀ g, Function.Injective (pickQ g) := fun g =>
    ((Q g).orderEmbOfFin rfl).injective.comp (Fin.castLE_injective _)
  let r : (Σ g, Fin (sz g)) → ↥Y := fun x => ⟨R x.1 (pickP x.1 x.2), hR _ _ (memP _ _)⟩
  let c : (Σ g, Fin (sz g)) → ↥X := fun x => ⟨C x.1 (pickQ x.1 x.2), hC _ _ (memQ _ _)⟩
  set B := M.submatrix (fun i : ↥Y => (i : Fin m)) (fun j : ↥X => (j : Fin N)) with hB
  have hcard : Fintype.card (Σ g, Fin (sz g)) = ∑ g, sz g := by
    simp [Fintype.card_sigma]
  have hdet : (B.submatrix r c).det ≠ 0 := by
    have htri : (B.submatrix r c).BlockTriangular fun x => key x.1 := by
      intro x y hxy
      exact hzero x.1 y.1 hxy _ (memP _ _) _ (memQ _ _)
    rw [htri.det]
    refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
    by_cases hv : ∃ x : (Σ g, Fin (sz g)), key x.1 = v
    · obtain ⟨⟨g₀, t₀⟩, hx₀⟩ := hv
      have hg : ∀ x : {x : (Σ g, Fin (sz g)) // key x.1 = v}, x.1.1 = g₀ :=
        fun x => hkey (x.2.trans hx₀.symm)
      let ρ : {x : (Σ g, Fin (sz g)) // key x.1 = v} → Fin n := fun x => pickP x.1.1 x.1.2
      let κ : {x : (Σ g, Fin (sz g)) // key x.1 = v} → Fin n := fun x => pickQ x.1.1 x.1.2
      have hρ : Function.Injective ρ := by
        rintro ⟨⟨g, t⟩, hx⟩ ⟨⟨g', t'⟩, hx'⟩ h
        have e₁ : g = g₀ := hkey (hx.trans hx₀.symm)
        have e₂ : g' = g₀ := hkey (hx'.trans hx₀.symm)
        subst e₁ e₂
        have := injP _ h
        subst this
        rfl
      have hκ : Function.Injective κ := by
        rintro ⟨⟨g, t⟩, hx⟩ ⟨⟨g', t'⟩, hx'⟩ h
        have e₁ : g = g₀ := hkey (hx.trans hx₀.symm)
        have e₂ : g' = g₀ := hkey (hx'.trans hx₀.symm)
        subst e₁ e₂
        have := injQ _ h
        subst this
        rfl
      have hblock : (B.submatrix r c).toSquareBlock (fun x => key x.1) v =
          (T g₀).submatrix ρ κ := by
        ext x y
        rw [toSquareBlock_def, of_apply, submatrix_apply, submatrix_apply, hB, submatrix_apply]
        have hx := hg x
        have hy := hg y
        show M (R x.1.1 (ρ x)) (C y.1.1 (κ y)) = T g₀ (ρ x) (κ y)
        have mx : ρ x ∈ P x.1.1 := memP _ _
        have my : κ y ∈ Q y.1.1 := memQ _ _
        rw [hx] at mx ⊢
        rw [hy] at my ⊢
        exact hdiag g₀ _ mx _ my
      rw [hblock]
      exact det_submatrix_ne_zero_of_totallyRegular (hT g₀) hρ hκ
    · have : IsEmpty {x : (Σ g, Fin (sz g)) // key x.1 = v} := ⟨fun x => hv ⟨x.1, x.2⟩⟩
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
  have hrank := rank_of_det_ne_zero hdet
  rw [hcard] at hrank
  rw [blockRank, ← hB, ← hrank]
  exact rank_submatrix_le _ _ _

end Blocks

section Derivatives

open MvPolynomial

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]

theorem matMulRight_ne_matMulLeft (j k i j' : Fin n) : matMulRight n j k ≠ matMulLeft n i j' :=
  (matMulLeft_ne_matMulRight _ _ _ _).symm

theorem matMulPolynomial_output (i k : Fin n) :
    matMulPolynomial K n (matMulOutput n i k) =
      ∑ j, X (matMulLeft n i j) * X (matMulRight n j k) :=
  matMul_output _ i k

theorem jacobian_left (a : Fin (n * n + n * n) → L) (i k i' j : Fin n) :
    Taylor.jacobian (matMulPolynomial K n) a (matMulOutput n i k) (matMulLeft n i' j) =
      if i = i' then a (matMulRight n j k) else 0 := by
  classical
  simp only [Taylor.jacobian, of_apply, matMulPolynomial_output, map_sum, Derivation.leibniz,
    pderiv_X, Pi.single_apply, matMulLeft_inj, (matMulLeft_ne_matMulRight _ _ _ _).symm,
    ite_false, smul_eq_mul]
  by_cases h : i = i' <;> simp [h, apply_ite (aeval a)]

theorem jacobian_right (a : Fin (n * n + n * n) → L) (i k j k' : Fin n) :
    Taylor.jacobian (matMulPolynomial K n) a (matMulOutput n i k) (matMulRight n j k') =
      if k = k' then a (matMulLeft n i j) else 0 := by
  classical
  simp only [Taylor.jacobian, of_apply, matMulPolynomial_output, map_sum, Derivation.leibniz,
    pderiv_X, Pi.single_apply, matMulRight_inj, matMulLeft_ne_matMulRight, ite_false,
    smul_eq_mul]
  by_cases h : k = k' <;> simp [h, apply_ite (aeval a)]

theorem sum_smul_hessian_apply (μ : Fin (n * n) → L) (a : Fin (n * n + n * n) → L)
    (x y : Fin (n * n + n * n)) :
    (∑ o, μ o • Taylor.hessian (matMulPolynomial K n o) a) x y =
      ∑ i, ∑ k, μ (matMulOutput n i k) * ∑ j,
        ((if y = matMulLeft n i j ∧ x = matMulRight n j k then 1 else 0) +
          (if y = matMulRight n j k ∧ x = matMulLeft n i j then 1 else 0)) := by
  rw [Matrix.sum_apply, sum_output]
  simp only [Matrix.smul_apply, smul_eq_mul, Taylor.hessian, of_apply, matMulPolynomial_output,
    map_sum, Taylor.Internal.aeval_pderiv_pderiv_X_mul_X]

theorem sum_smul_hessian_left_right (μ : Fin (n * n) → L) (a : Fin (n * n + n * n) → L)
    (i j j' k : Fin n) :
    (∑ o, μ o • Taylor.hessian (matMulPolynomial K n o) a) (matMulLeft n i j)
        (matMulRight n j' k) = if j = j' then μ (matMulOutput n i k) else 0 := by
  classical
  rw [sum_smul_hessian_apply]
  simp only [matMulRight_inj, matMulLeft_inj, (matMulLeft_ne_matMulRight _ _ _ _).symm,
    false_and, ite_false, zero_add]
  rw [Finset.sum_eq_single i (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [Ne.symm hx])
    (by simp), Finset.sum_eq_single k (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
  by_cases h : j = j'
  · subst h
    simp
  · simp only [h, ite_false]
    exact mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ =>
      ite_eq_right_iff.mpr fun hc => absurd (hc.2.2.trans hc.1.1.symm) h)

theorem sum_smul_hessian_right_left (μ : Fin (n * n) → L) (a : Fin (n * n + n * n) → L)
    (i j j' k : Fin n) :
    (∑ o, μ o • Taylor.hessian (matMulPolynomial K n o) a) (matMulRight n j k)
        (matMulLeft n i j') = if j = j' then μ (matMulOutput n i k) else 0 := by
  classical
  rw [sum_smul_hessian_apply]
  simp only [matMulRight_inj, matMulLeft_inj, (matMulLeft_ne_matMulRight _ _ _ _).symm,
    matMulLeft_ne_matMulRight, and_false, ite_false, add_zero]
  rw [Finset.sum_eq_single i (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [Ne.symm hx])
    (by simp), Finset.sum_eq_single k (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
  by_cases h : j = j'
  · subst h
    simp
  · simp only [h, ite_false]
    exact mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ =>
      ite_eq_right_iff.mpr fun hc => absurd (hc.2.1.trans hc.1.2.symm) h)

theorem sum_smul_hessian_left_left (μ : Fin (n * n) → L) (a : Fin (n * n + n * n) → L)
    (i j i' j' : Fin n) :
    (∑ o, μ o • Taylor.hessian (matMulPolynomial K n o) a) (matMulLeft n i j)
        (matMulLeft n i' j') = 0 := by
  rw [sum_smul_hessian_apply]
  simp [matMulLeft_ne_matMulRight]

theorem sum_smul_hessian_right_right (μ : Fin (n * n) → L) (a : Fin (n * n + n * n) → L)
    (j k j' k' : Fin n) :
    (∑ o, μ o • Taylor.hessian (matMulPolynomial K n o) a) (matMulRight n j k)
        (matMulRight n j' k') = 0 := by
  rw [sum_smul_hessian_apply]
  simp [matMulRight_ne_matMulLeft]

end Derivatives

section Ranks

variable {K L : Type*} [CommRing K] [Field L] [Algebra K L]

/-- **The row blocks of the Jacobian.** At a point `(A₀, B₀)` of totally regular matrices,
the block of the Jacobian with rows `Y` and columns `X` has rank at least
`jacobianRows cY aX bX H`. -/
theorem jacobianRows_le_blockRank {A₀ B₀ : Matrix (Fin n) (Fin n) L} (hA : TotallyRegular A₀)
    (hB : TotallyRegular B₀) (Y : Finset (Fin (n * n))) (X : Finset (Fin (n * n + n * n)))
    (cY aX bX : Finset (Fin n × Fin n)) (H : Finset (Fin n))
    (hc : ∀ q ∈ cY, matMulOutput n q.1 q.2 ∈ Y) (ha : ∀ q ∈ aX, matMulLeft n q.1 q.2 ∈ X)
    (hb : ∀ q ∈ bX, matMulRight n q.1 q.2 ∈ X) :
    jacobianRows cY aX bX H ≤
      blockRank (Taylor.jacobian (matMulPolynomial K n) (matMulInput A₀ B₀)) Y X := by
  classical
  have h := sum_min_le_blockRank (G := Fin n ⊕ Fin n)
    (Sum.elim (fun i => (i : ℕ)) fun k => n + k)
    (by
      rintro (i | k) (i' | k') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · exact congrArg _ (Fin.ext h)
      · have := i.isLt
        omega
      · have := i'.isLt
        omega
      · exact congrArg _ (Fin.ext (by omega)))
    (Taylor.jacobian (matMulPolynomial K n) (matMulInput A₀ B₀)) Y X
    (Sum.elim (fun i k => matMulOutput n i k) fun k i => matMulOutput n i k)
    (Sum.elim (fun i j => matMulLeft n i j) fun k j => matMulRight n j k)
    (Sum.elim (fun _ => B₀ᵀ) fun _ => A₀)
    (by rintro (_ | _); exacts [MatMul.Internal.totallyRegular_transpose hB, hA])
    (Sum.elim (fun i => if i ∈ H then rowSet cY i else ∅) fun k => colSet cY k \ H)
    (Sum.elim (fun i => if i ∈ H then rowSet aX i else ∅) fun k => colSet bX k)
    (by
      rintro (i | k) x hx
      · simp only [Sum.elim_inl] at hx ⊢
        split_ifs at hx
        · exact hc (i, x) (by simpa [rowSet] using hx)
        · simp at hx
      · simp only [Sum.elim_inr, Finset.mem_sdiff] at hx ⊢
        exact hc (x, k) (by simpa [colSet] using hx.1))
    (by
      rintro (i | k) x hx
      · simp only [Sum.elim_inl] at hx ⊢
        split_ifs at hx
        · exact ha (i, x) (by simpa [rowSet] using hx)
        · simp at hx
      · simp only [Sum.elim_inr] at hx ⊢
        exact hb (x, k) (by simpa [colSet] using hx))
    (by
      rintro (i | k) (i' | k') hlt x hx y hy <;>
        simp only [Sum.elim_inl, Sum.elim_inr] at hlt hx hy ⊢
      · rw [jacobian_left, ite_eq_right fun h => by rw [h] at hlt; omega]
      · have := i.isLt
        omega
      · split_ifs at hy with hi'
        · rw [jacobian_left, ite_eq_right fun h : x = i' =>
            (Finset.mem_sdiff.mp hx).2 (by rw [h]; exact hi')]
        · simp at hy
      · rw [jacobian_right, ite_eq_right fun h => by rw [h] at hlt; omega])
    (by
      rintro (i | k) x hx y hy <;> simp only [Sum.elim_inl, Sum.elim_inr]
      · rw [jacobian_left, ite_eq_left rfl, matMulInput_right, transpose_apply]
      · rw [jacobian_right, ite_eq_left rfl, matMulInput_left])
  rw [Fintype.sum_sum_type] at h
  refine le_of_eq_of_le ?_ h
  unfold jacobianRows
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl]
  split_ifs <;> simp

/-- **The column blocks of the Jacobian.** At a point `(A₀, B₀)` of totally regular matrices,
the block of the Jacobian with rows `Y` and columns `X` has rank at least
`jacobianCols cY aX bX H`. -/
theorem jacobianCols_le_blockRank {A₀ B₀ : Matrix (Fin n) (Fin n) L} (hA : TotallyRegular A₀)
    (hB : TotallyRegular B₀) (Y : Finset (Fin (n * n))) (X : Finset (Fin (n * n + n * n)))
    (cY aX bX : Finset (Fin n × Fin n)) (H : Finset (Fin n))
    (hc : ∀ q ∈ cY, matMulOutput n q.1 q.2 ∈ Y) (ha : ∀ q ∈ aX, matMulLeft n q.1 q.2 ∈ X)
    (hb : ∀ q ∈ bX, matMulRight n q.1 q.2 ∈ X) :
    jacobianCols cY aX bX H ≤
      blockRank (Taylor.jacobian (matMulPolynomial K n) (matMulInput A₀ B₀)) Y X := by
  classical
  have h := sum_min_le_blockRank (G := Fin n ⊕ Fin n)
    (Sum.elim (fun k => (k : ℕ)) fun i => n + i)
    (by
      rintro (k | i) (k' | i') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · exact congrArg _ (Fin.ext h)
      · have := k.isLt
        omega
      · have := k'.isLt
        omega
      · exact congrArg _ (Fin.ext (by omega)))
    (Taylor.jacobian (matMulPolynomial K n) (matMulInput A₀ B₀)) Y X
    (Sum.elim (fun k i => matMulOutput n i k) fun i k => matMulOutput n i k)
    (Sum.elim (fun k j => matMulRight n j k) fun i j => matMulLeft n i j)
    (Sum.elim (fun _ => A₀) fun _ => B₀ᵀ)
    (by rintro (_ | _); exacts [hA, MatMul.Internal.totallyRegular_transpose hB])
    (Sum.elim (fun k => if k ∈ H then colSet cY k else ∅) fun i => rowSet cY i \ H)
    (Sum.elim (fun k => if k ∈ H then colSet bX k else ∅) fun i => rowSet aX i)
    (by
      rintro (k | i) x hx
      · simp only [Sum.elim_inl] at hx ⊢
        split_ifs at hx
        · exact hc (x, k) (by simpa [colSet] using hx)
        · simp at hx
      · simp only [Sum.elim_inr, Finset.mem_sdiff] at hx ⊢
        exact hc (i, x) (by simpa [rowSet] using hx.1))
    (by
      rintro (k | i) x hx
      · simp only [Sum.elim_inl] at hx ⊢
        split_ifs at hx
        · exact hb (x, k) (by simpa [colSet] using hx)
        · simp at hx
      · simp only [Sum.elim_inr] at hx ⊢
        exact ha (i, x) (by simpa [rowSet] using hx))
    (by
      rintro (k | i) (k' | i') hlt x hx y hy <;>
        simp only [Sum.elim_inl, Sum.elim_inr] at hlt hx hy ⊢
      · rw [jacobian_right, ite_eq_right fun h => by rw [h] at hlt; omega]
      · have := k.isLt
        omega
      · split_ifs at hy with hk'
        · rw [jacobian_right, ite_eq_right fun h : x = k' =>
            (Finset.mem_sdiff.mp hx).2 (by rw [h]; exact hk')]
        · simp at hy
      · rw [jacobian_left, ite_eq_right fun h => by rw [h] at hlt; omega])
    (by
      rintro (k | i) x hx y hy <;> simp only [Sum.elim_inl, Sum.elim_inr]
      · rw [jacobian_right, ite_eq_left rfl, matMulInput_left]
      · rw [jacobian_left, ite_eq_left rfl, matMulInput_right, transpose_apply])
  rw [Fintype.sum_sum_type] at h
  refine le_of_eq_of_le ?_ h
  unfold jacobianCols
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Sum.elim_inl]
  split_ifs <;> simp

/-- **The cross block of the Hessian.** For a totally regular `Λ`, let `μ (C i k) = Λ i k`.
If `Y` holds exactly the inputs `A i j` with `(i, j) ∈ a` and `B j k` with `(j, k) ∈ b`, the
block of the Hessian of `∑ μ o C o` with rows `Y` and columns `Yᶜ` has rank at least
`chargeJ a b`. -/
theorem chargeJ_le_blockRank_hessian {Λ : Matrix (Fin n) (Fin n) L} (hΛ : TotallyRegular Λ)
    (a₀ : Fin (n * n + n * n) → L) (Y : Finset (Fin (n * n + n * n)))
    (a b : Finset (Fin n × Fin n)) (ha : ∀ i j, (i, j) ∈ a ↔ matMulLeft n i j ∈ Y)
    (hb : ∀ j k, (j, k) ∈ b ↔ matMulRight n j k ∈ Y) :
    chargeJ a b ≤ blockRank (∑ o, (fun o => Λ (finProdFinEquiv.symm o).1
      (finProdFinEquiv.symm o).2) o • Taylor.hessian (matMulPolynomial K n o) a₀) Y Yᶜ := by
  classical
  have h := sum_min_le_blockRank (G := Fin n × Bool)
    (fun g => 2 * (g.1 : ℕ) + g.2.toNat)
    (by
      rintro ⟨j, _ | _⟩ ⟨j', _ | _⟩ h <;> simp only [Bool.toNat_false, Bool.toNat_true] at h
      · exact Prod.ext (Fin.ext (by dsimp only; omega)) rfl
      · omega
      · omega
      · exact Prod.ext (Fin.ext (by dsimp only; omega)) rfl)
    (∑ o, (fun o => Λ (finProdFinEquiv.symm o).1
      (finProdFinEquiv.symm o).2) o • Taylor.hessian (matMulPolynomial K n o) a₀) Y Yᶜ
    (fun g x => if g.2 then matMulRight n g.1 x else matMulLeft n x g.1)
    (fun g x => if g.2 then matMulLeft n x g.1 else matMulRight n g.1 x)
    (fun g => if g.2 then Λᵀ else Λ)
    (by
      rintro ⟨j, _ | _⟩
      · exact hΛ
      · exact MatMul.Internal.totallyRegular_transpose hΛ)
    (fun g => if g.2 then rowSet b g.1 else colSet a g.1)
    (fun g => if g.2 then (colSet a g.1)ᶜ else (rowSet b g.1)ᶜ)
    (by
      rintro ⟨j, _ | _⟩ x hx <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hx ⊢
      · exact (ha x j).mp (by simpa [colSet] using hx)
      · exact (hb j x).mp (by simpa [rowSet] using hx))
    (by
      rintro ⟨j, _ | _⟩ x hx <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hx ⊢
      · rw [Finset.mem_compl, ← hb]
        simpa [rowSet] using hx
      · rw [Finset.mem_compl, ← ha]
        simpa [colSet] using hx)
    (by
      rintro ⟨j, _ | _⟩ ⟨j', _ | _⟩ hlt x _ y _ <;> dsimp only at hlt ⊢ <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Bool.toNat_false, Bool.toNat_true]
          at hlt ⊢
      · rw [sum_smul_hessian_left_right, ite_eq_right fun h => by rw [h] at hlt; omega]
      · exact sum_smul_hessian_left_left _ _ _ _ _ _
      · exact sum_smul_hessian_right_right _ _ _ _ _ _
      · rw [sum_smul_hessian_right_left, ite_eq_right fun h => by rw [h] at hlt; omega])
    (by
      rintro ⟨j, _ | _⟩ x _ y _ <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · rw [sum_smul_hessian_left_right, ite_eq_left rfl]
        simp [matMulOutput]
      · rw [sum_smul_hessian_right_left, ite_eq_left rfl]
        simp [matMulOutput])
  rw [Fintype.sum_prod_type] at h
  refine le_of_eq_of_le ?_ h
  rw [← MatMul.Internal.sum_min_eq_chargeJ]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  omega

end Ranks



end Algebraic.Cutwidth.MultiOutput.MatMul.ArithmeticInternal
