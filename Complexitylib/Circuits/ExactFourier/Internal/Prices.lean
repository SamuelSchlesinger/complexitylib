/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.Shears
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Exact Fourier circuits: prices

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Prices.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier

/-- Lifting an in-place word to disjoint targets adds no auxiliary coordinates. -/
theorem Shear.act_sumInl {ι κ : Type*} (s : Shear ι) (v : ι → ℂ) (y : κ → ℂ) :
    Shear.act (s.sumInl κ) (Sum.elim v y) = Sum.elim (s.act v) y := by
  classical
  funext a
  cases a <;> simp [Shear.act, Matrix.TransvectionStruct.sumInl]

theorem runShears_sumInl {ι κ : Type*} (W : List (Shear ι)) (v : ι → ℂ) (y : κ → ℂ) :
    runShears (W.map (fun s => s.sumInl κ)) (Sum.elim v y) =
      Sum.elim (runShears W v) y := by
  induction W generalizing v with
  | nil => rfl
  | cons s W ih =>
      simp only [List.map_cons, runShears_cons, Shear.act_sumInl, ih]

theorem Program.memorySweep_exists {n k : ℕ} (p : Program n k) (enabled : Bool) :
    ∃ W : List (Shear (Fin n ⊕ Fin k)), W.length ≤ 2 * k ∧
      ∀ (x : Fin n → ℂ) (z : Fin k → ℂ),
        runShears W (Sum.elim x z) =
          Sum.elim x (p.dirtyScratch (if enabled then x else 0) z) := by
  obtain ⟨W, hW, he⟩ := p.dirtySweep_exists enabled Sum.inl Sum.inr
    (fun _ _ h => Sum.inr.inj h) (by intros; simp)
  refine ⟨W, hW, ?_⟩
  intro x z
  funext r
  cases r with
  | inl i => simpa using (he (Sum.elim x z)).2 (Sum.inl i) (by intros; simp)
  | inr j =>
      have hi := (he (Sum.elim x z)).1 j
      convert hi using 1
      cases enabled <;> rfl

open Classical in
/-- The designated outputs are individual reads, not uncharged arbitrary linear maps. -/
theorem broadcast_subset_exists {ι κ : Type*} (S : Finset κ) (refs : κ → Option ι) :
    ∃ W : List (Shear (ι ⊕ κ)), W.length ≤ S.card ∧
      ∀ (v : ι → ℂ) (y : κ → ℂ),
        runShears W (Sum.elim v y) =
          Sum.elim v (fun j => y j + if j ∈ S then readCoord (refs j) v else 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨[], by simp, ?_⟩
      intros
      simp
  | @insert j S hj ih =>
      obtain ⟨W, hW, hWe⟩ := ih
      obtain ⟨V, hV, hVe⟩ := add_reference (Sum.inr j) ((refs j).map Sum.inl) 1
        (by intro r hr; cases h : refs j <;> simp [h] at hr
            subst r; simp)
      refine ⟨W ++ V, by simp only [List.length_append, Finset.card_insert_of_notMem hj]; omega,
        ?_⟩
      intro v y
      rw [runShears_append, hWe]
      funext r
      cases r with
      | inl i =>
          simpa using (hVe (Sum.elim v
            (fun k => y k + if k ∈ S then readCoord (refs k) v else 0))).2 (Sum.inl i)
              (by simp)
      | inr k =>
          by_cases hkj : k = j
          · subst k
            rw [(hVe _).1]
            cases h : refs j <;> simp [h, readCoord, hj]
          · rw [(hVe _).2 (Sum.inr k) (by simp [hkj])]
            simp [hkj]

theorem broadcast_exists {ι κ : Type*} [Fintype κ] (refs : κ → Option ι) :
    ∃ W : List (Shear (ι ⊕ κ)), W.length ≤ Fintype.card κ ∧
      ∀ (v : ι → ℂ) (y : κ → ℂ),
        runShears W (Sum.elim v y) = Sum.elim v (fun j => y j + readCoord (refs j) v) := by
  classical
  simpa using broadcast_subset_exists Finset.univ refs

/-- Inverting the output-read word subtracts exactly the same reads. -/
theorem broadcast_reverse {ι κ : Type*} (W : List (Shear (ι ⊕ κ)))
    (R : (ι → ℂ) → κ → ℂ)
    (hW : ∀ v y, runShears W (Sum.elim v y) = Sum.elim v (fun j => y j + R v j))
    (v : ι → ℂ) (y : κ → ℂ) :
    runShears (reverseShears W) (Sum.elim v y) =
      Sum.elim v (fun j => y j - R v j) := by
  have h := runShears_reverse W (Sum.elim v (fun j => y j - R v j))
  rw [hW] at h
  simpa using h

end ExactFourier

namespace ExactFourier

/-- Forward/read/reverse on arbitrary memory. This is a word identity, not an
assumption that dirty scratch starts at zero. -/
theorem replay_readout {ι κ : Type*} (W : List (Shear ι))
    (B : List (Shear (ι ⊕ κ))) (R : (ι → ℂ) → κ → ℂ)
    (hB : ∀ v y, runShears B (Sum.elim v y) = Sum.elim v (fun j => y j + R v j))
    (v : ι → ℂ) (y : κ → ℂ) :
    runShears ((W.map (fun s => s.sumInl κ)) ++ B ++
        reverseShears (W.map (fun s => s.sumInl κ))) (Sum.elim v y) =
      Sum.elim v (fun j => y j + R (runShears W v) j) := by
  simp only [runShears_append, runShears_sumInl, hB]
  have h := runShears_reverse (W.map (fun s => s.sumInl κ))
    (Sum.elim v (fun j => y j + R (runShears W v) j))
  rw [runShears_sumInl] at h
  exact h

theorem dirty_coordinate_replay_count {n a : ℕ} (C : LinearDAG n a) :
    ∃ W : List (Shear ((Fin n ⊕ Fin C.size) ⊕ Fin a)),
      W.length ≤ 8 * C.size + 2 * a ∧
      ∀ (x : Fin n → ℂ) (y : Fin a → ℂ) (z : Fin C.size → ℂ),
        runShears W (Sum.elim (Sum.elim x z) y) =
          Sum.elim (Sum.elim x z) (fun j => y j + C.eval x j) := by
  classical
  let mem := Fin n ⊕ Fin C.size
  let refs (enabled : Bool) : Fin a → Option mem := fun j =>
    referenceMap enabled Sum.inl Sum.inr (C.outputs j)
  let R (enabled : Bool) (v : mem → ℂ) (j : Fin a) := readCoord (refs enabled j) v
  obtain ⟨W, hW, hWe⟩ := C.program.memorySweep_exists true
  obtain ⟨V, hV, hVe⟩ := C.program.memorySweep_exists false
  obtain ⟨B, hB, hBe⟩ := broadcast_exists (refs true)
  obtain ⟨D, hD, hDe⟩ := broadcast_exists (refs false)
  let W' := W.map (fun s => s.sumInl (Fin a))
  let V' := V.map (fun s => s.sumInl (Fin a))
  let first := W' ++ B ++ reverseShears W'
  let second := V' ++ reverseShears D ++ reverseShears V'
  refine ⟨first ++ second, ?_, ?_⟩
  · simp only [first, second, W', V', List.length_append, List.length_map,
      reverseShears_length, Fintype.card_fin] at *
    omega
  · intro x y z
    have hR (enabled : Bool) (xs : Fin n → ℂ) (zs : Fin C.size → ℂ) (j : Fin a) :
        R enabled (Sum.elim xs zs) j =
          available (if enabled then xs else 0) zs (C.outputs j) := by
      have h := congrFun (read_referenceMap enabled
        (Sum.inl : Fin n → mem) Sum.inr (Sum.elim xs zs)) (C.outputs j)
      cases enabled <;> exact h
    have hFirst : runShears first (Sum.elim (Sum.elim x z) y) =
        Sum.elim (Sum.elim x z)
          (fun j => y j + C.program.dirtyEval x z (C.outputs j)) := by
      rw [show first = W.map (fun s => s.sumInl (Fin a)) ++ B ++
          reverseShears (W.map (fun s => s.sumInl (Fin a))) from rfl]
      rw [replay_readout W B (R true) hBe, hWe]
      simp only [↓reduceIte, hR]
      rw [← C.program.dirtyEval_available x z]
    have hDrev : ∀ v y, runShears (reverseShears D) (Sum.elim v y) =
        Sum.elim v (fun j => y j + -R false v j) := by
      intro v y
      simpa only [sub_eq_add_neg] using broadcast_reverse D (R false) hDe v y
    have hSecond (ys : Fin a → ℂ) :
        runShears second (Sum.elim (Sum.elim x z) ys) =
          Sum.elim (Sum.elim x z)
            (fun j => ys j - C.program.dirtyEval 0 z (C.outputs j)) := by
      rw [show second = V.map (fun s => s.sumInl (Fin a)) ++ reverseShears D ++
          reverseShears (V.map (fun s => s.sumInl (Fin a))) from rfl]
      rw [replay_readout V (reverseShears D) (fun v j => -R false v j) hDrev, hVe]
      simp only [Bool.false_eq_true, ↓reduceIte, hR, sub_eq_add_neg]
      rw [← C.program.dirtyEval_available 0 z]
    rw [runShears_append, hFirst, hSecond]
    congr 1
    funext j
    rw [C.program.dirtyEval_split x z]
    simp [LinearDAG.eval, add_sub_assoc]

end ExactFourier

namespace ExactFourier

/-- The operational shears above are the ordinary elementary matrices. -/
theorem Shear.act_eq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Shear ι) (v : ι → ℂ) : s.act v = s.toMatrix.mulVec v := by
  funext i
  by_cases h : i = s.i <;> simp [Shear.act, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, h]

/-- The matrix representing execution of a list of elementary shears in order. -/
noncomputable def shearMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : List (Shear ι)) : Matrix ι ι ℂ := (W.map Matrix.TransvectionStruct.toMatrix).reverse.prod

theorem runShears_eq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : List (Shear ι)) (v : ι → ℂ) : runShears W v = (shearMatrix W).mulVec v := by
  induction W generalizing v with
  | nil => simp [shearMatrix]
  | cons s W ih =>
      rw [runShears_cons, ih, Shear.act_eq_mulVec]
      simp [shearMatrix, Matrix.mulVec_mulVec]

theorem shearMatrix_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : List (Shear ι)) : IsUnit (shearMatrix W) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h := Matrix.TransvectionStruct.det_toMatrix_prod W.reverse
  rw [show (shearMatrix W).det = 1 by simpa [shearMatrix, List.map_reverse] using h]
  exact isUnit_one

/-- Jam the arbitrary dirty memory in an identity summand. The lower-left block
is the designated rectangular map extended by zero on dirty scratch. -/
def replayMatrix {n a k : ℕ} (G : Matrix (Fin a) (Fin n) ℂ) :
    Matrix ((Fin n ⊕ Fin k) ⊕ Fin a) ((Fin n ⊕ Fin k) ⊕ Fin a) ℂ :=
  Matrix.fromBlocks 1 0 (Matrix.fromCols G 0) 1

theorem replayMatrix_mulVec {n a k : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (x : Fin n → ℂ) (z : Fin k → ℂ) (y : Fin a → ℂ) :
    (replayMatrix G).mulVec (Sum.elim (Sum.elim x z) y) =
      Sum.elim (Sum.elim x z) (fun j => y j + G.mulVec x j) := by
  funext r
  cases r <;> simp [replayMatrix, Matrix.fromBlocks_mulVec, Matrix.fromCols_mulVec,
    Function.comp_def, add_comm]

/-- Matrix endpoint of the dirty replay, necessary for the price and boundary laws. -/
theorem dirty_coordinate_replay_matrix {n a : ℕ} (C : LinearDAG n a)
    (G : Matrix (Fin a) (Fin n) ℂ) (hG : ∀ x, C.eval x = G.mulVec x) :
    ∃ W : List (Shear ((Fin n ⊕ Fin C.size) ⊕ Fin a)),
      W.length ≤ 8 * C.size + 2 * a ∧ shearMatrix W = replayMatrix G := by
  obtain ⟨W, hW, hWe⟩ := dirty_coordinate_replay_count C
  refine ⟨W, hW, ?_⟩
  apply Matrix.mulVec_injective
  funext v
  have hv : v = Sum.elim (Sum.elim (fun i => v (.inl (.inl i)))
      (fun i => v (.inl (.inr i)))) (fun i => v (.inr i)) := by
    funext i
    rcases i with (i | i) | i <;> rfl
  rw [hv, ← runShears_eq_mulVec, hWe, replayMatrix_mulVec, hG]

end ExactFourier

namespace ExactFourier
open scoped Kronecker

/-- Literal permutation-times-invertible-diagonal form on a finite index type. -/
def MonomialMatrix {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∃ (σ : Equiv.Perm ι) (d : ι → ℂ),
    (∀ j, d j ≠ 0) ∧ ∀ i j, A i j = if i = σ j then d j else 0

/-- An abstract nonnegative matrix cost obeying the stated invariance and composition laws. -/
structure MatrixPrice where
  /-- The real-valued cost assigned to a finite square complex matrix. -/
  value : ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Matrix ι ι ℂ → ℝ
  nonneg : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → 0 ≤ value A
  zero_iff : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → (value A = 0 ↔ MonomialMatrix A)
  reindex : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ), IsUnit A →
      value (Matrix.reindex e e A) = value A
  monomial : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (A L R : Matrix ι ι ℂ), IsUnit A → MonomialMatrix L → MonomialMatrix R →
      value (L * A * R) = value A
  mul_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ), IsUnit A → IsUnit B → value (A * B) ≤ value A + value B
  tensor : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ), IsUnit A → IsUnit B →
      value (A ⊗ₖ B) = Fintype.card κ * value A + Fintype.card ι * value B
  directSum : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ), IsUnit A → IsUnit B →
      value (Matrix.fromBlocks A 0 0 B) = value A + value B
  inverse : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → value A⁻¹ = value A
  transpose : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    IsUnit A → value A.transpose = value A
  normalized : value (Matrix.transvection (1 : Fin 2) 0 (1 : ℂ)) = 1

namespace MonomialMatrix

theorem diagonal {ι : Type*} [DecidableEq ι] (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) :
    MonomialMatrix (Matrix.diagonal d) := by
  refine ⟨Equiv.refl ι, d, hd, ?_⟩
  intro i j
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.diagonal, h]

theorem one {ι : Type*} [DecidableEq ι] : MonomialMatrix (1 : Matrix ι ι ℂ) := by
  simpa using diagonal (fun _ : ι => (1 : ℂ)) (by simp)

end MonomialMatrix

namespace MatrixPrice

@[simp] theorem one (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι] :
    p.value (1 : Matrix ι ι ℂ) = 0 :=
  (p.zero_iff 1 isUnit_one).mpr MonomialMatrix.one

theorem identity_pad (p : MatrixPrice) {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (hA : IsUnit A) :
    p.value (Matrix.fromBlocks A 0 0 (1 : Matrix κ κ ℂ)) = p.value A := by
  rw [p.directSum A 1 hA isUnit_one, p.one, add_zero]

theorem transvection_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c : ℂ) : IsUnit (Matrix.transvection i j c) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_transvection_of_ne i j hij c]
  exact isUnit_one

/-- Diagonal conjugation varies the shear coefficient, including all complex values. -/
theorem shear_two (p : MatrixPrice) (c : ℂ) (hc : c ≠ 0) :
    p.value (Matrix.transvection (1 : Fin 2) 0 c) = 1 := by
  let d : Fin 2 → ℂ := ![1, c]
  let L := Matrix.diagonal d
  let R := Matrix.diagonal (fun i => (d i)⁻¹)
  have hd : ∀ i, d i ≠ 0 := by intro i; fin_cases i <;> simp [d, hc]
  have h : L * Matrix.transvection (1 : Fin 2) 0 (1 : ℂ) * R =
      Matrix.transvection (1 : Fin 2) 0 c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, R, d, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection,
        Matrix.single, hc]
  rw [← h, p.monomial _ L R (transvection_isUnit 1 0 (by decide) 1)
    (MonomialMatrix.diagonal d hd)
    (MonomialMatrix.diagonal _ (fun i => inv_ne_zero (hd i))), p.normalized]

/-- An ordered pair and its untouched complement, used for exact identity padding. -/
noncomputable def pairComplement {ι : Type*} (i j : ι) (hij : i ≠ j) :
    (Fin 2 ⊕ {t : ι // t ≠ i ∧ t ≠ j}) ≃ ι := by
  classical
  exact {
    toFun := Sum.elim ![j, i] Subtype.val
    invFun := fun t => if htj : t = j then Sum.inl 0 else
      if hti : t = i then Sum.inl 1 else Sum.inr ⟨t, hti, htj⟩
    left_inv := by
      intro t
      rcases t with a | ⟨t, hti, htj⟩
      · fin_cases a <;> simp [hij]
      · simp [hti, htj]
    right_inv := by
      intro t
      by_cases htj : t = j
      · subst t; simp
      · by_cases hti : t = i
        · subst t; simp [hij]
        · simp [hti, htj] }

@[simp] theorem pairComplement_left₀ {ι : Type*} (i j : ι) (hij : i ≠ j) :
    pairComplement i j hij (Sum.inl 0) = j := rfl

@[simp] theorem pairComplement_left₁ {ι : Type*} (i j : ι) (hij : i ≠ j) :
    pairComplement i j hij (Sum.inl 1) = i := rfl

@[simp] theorem pairComplement_right {ι : Type*} (i j : ι) (hij : i ≠ j)
    (t : {t : ι // t ≠ i ∧ t ≠ j}) : pairComplement i j hij (Sum.inr t) = t := rfl

/-- Every coordinate shear is a single two-coordinate shear, with literal identity padding. -/
theorem transvection_le_one (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c : ℂ) : p.value (Matrix.transvection i j c) ≤ 1 := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  let κ := {t : ι // t ≠ i ∧ t ≠ j}
  let t : Matrix.TransvectionStruct (Fin 2) ℂ := ⟨1, 0, by decide, c⟩
  let e := pairComplement i j hij
  have he : Matrix.reindex e e (Matrix.fromBlocks t.toMatrix 0 0 (1 : Matrix κ κ ℂ)) =
      Matrix.transvection i j c := by
    rw [← t.toMatrix_sumInl κ]
    exact ((t.sumInl κ).toMatrix_reindexEquiv e).symm
  have ht : IsUnit t.toMatrix := transvection_isUnit 1 0 (by decide) c
  have hpad : IsUnit (Matrix.fromBlocks t.toMatrix 0 0 (1 : Matrix κ κ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨ht, isUnit_one⟩
  rw [← he, p.reindex e _ hpad, p.identity_pad t.toMatrix ht]
  exact le_of_eq (p.shear_two c hc)

theorem transvection_list_isUnit {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι ℂ)) :
    IsUnit (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.TransvectionStruct.det_toMatrix_prod]
  exact isUnit_one

/-- Every literal shear in an implementing word is charged. -/
theorem transvection_list_le (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι ℂ)) :
    p.value (L.map Matrix.TransvectionStruct.toMatrix).prod ≤ L.length := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have ht := p.transvection_le_one t.i t.j t.hij t.c
      have hm := p.mul_le t.toMatrix (L.map Matrix.TransvectionStruct.toMatrix).prod
        (transvection_isUnit t.i t.j t.hij t.c) (transvection_list_isUnit L)
      calc
        _ ≤ p.value t.toMatrix + p.value (L.map Matrix.TransvectionStruct.toMatrix).prod := hm
        _ ≤ 1 + (L.length : ℝ) := add_le_add ht ih
        _ = (L.length : ℝ) + 1 := add_comm _ _

/-- Inverse symmetry and subadditivity control a relative transformation in both directions. -/
theorem difference_le (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    |p.value B - p.value A| ≤ p.value (A⁻¹ * B) := by
  have hAi : IsUnit A⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr hA
  have hBi : IsUnit B⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr hB
  have hAB : A * (A⁻¹ * B) = B := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      one_mul]
  have hu : IsUnit (A⁻¹ * B) := hAi.mul hB
  have hb := p.mul_le A (A⁻¹ * B) hA hu
  rw [hAB] at hb
  have ha := p.mul_le B (A⁻¹ * B)⁻¹ hB ((Matrix.isUnit_nonsing_inv_iff).mpr hu)
  have hBA : B * (A⁻¹ * B)⁻¹ = A := by
    nth_rw 1 [← hAB]
    rw [Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), mul_one]
  rw [hBA, p.inverse _ hu] at ha
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end MatrixPrice
end ExactFourier

end

end Complexity
