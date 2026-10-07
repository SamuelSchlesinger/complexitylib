/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.EncodingBounds

/-!
# Rational hitting lists: determinant

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Determinant.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.DeterminantAlgorithm
open Matrix
open scoped BigOperators

@[simp] lemma vector_get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Fin.cast]

/-- A dense square integer matrix stored as a vector of row vectors. -/
abbrev Table (n : ℕ) := Vector (Vector ℤ n) n

/-- Read a dense integer table as a matrix. -/
def denote {n : ℕ} (A : Table n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (A.get i).get j

/-- Materialize every entry of an integer matrix into a dense table. -/
def tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Table n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[simp] lemma denote_tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    denote (tabulate A) = A := by
  ext i j
  simp [denote, tabulate]

/-- One division-free Bird determinant stage on stored tables. -/
def step {n : ℕ} (A F : Table n) : Table n :=
  tabulate (BirdDet.Spec.stepEntry (denote A) (denote F))

/-- Iterate the division-free determinant stage. -/
def stages {n : ℕ} (A : Table n) : ℕ → Table n
  | 0 => A
  | k+1 => step A (stages A k)

lemma stages_spec {n : ℕ} (A : Table n) (k : ℕ) :
    denote (stages A k) = (BirdDet.Spec.stepEntry (denote A))^[k] (denote A) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stages,step,denote_tabulate,Function.iterate_succ_apply',ih]

/-- Compute the determinant from the final Bird stage, including dimension zero. -/
def determinant : {n : ℕ} → Table n → ℤ
  | 0, _ => 1
  | k+1,A => (-1 : ℤ)^k * denote (stages A k) 0 0

/- Bridges between the matrix specification and the array determinant. -/

lemma sumFrom_eq_sum_Ico {n lo : ℕ} (f : ℕ → ℤ) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih =>
    rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot
      hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

lemma sumFrom_fin_tail {n : ℕ} (i : Fin n) (f : ℕ → ℤ) :
    BirdDet.sumFrom n (i.val+1) f = ∑ k ∈ Finset.Ioi i, f k.val := by
  rw [sumFrom_eq_sum_Ico]
  calc _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; simp; omega
       _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
       _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
       _ = _ := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

lemma iterate_array_spec {n : ℕ} (A : Array ℤ) (hA : A.size = n*n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [Function.iterate_succ_apply',BirdDet.stepEntry_eq,BirdDet.Spec.stepEntry_eq,
      sumFrom_fin_tail,ih,Matrix.of_apply,BirdDet.get_eq]

lemma array_spec {n : ℕ} (A : Array ℤ) (hA : A.size = n*n) :
    BirdDet.birdDet n A = BirdDet.Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero,BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp [BirdDet.birdDet_succ,BirdDet.Spec.birdDetSpec_succ,← iterate_array_spec A hA k]

lemma spec_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    BirdDet.Spec.birdDet A = A.det := by
  let a := Array.ofFn fun k : Fin (n*n) => A k.divNat k.modNat
  have ha : a.size = n*n := Array.size_ofFn
  have he : Matrix.ofArray a ha = A := Matrix.ofArray_ofFn A
  rw [← he,← array_spec a ha,← BirdDet.det_eq_birdDet a ha]

/-- A genuine executable determinant, not `Matrix.det`'s permutation sum. -/
theorem determinant_eq {n : ℕ} (A : Table n) : determinant A = (denote A).det := by
  rw [← spec_eq_det]
  cases n with
  | zero => simp only [determinant, BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp only [determinant,stages_spec,BirdDet.Spec.birdDetSpec_succ]

lemma step_bound {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (B C : ℕ)
    (hA : ∀ i j, |A i j| ≤ B) (hF : ∀ i j, |F i j| ≤ C) (i j : Fin n) :
    |BirdDet.Spec.stepEntry A F i j| ≤ (2*n*B*C : ℕ) := by
  have hc : (Finset.Ioi i).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hsum : |∑ k ∈ Finset.Ioi i, F k k| ≤ (n*C : ℕ) := by
    calc _ ≤ ∑ k ∈ Finset.Ioi i, |F k k| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _k ∈ Finset.Ioi i, (C : ℤ) := Finset.sum_le_sum (fun k _ => hF k k)
         _ ≤ (n*C : ℕ) := by
            simp only [Finset.sum_const,nsmul_eq_mul]
            exact_mod_cast Nat.mul_le_mul_right C hc
  have hprod : |∑ k ∈ Finset.Ioi i, F i k*A k j| ≤ (n*C*B : ℕ) := by
    calc _ ≤ ∑ k ∈ Finset.Ioi i, |F i k*A k j| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _k ∈ Finset.Ioi i, ((C : ℤ)*(B : ℤ)) := by
            apply Finset.sum_le_sum
            intro k _
            rw [abs_mul]
            exact mul_le_mul (hF i k) (hA k j) (abs_nonneg _) (by positivity)
         _ ≤ (n*C*B : ℕ) := by
            simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
            exact_mod_cast (Nat.mul_le_mul_right (C*B) hc).trans_eq (Nat.mul_assoc n C B).symm
  rw [BirdDet.Spec.stepEntry_eq]
  calc _ ≤ |(-(∑ k ∈ Finset.Ioi i, F k k))*A i j| + |∑ k ∈ Finset.Ioi i, F i k*A k j| :=
    abs_add_le _ _
       _ ≤ (n*C : ℕ)*(B : ℤ) + (n*C*B : ℕ) := by
          apply add_le_add _ hprod
          rw [abs_mul,abs_neg]
          exact mul_le_mul hsum (hA i j) (abs_nonneg _) (by positivity)
       _ = _ := by push_cast; ring

/-- Every stored table entry has only linearly many multiplicative growth stages. -/
theorem stages_bound {n : ℕ} (A : Table n) (B : ℕ)
    (hA : ∀ i j, |denote A i j| ≤ B) (k : ℕ) (i j : Fin n) :
    |denote (stages A k) i j| ≤ (B*(2*n*B)^k : ℕ) := by
  induction k generalizing i j with
  | zero => simpa [stages] using hA i j
  | succ k ih =>
    simp only [stages,step,denote_tabulate]
    convert step_bound (denote A) (denote (stages A k)) B (B*(2*n*B)^k) hA
      (fun u v => ih u v) i j using 1 ; push_cast ; ring

lemma self_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have : 0 < 2^n := by positivity
    omega

/-- Binary exponent bound for all stored intermediate tables, including singular inputs. -/
theorem stages_power_bound {n : ℕ} (A : Table n) (b : ℕ)
    (hA : ∀ i j, |denote A i j| ≤ (2 : ℤ)^b) (k : ℕ) (i j : Fin n) :
    |denote (stages A k) i j| ≤ (2 : ℤ)^(b+k*(1+n+b)) := by
  have hn := self_le_two_pow n
  have hf : 2*n*2^b ≤ 2^(1+n+b) := by
    calc _ ≤ 2*2^n*2^b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
         _ = _ := by rw [pow_add,pow_add]; norm_num
  calc _ ≤ ((2^b*(2*n*2^b)^k : ℕ) : ℤ) := stages_bound A (2^b) (by simpa using hA) k i j
       _ ≤ ((2^b*(2^(1+n+b))^k : ℕ) : ℤ) := by
         exact_mod_cast Nat.mul_le_mul_left (2^b)
           (Nat.pow_le_pow_left hf k)
       _ = (2 : ℤ)^(b+k*(1+n+b)) := by
          simp only [Nat.cast_pow,Nat.cast_ofNat,← pow_mul,← pow_add,Nat.mul_comm]

end RationalHitting.DeterminantAlgorithm

end Complexity
