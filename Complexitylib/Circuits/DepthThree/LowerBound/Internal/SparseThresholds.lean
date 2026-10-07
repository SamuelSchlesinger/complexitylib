/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.EntropyThreshold
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparsePrefix
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Unrestricted depth-three lower bound: sparse thresholds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseThresholds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

/-- The sunflower, occurrence, insertion, and accumulated thresholds at one level. -/
structure SparseLevel where
  /-- The required sunflower cardinality. -/
  r : ℕ
  /-- The literal-occurrence threshold. -/
  e : ℕ
  /-- The insertion bound at this level. -/
  D : ℕ
  /-- The sum of earlier insertion bounds. -/
  F : ℕ

/-- Choose the next sparsification thresholds using the entropy bound. -/
def nextSparseLevel (ε : ℝ) (hε : 0 < ε) (i : ℕ)
    (previous : SparseLevel) : SparseLevel :=
  let F := previous.F + previous.D
  let r := Classical.choose (exists_integer_entropy_threshold F hε)
  let e := i.factorial * (r - 1) ^ i
  ⟨r, e, (e + 1) * (2 + F), F⟩

/-- The recursively chosen sparsification thresholds at each clause size. -/
def sparseLevel (ε : ℝ) (hε : 0 < ε) : ℕ → SparseLevel
  | 0 => ⟨2, 0, 0, 0⟩
  | 1 => ⟨2, 1, 4, 0⟩
  | n + 2 => nextSparseLevel ε hε (n + 1) (sparseLevel ε hε (n + 1))

/-- The sunflower-size threshold at the given sparsification level. -/
def sparseR (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).r
/-- The literal-occurrence bound at the given sparsification level. -/
def sparseE (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).e
/-- The insertion bound at the given sparsification level. -/
def sparseD (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).D
/-- The sum of insertion bounds at earlier sparsification levels. -/
def sparseF (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).F

variable (ε : ℝ) (hε : 0 < ε)

@[simp] theorem sparseE_zero : sparseE ε hε 0 = 0 := rfl
@[simp] theorem sparseD_zero : sparseD ε hε 0 = 0 := rfl
@[simp] theorem sparseF_zero : sparseF ε hε 0 = 0 := rfl
@[simp] theorem sparseE_one : sparseE ε hε 1 = 1 := rfl
@[simp] theorem sparseD_one : sparseD ε hε 1 = 4 := rfl
@[simp] theorem sparseF_one : sparseF ε hε 1 = 0 := rfl

theorem sparseR_succ_succ (n : ℕ) :
    sparseR ε hε (n + 2) = Classical.choose
      (exists_integer_entropy_threshold (sparseF ε hε (n + 1) + sparseD ε hε (n + 1)) hε) :=
  rfl

theorem sparseF_succ_succ (n : ℕ) :
    sparseF ε hε (n + 2) = sparseF ε hε (n + 1) + sparseD ε hε (n + 1) := rfl

theorem sparseE_succ_succ (n : ℕ) :
    sparseE ε hε (n + 2) = (n + 1).factorial * (sparseR ε hε (n + 2) - 1) ^ (n + 1) :=
  rfl

theorem sparseD_succ_succ (n : ℕ) :
    sparseD ε hε (n + 2) =
      (sparseE ε hε (n + 2) + 1) * (2 + sparseF ε hε (n + 2)) := rfl

theorem sparseR_ge_two (i : ℕ) : 2 ≤ sparseR ε hε i := by
  cases i with
  | zero => exact le_rfl
  | succ i =>
      cases i with
      | zero => exact le_rfl
      | succ n =>
          rw [sparseR_succ_succ]
          exact (Classical.choose_spec
            (exists_integer_entropy_threshold
              (sparseF ε hε (n + 1) + sparseD ε hε (n + 1)) hε)).1

theorem sparseF_eq_sum_Ico (i : ℕ) :
    sparseF ε hε i = ∑ v ∈ Finset.Ico 1 i, sparseD ε hε v := by
  induction i with
  | zero => simp
  | succ i ih =>
      cases i with
      | zero => simp
      | succ n =>
          rw [sparseF_succ_succ, ih]
          exact (Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1) (sparseD ε hε)).symm

theorem sparseE_succ (i : ℕ) (hi : 1 ≤ i) :
    sparseE ε hε (i + 1) = i.factorial * (sparseR ε hε (i + 1) - 1) ^ i := by
  cases i with
  | zero => omega
  | succ n => exact sparseE_succ_succ ε hε n

theorem sparseD_eq (i : ℕ) (hi : 1 ≤ i) :
    sparseD ε hε i =
      (sparseE ε hε i + 1) * (2 + ∑ v ∈ Finset.Ico 1 i, sparseD ε hε v) := by
  cases i with
  | zero => omega
  | succ i =>
      cases i with
      | zero => simp
      | succ n => rw [sparseD_succ_succ, sparseF_eq_sum_Ico]

theorem sparseE_pos (i : ℕ) (hi : 1 ≤ i) : 0 < sparseE ε hε i := by
  cases i with
  | zero => omega
  | succ i =>
      cases i with
      | zero => simp
      | succ n =>
          rw [sparseE_succ_succ]
          have hr := sparseR_ge_two ε hε (n + 2)
          exact Nat.mul_pos (Nat.factorial_pos _) (pow_pos (by omega) _)

theorem sparseD_pos (i : ℕ) (hi : 1 ≤ i) : 0 < sparseD ε hε i := by
  rw [sparseD_eq ε hε i hi]
  exact Nat.mul_pos (by omega) (by omega)

theorem sparse_entropy_bound (i : ℕ) (hi : 2 ≤ i) :
    (sparseF ε hε i : ℝ) * binaryEntropy (1 / (sparseR ε hε i : ℝ)) ≤ ε := by
  cases i with
  | zero => omega
  | succ i =>
      cases i with
      | zero => omega
      | succ n =>
          rw [sparseF_succ_succ, sparseR_succ_succ]
          exact (Classical.choose_spec
            (exists_integer_entropy_threshold
              (sparseF ε hε (n + 1) + sparseD ε hε (n + 1)) hε)).2

theorem sparseNumerics (b : ℕ) :
    SparseNumerics (sparseR ε hε) (sparseE ε hε) (sparseD ε hε) b where
  r_ge_two i _ _ := sparseR_ge_two ε hε i
  e_one := sparseE_one ε hε
  e_succ i hi _ := sparseE_succ ε hε i hi
  D_eq i hi _ := sparseD_eq ε hε i hi

/-- The resulting bound on sparse literal occurrences. -/
def sparseM (b : ℕ) : ℕ := 2 + 2 * ∑ i ∈ Finset.Icc 1 b, sparseE ε hε i

theorem sparseM_eq (b : ℕ) :
    sparseM ε hε b = 2 + 2 * ∑ i ∈ Finset.Icc 1 b, sparseE ε hε i := rfl

theorem sparseM_pos (b : ℕ) : 0 < sparseM ε hε b := by
  unfold sparseM
  omega

theorem sparse_tolerance_pos {b : ℕ} {η : ℝ} (hb : 1 ≤ b) (hη : 0 < η) :
    0 < η / (b : ℝ) := by
  apply div_pos hη
  exact_mod_cast (show 0 < b by omega)

theorem exists_sparse_numerics (b : ℕ) (η : ℝ) (hb : 1 ≤ b) (hη : 0 < η) :
    ∃ (r e D F : ℕ → ℕ) (M : ℕ),
      SparseNumerics r e D b ∧
      (∀ i, 2 ≤ r i) ∧ F 0 = 0 ∧ F 1 = 0 ∧
      (∀ i, F i = ∑ v ∈ Finset.Ico 1 i, D v) ∧
      (∀ i, 2 ≤ i → i ≤ b →
        (F i : ℝ) * binaryEntropy (1 / (r i : ℝ)) ≤ η / (b : ℝ)) ∧
      M = 2 + 2 * ∑ i ∈ Finset.Icc 1 b, e i ∧ 0 < M := by
  let δ := η / (b : ℝ)
  have hδ : 0 < δ := sparse_tolerance_pos hb hη
  exact ⟨sparseR δ hδ, sparseE δ hδ, sparseD δ hδ, sparseF δ hδ,
    sparseM δ hδ b, sparseNumerics δ hδ b, sparseR_ge_two δ hδ,
    sparseF_zero δ hδ, sparseF_one δ hδ, sparseF_eq_sum_Ico δ hδ,
    fun i hi _ => sparse_entropy_bound δ hδ i hi, sparseM_eq δ hδ b,
    sparseM_pos δ hδ b⟩

end DepthThreeLowerBound

end

end Complexity
