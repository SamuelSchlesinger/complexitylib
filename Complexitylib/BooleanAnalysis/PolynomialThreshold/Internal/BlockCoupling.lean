/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.BinomialMoments
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.FiniteCoupling
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.ProjectionBlocks
public import Mathlib.Data.Fintype.BigOperators

/-!
# Gotsman--Linial: BlockCoupling

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/BlockCoupling.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# The finite block coupling

Normalize a nonnegative matrix of block masses, identify its two binomial
marginals, and reflect its first index.  The low-degree block vanishing gives
the one-sided displacement bound required by the finite coupling lemma.
-/

open scoped BigOperators

namespace BooleanAnalysis.PolynomialThreshold.Internal

/-- Normalize finite two-index masses by their total mass. -/
noncomputable def normalizedPairWeight {α β : Type*}
    (B : α → β → ℝ) (Z : ℝ) (t : α × β) : ℝ :=
  B t.1 t.2 / Z

theorem normalizedPairWeight_nonneg {α β : Type*}
    (B : α → β → ℝ) (Z : ℝ) (hB : ∀ r s, 0 ≤ B r s) (hZ : 0 ≤ Z)
    (t : α × β) : 0 ≤ normalizedPairWeight B Z t :=
  div_nonneg (hB t.1 t.2) hZ

theorem normalizedPairWeight_row {α β : Type*} [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (r : α) :
    (∑ s : β, normalizedPairWeight B Z (r, s)) = (∑ s : β, B r s) / Z := by
  simp only [normalizedPairWeight, ← Finset.sum_div]

theorem normalizedPairWeight_column {α β : Type*} [Fintype α]
    (B : α → β → ℝ) (Z : ℝ) (s : β) :
    (∑ r : α, normalizedPairWeight B Z (r, s)) = (∑ r : α, B r s) / Z := by
  simp only [normalizedPairWeight, ← Finset.sum_div]

/-- First-coordinate expectations are computed from the row sums. -/
theorem normalizedPairWeight_expect_fst {α β : Type*} [Fintype α] [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (φ : α → ℝ) :
    (∑ t : α × β, normalizedPairWeight B Z t * φ t.1) =
      ∑ r : α, ((∑ s : β, B r s) / Z) * φ r := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp only [normalizedPairWeight]
  rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Second-coordinate expectations are computed from the column sums. -/
theorem normalizedPairWeight_expect_snd {α β : Type*} [Fintype α] [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (φ : β → ℝ) :
    (∑ t : α × β, normalizedPairWeight B Z t * φ t.2) =
      ∑ s : β, ((∑ r : α, B r s) / Z) * φ s := by
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro s _
  simp only [normalizedPairWeight]
  rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Finite masses with binomial row and column sums, supported above the
anti-diagonal `r+s=n-d`, have the required centered quadratic bound. -/
theorem binomial_block_coupling_bound
    (n d : ℕ) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  let w : Fin (n + 1) × Fin (n + 1) → ℝ :=
    normalizedPairWeight B ((2 : ℝ) ^ n)
  let U : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => (t.2.val : ℝ)
  let V : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun t => (n : ℝ) - (t.1.val : ℝ)
  have hU (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (U t)) =
        ∑ s : Fin (n + 1), binomialWeight n s * φ (s.val : ℝ) := by
    simpa only [w, U, hcol, binomialWeight] using
      normalizedPairWeight_expect_snd B ((2 : ℝ) ^ n)
        (fun s => φ (s.val : ℝ))
  have hV (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (V t)) =
        ∑ r : Fin (n + 1),
          binomialWeight n r * φ ((n : ℝ) - (r.val : ℝ)) := by
    simpa only [w, V, hrow, binomialWeight] using
      normalizedPairWeight_expect_fst B ((2 : ℝ) ^ n)
        (fun r => φ ((n : ℝ) - (r.val : ℝ)))
  have hw : ∀ t, 0 ≤ w t :=
    normalizedPairWeight_nonneg B _ hB (binomialDenominator_pos n).le
  have hprob : (∑ t, w t) = 1 := by
    have h := hU (fun _ => 1)
    simpa only [mul_one, sum_binomialWeight] using h
  have hsame : ∀ φ : ℝ → ℝ,
      (∑ t, w t * φ (U t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hU, hV, binomialWeight_reflect]
  have hvariance :
      (∑ t, w t * (U t - (n : ℝ) / 2) ^ 2) =
        (Real.sqrt (n : ℝ) / 2) ^ 2 := by
    rw [hU (fun z => (z - (n : ℝ) / 2) ^ 2)]
    rw [binomialWeight_variance, binomialSigma_sq]
  have hstep : ∀ t, w t ≠ 0 → V t - U t ≤ (d : ℝ) := by
    rintro ⟨r, s⟩ ht
    have hnonzero : B r s ≠ 0 := by
      intro hz
      exact ht (by simp only [w, normalizedPairWeight, hz, zero_div])
    have hnat : n - d ≤ r.val + s.val :=
      Nat.le_of_not_gt (fun hlt => hnonzero (hvanish r s hlt))
    have hnat' : n ≤ r.val + s.val + d := by omega
    have hreal : (n : ℝ) ≤ (r.val : ℝ) + (s.val : ℝ) + (d : ℝ) := by
      exact_mod_cast hnat'
    dsimp only [U, V]
    linarith
  have hbound := finite_one_sided_coupling_bound w U V
    ((n : ℝ) / 2) (Real.sqrt (n : ℝ) / 2) (d : ℝ)
    hw hprob hsame (binomialSigma_nonneg n) (Nat.cast_nonneg d) hvariance hstep
  calc
    _ = (2 : ℝ) ^ n * (∑ t, w t * (U t - V t) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [w, U, V, normalizedPairWeight]
      field_simp [binomialDenominator_ne_zero n]
      ring
    _ ≤ (2 : ℝ) ^ n * (8 * (d : ℝ) * (Real.sqrt (n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hbound (binomialDenominator_pos n).le
    _ = 4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by ring

/-- The actual finite probability weights supplied by the Hilbert--Schmidt
blocks of an operator in a binomial orthogonal grading. -/
noncomputable def blockCouplingWeight {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  normalizedPairWeight (fun r s => hsNormSq (P s * H * P r)) ((2 : ℝ) ^ n) t

theorem blockCouplingWeight_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : 0 ≤ blockCouplingWeight P H t :=
  normalizedPairWeight_nonneg _ _ (fun _ _ => hsNormSq_nonneg _)
    (binomialDenominator_pos n).le t

/-- The first block index has the binomial distribution. -/
theorem blockCouplingWeight_fst_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (r : Fin (n + 1)) :
    (∑ s : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n r := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_row, sum_hsNormSq_blocks_column hP H r hH, hmult]
  rfl

/-- The second block index has the same binomial distribution. -/
theorem blockCouplingWeight_snd_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (s : Fin (n + 1)) :
    (∑ r : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n s := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_column, sum_hsNormSq_blocks_row hP H s hH, hmult]
  rfl

/-- Unitarity and the grading multiplicities make the block weights a
probability distribution without any additional normalization assumption. -/
theorem sum_blockCouplingWeight {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ)) :
    (∑ t : Fin (n + 1) × Fin (n + 1), blockCouplingWeight P H t) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [blockCouplingWeight_fst_marginal hP H hH hmult]
  exact sum_binomialWeight n

/-- A nonzero block probability lies on or above the required anti-diagonal. -/
theorem blockCouplingWeight_support {n d : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0)
    (r s : Fin (n + 1)) (ht : blockCouplingWeight P H (r, s) ≠ 0) :
    n - d ≤ r.val + s.val := by
  apply Nat.le_of_not_gt
  intro hlt
  apply ht
  simp only [blockCouplingWeight, normalizedPairWeight, hvanish r s hlt,
    hsNormSq_zero, zero_div]

/-- The spectral block coupling bounds the actual centered grading
anticommutator.  Its hypotheses are the orthogonal grading, its binomial
multiplicities, unitarity, and the separately proved low-degree vanishing. -/
theorem hsNormSq_centeredGrading_anticommutator_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  rw [hsNormSq_centered_anticommutator hP H]
  apply binomial_block_coupling_bound n d (fun r s => hsNormSq (P s * H * P r))
  · intro r s
    exact hsNormSq_nonneg _
  · intro r
    rw [sum_hsNormSq_blocks_column hP H r hleft, hmult]
  · intro s
    rw [sum_hsNormSq_blocks_row hP H s hright, hmult]
  · intro r s hrs
    rw [hvanish r s hrs, hsNormSq_zero]

/-- Trace-multiplicity form, for direct use with finite-dimensional orthogonal
projections whose ranks have already been computed. -/
theorem hsNormSq_centeredGrading_anticommutator_le_of_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  apply hsNormSq_centeredGrading_anticommutator_le n d P hP H hleft hright _ hvanish
  intro k
  rw [hsNormSq_projection (P k) (hP.conjTranspose_eq k) (hP.idempotent k), htrace]

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
