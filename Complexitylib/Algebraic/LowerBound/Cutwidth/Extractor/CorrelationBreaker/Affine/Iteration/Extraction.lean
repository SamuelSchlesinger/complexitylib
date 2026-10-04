/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Internal.Induction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Internal.Rows

import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Internal.Actual

/-!
# Security of repeated actual affine rounds

The actual evolving states double their retained-subset capacity, with
closed discrepancy `2^i * ρ + 8 * (2^i - 1) * 2^-e`. Every intermediate
source bound follows from an original envelope and its exact message
accounting. No intermediate seed or repaired-source witness is supplied.

The state invariant also bounds the actual XOR outputs while retaining
the complete original right state. Appending that conditionally independent
state preserves the left-row error; known output masks add no error.

The selected theorem initializes from the actual first phase and supplies
all round budgets. Its conclusion concerns the complete named program on
the original affine input, retaining the original tag, full right latent
state, and any set of tampered outputs, including all tamperings. No
intermediate source or seed certificate occurs in its hypotheses. The
source reserve is conservative and is not asserted feasible for every
input size. This follows the finite construction in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

variable {n d h t L : Nat} {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

/-- Before any round, the discrepancy is the initial discrepancy. -/
theorem affineIterationError_zero (e : Nat) (ρ : ℝ) : affineIterationError e ρ 0 = ρ :=
  Internal.affineIterationError_zero e ρ

/-- One additional round doubles the previous error and adds its local loss. -/
theorem affineIterationError_succ (e i : Nat) (ρ : ℝ) :
    affineIterationError e ρ (i + 1) =
      2 * affineIterationError e ρ i + 8 * ((2 : ℝ) ^ e)⁻¹ :=
  Internal.affineIterationError_succ e i ρ

/-- Original envelopes and finite reserves propagate the invariant along every actual iterate. -/
theorem AffineIterationState.iterate_invariant {n d h t L : Nat}
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e rounds k : Nat)
    (kx ky : Nat → Nat) (μ ν : Z → ℝ) {ρ : ℝ}
    (size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L)
    (right_length : Nat.clog 2 (d + 1) ≤ L)
    (row_length : Nat.clog 2 (matchedBlockOutputBits h L + 1) ≤ L)
    (room : 64 ≤ L) (short_error : e + 24 + 2 ≤ L)
    (final_length : Nat.clog 2 (n + 1) ≤ L) (final_error : e + h + 2 ≤ L)
    (final_budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, s.weight z * mapWeight (s.source z) (s.left z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, s.weight z *
      mapWeight (fun b => s.rightWords z b none) (s.right z) y₀ ≤ ν z)
    (first : ∀ i < rounds,
      2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + e ≤ ky i)
    (merge : 2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits h L)
    (recover : ∀ i < rounds,
      2 ^ 62 * L + (t + 3 * (t + 1)) * matchedBlockSeedBits L + e ≤ ky i)
    (final : ∀ i < rounds, 2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L + e ≤ kx i)
    (left_mass : ∀ i < rounds,
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (2 * i) * (∑ z, μ z) ≤
        ((2 : ℝ) ^ kx i)⁻¹)
    (right_mass : ∀ i < rounds,
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (4 * i) * (∑ z, ν z) ≤
        ((2 : ℝ) ^ ky i)⁻¹)
    (old : AffineRowInvariant h t L s.weight s.left s.leftRows k ρ)
    (i : Nat) (executed : i ≤ rounds) :
    AffineRowInvariant h t L (s.iterate e i).weight (s.iterate e i).left
      (s.iterate e i).leftRows (2 ^ i * k) (affineIterationError e ρ i) :=
  Internal.affineIterationState_iterate_invariant s e rounds k kx ky μ ν
    size right_length row_length room short_error final_length final_error final_budget
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap
    first merge recover final left_mass right_mass old i executed

/-- Appending the complete conditionally independent right state preserves the left-row error. -/
theorem AffineIterationState.leftSubsetWeight_dist_eq
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t))
    (hw : ∀ z, 0 ≤ s.weight z) (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    weightDist (s.leftSubsetWeight S) (uniformSecondWeight (s.leftSubsetWeight S)) =
      weightDist (affineRoundLeftRowsWeight h t L s.weight s.left s.leftRows S)
        (uniformSecondWeight (affineRoundLeftRowsWeight h t L s.weight s.left s.leftRows S)) :=
  Internal.affineIterationState_leftSubsetWeight_dist_eq s S hw hr

/-- The known honest and tampered right masks do not increase the conditional-uniformity error. -/
theorem AffineIterationState.subsetWeight_dist_le_left
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t)) :
    weightDist (s.subsetWeight S) (uniformSecondWeight (s.subsetWeight S)) ≤
      weightDist (s.leftSubsetWeight S) (uniformSecondWeight (s.leftSubsetWeight S)) :=
  Internal.affineIterationState_subsetWeight_dist_le_left s S

/-- Normalized factors induce a normalized actual masked-output law. -/
theorem AffineIterationState.subsetWeight_probability
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t))
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    IsProbabilityWeight (s.subsetWeight S) :=
  Internal.affineIterationState_subsetWeight_probability s S hw hl hr

/-- An actual left-row invariant bounds masked outputs while retaining the complete right state. -/
theorem AffineIterationState.subsetWeight_dist_le
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t))
    {k : Nat} {ρ : ℝ} (hw : ∀ z, 0 ≤ s.weight z)
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (invariant : AffineRowInvariant h t L s.weight s.left s.leftRows k ρ)
    (size : S.card ≤ k) :
    weightDist (s.subsetWeight S) (uniformSecondWeight (s.subsetWeight S)) ≤ ρ :=
  Internal.affineIterationState_subsetWeight_dist_le s S hw hr invariant size

/-- The complete actual program induces a normalized original-input output law. -/
theorem affineCorrelationBreakerWeight_probability (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affineCorrelationBreakerWeight n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice S) :=
  Internal.affineCorrelationBreakerWeight_probability n d t h L₀ e₀ L₁ e₁ er rounds
    w l r x mask ys advice S hw hl hr

/-- The chosen complete affine program has the requested error against every tampering subset. -/
theorem affineCorrelationBreaker_parameters_dist_le (n t a target : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t
      (affinePhaseOneRightBits n t a (affineIterationTarget t target)))
    (advice : Option (Fin t) → List Bool) (S : Finset (Fin t)) (μ : Z → ℝ)
    (positive : 0 < t)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) =
      uniformWeight (Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool))
    (honest_length : (advice none).length = a)
    (tampered_length : ∀ i, (advice (some i)).length = a)
    (different : ∀ i, advice none ≠ advice (some i))
    (source : (∑ z, μ z) ≤ ((2 : ℝ) ^ affineIterationSourceEntropy n t a target)⁻¹) :
    let σ := affineIterationTarget t target
    let d := affinePhaseOneRightBits n t a σ
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a σ
    let L := affinePhaseOneScale n t a σ
    let e := affinePhaseOneLocalError σ
    let actual := affineCorrelationBreakerWeight n d t h L₀ e L (adviceErrorExponent a e) e
      (affineIterationRounds t) w l r x mask ys advice S
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affineCorrelationBreaker_parameters_dist_le n t a target
    w l r x mask ys advice S μ positive hw hl hr nonnegative cap uniform
    honest_length tampered_length different source

end Algebraic.Cutwidth.Extractor
