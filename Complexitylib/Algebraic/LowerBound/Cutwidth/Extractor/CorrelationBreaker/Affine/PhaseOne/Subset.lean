/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Internal.Projection

/-!
# Initial security for all left-row subsets of size at most one

The law is the old-left-row law at the complete actual first-phase
transcript. For any subset of one tampering, an exact projection drops
only the original right state and unwanted tampered outputs from the
checked pair law. Consequently the pairwise error is also the error for
every empty or singleton subset, without an additional statistical loss.

The security theorems assume a positive number of tamperings, so the empty
subset can use a genuine pair index. They consume only original source
and advice hypotheses; the selected-parameter theorem discharges every
numerical guard. This initializes the subset invariant in the first phase
of Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- The actual subset law is a projection of any pair whose index contains the subset. -/
theorem affinePhaseOneLeftRowsWeight_eq_map_pair (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (i : Fin t) (selected : S ⊆ {i})
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice S =
      mapWeight (fun p => ((p.1.1.1, fun _ : S => p.1.2), p.2))
        (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er
          w l r x mask ys advice i) :=
  Internal.affinePhaseOneLeftRowsWeight_eq_map_pair n d t h L₀ e₀ L₁ e₁ er
    w l r x mask ys advice S i selected hl hr

/-- Discarding the original right state and extra selected output cannot increase distance. -/
theorem affinePhaseOneLeftRowsWeight_dist_le_pair (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (i : Fin t) (selected : S ⊆ {i})
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er
      w l r x mask ys advice S)
      (uniformSecondWeight (affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er
        w l r x mask ys advice S)) ≤
      weightDist (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er
        w l r x mask ys advice i)
        (uniformSecondWeight (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er
          w l r x mask ys advice i)) :=
  Internal.affinePhaseOneLeftRowsWeight_dist_le_pair n d t h L₀ e₀ L₁ e₁ er
    w l r x mask ys advice S i selected hl hr

/-- Normalized original factors induce a normalized first-phase subset law. -/
theorem affinePhaseOneLeftRowsWeight_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice S) :=
  Internal.affinePhaseOneLeftRowsWeight_probability n d t h L₀ e₀ L₁ e₁ er
    w l r x mask ys advice S hw hl hr

/-- Original source assumptions initialize every empty or singleton left-row subset. -/
theorem affinePhaseOne_left_subset_dist_le (n d t h L₀ e₀ L₁ target er : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (μ : Z → ℝ) (positive : 0 < t) (small : S.card ≤ 1)
    (length : Nat.clog 2 (n + 1) ≤ L₀) (room : 64 ≤ L₀) (error : e₀ + 64 + 2 ≤ L₀)
    (size : matchedBlockSeedBits L₀ ≤ d)
    (guard : FlipFlopSizeGuard d (matchedBlockOutputBits 64 L₀) L₁
      (adviceErrorExponent (advice none).length target))
    (output_size : matchedBlockOutputBits 64 L₁ ≤ matchedBlockOutputBits 64 L₀)
    (final_length : Nat.clog 2 (n + 1) ≤ L₁)
    (final_error : er + h + 2 ≤ L₁)
    (final_budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) = uniformWeight (Fin d → Bool))
    (advice_length : ∀ i, (advice none).length = (advice (some i)).length)
    (different : ∀ i, advice none ≠ advice (some i))
    (source_budget : 2 ^ 150 * ((advice none).length + 1) * L₁ +
      (t + 1) * (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀) ≤ d)
    (seed_width : 2 ^ 150 * ((advice none).length + 1) * L₁ ≤ matchedBlockOutputBits 64 L₀) :
    let e₁ := adviceErrorExponent (advice none).length target
    let actual := affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er
      w l r x mask ys advice S
    weightDist actual (uniformSecondWeight actual) ≤
      affinePhaseOneError t h L₀ e₀ L₁ target er (∑ z, μ z) :=
  Internal.affinePhaseOne_left_subset_dist_le n d t h L₀ e₀ L₁ target er
    w l r x mask ys advice S μ positive small length room error size guard output_size
    final_length final_error final_budget hw hl hr nonnegative cap uniform
    advice_length different source_budget seed_width

/-- The finite chooser gives error `2^-target` for every initial subset of size at most one. -/
theorem affinePhaseOne_left_subset_parameters_dist_le (n t a target : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t (affinePhaseOneRightBits n t a target))
    (advice : Option (Fin t) → List Bool) (S : Finset (Fin t)) (μ : Z → ℝ)
    (positive : 0 < t) (small : S.card ≤ 1)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) =
      uniformWeight (Fin (affinePhaseOneRightBits n t a target) → Bool))
    (honest_length : (advice none).length = a)
    (tampered_length : ∀ i, (advice (some i)).length = a)
    (different : ∀ i, advice none ≠ advice (some i))
    (source : (∑ z, μ z) ≤ ((2 : ℝ) ^ (affinePhaseOneSourceEntropy n t a target))⁻¹) :
    let d := affinePhaseOneRightBits n t a target
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a target
    let L₁ := affinePhaseOneScale n t a target
    let e := affinePhaseOneLocalError target
    let actual := affinePhaseOneLeftRowsWeight n d t h L₀ e L₁ (adviceErrorExponent a e) e
      w l r x mask ys advice S
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affinePhaseOne_left_subset_parameters_dist_le n t a target
    w l r x mask ys advice S μ positive small hw hl hr nonnegative cap uniform
    honest_length tampered_length different source

end Algebraic.Cutwidth.Extractor
