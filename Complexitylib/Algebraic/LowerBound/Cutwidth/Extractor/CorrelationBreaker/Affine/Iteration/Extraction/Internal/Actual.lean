/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Internal.Rows
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Internal.Parameters

/-!
# Complete actual affine extraction from the original factors

The terminal factored state is the exact image of the original latent
variables. Its XOR rows are the named complete program. Forgetting only
the intermediate transcript yields the law retaining the original tag,
full right state, and every requested tampered program output.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineCorrelationBreakerWeight_eq_map (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    affineCorrelationBreakerWeight n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice S =
      mapWeight (fun p =>
        ((((AffineIterationTranscript.origin rounds p.1.1.1).1.1.1, p.1.1.2), p.1.2), p.2))
        ((s.iterate er rounds).subsetWeight S) := by
  dsimp only
  rw [affinePhaseOneIterationState_subsetWeight_eq
    n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice S hw hl hr, mapWeight_comp]
  unfold affineCorrelationBreakerWeight
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only
  rw [AffineIterationState.transcript_origin]
  rfl

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
  (factoredWeight_probability w l r hw hl hr).map _

theorem affineCorrelationBreakerWeight_dist_le_subset (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let actual := affineCorrelationBreakerWeight n d t h L₀ e₀ L₁ e₁ er rounds
      w l r x mask ys advice S
    weightDist actual (uniformSecondWeight actual) ≤
      weightDist ((s.iterate er rounds).subsetWeight S)
        (uniformSecondWeight ((s.iterate er rounds).subsetWeight S)) := by
  let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
  have projected := weightDist_uniformSecond_map_first_le ((s.iterate er rounds).subsetWeight S)
    (fun p => (((AffineIterationTranscript.origin rounds p.1.1).1.1.1, p.1.2), p.2))
  rw [← affineCorrelationBreakerWeight_eq_map
    n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice S hw hl hr] at projected
  exact projected

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
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ := by
  let σ := affineIterationTarget t target
  let d := affinePhaseOneRightBits n t a σ
  let h := growingMatchedBlockDepth t
  let L₀ := affinePhaseOneInitialScale n t a σ
  let L := affinePhaseOneScale n t a σ
  let e := affinePhaseOneLocalError σ
  let s := affinePhaseOneIterationState n d t h L₀ e L (adviceErrorExponent a e) e
    w l r x mask ys advice
  have initial := affinePhaseOneIterationState_probability n d t h L₀ e L
    (adviceErrorExponent a e) e w l r x mask ys advice hw hl hr
  have probability := s.iterate_probability e (affineIterationRounds t)
    initial.1 initial.2.1 initial.2.2
  have invariant := affinePhaseOneIterationState_parameters_invariant n t a target
    w l r x mask ys advice μ positive hw hl hr nonnegative cap uniform
    honest_length tampered_length different source
  have bound := affineIterationState_subsetWeight_dist_le
    (s.iterate e (affineIterationRounds t)) S probability.1.1 probability.2.2 invariant
    (by simpa only [Fintype.card_fin] using S.card_le_univ)
  exact (affineCorrelationBreakerWeight_dist_le_subset n d t h L₀ e L
    (adviceErrorExponent a e) e (affineIterationRounds t) w l r x mask ys advice S
    hw hl hr).trans bound

end Algebraic.Cutwidth.Extractor.Internal
