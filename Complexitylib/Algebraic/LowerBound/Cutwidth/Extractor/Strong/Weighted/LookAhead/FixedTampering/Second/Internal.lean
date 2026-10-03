/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Mathlib.Tactic.Ring

/-!
# Second-output extraction after a left-only tampered seed

First reveal the leak. Its alphabet multiplies the total original left
envelope, while both right-source envelope totals and the average original
prefix discrepancy are preserved. The actual two-round theorem supplies
the second output with the full right state retained. Project to the right
observation, alternate back to the original right source, and append both
honest outputs using the retained left state and right input.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededExtractor_fixedTampering_second_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {R : Y → Mid → Out}
    {K L J : Nat} {ε η θ δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (refresh : WeightedStrongSeededExtractor R J θ) (refresh_error : 0 ≤ θ)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed) (μ ν ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (refresh_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (refresh_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (fixedTamperingSecondRefreshWeight w l r x q y y' leak initialSeed W QExt R)
      (uniformSecondWeight
        (fixedTamperingSecondRefreshWeight w l r x q y y' leak initialSeed W QExt R)) ≤
      θ + 2 * ε + η + δ +
        (K : ℝ) * Fintype.card Mid * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) * (∑ z, ν z) +
        (J : ℝ) * Fintype.card Q * Fintype.card Out * ∑ z, ξ z := by
  let w₁ := observedTranscriptWeight w l leak
  let l₁ := observedTranscriptKernel l leak
  let r₁ : Z × Mid → B → ℝ := fun zm => r zm.1
  let μ₁ : Z × Mid → ℝ := fun zm => μ zm.1
  let ν₁ := observedTranscriptWeight ν l leak
  let ξ₁ := observedTranscriptWeight ξ l leak
  have hw₁ : IsProbabilityWeight w₁ := observedTranscriptWeight_probability w l leak hw hl
  have hl₁ : ∀ zm, IsProbabilityWeight (l₁ zm) :=
    observedTranscriptKernel_probability l leak hl
  have hr₁ : ∀ zm, IsProbabilityWeight (r₁ zm) := fun zm => hr zm.1
  have hν₁ : ∀ zm, 0 ≤ ν₁ zm :=
    observedTranscriptWeight_nonnegative ν l leak right_nonnegative (fun z => (hl z).1)
  have hξ₁ : ∀ zm, 0 ≤ ξ₁ zm :=
    observedTranscriptWeight_nonnegative ξ l leak refresh_nonnegative (fun z => (hl z).1)
  have capμ : ∀ zm x₀, w₁ zm * mapWeight (x zm.1) (l₁ zm) x₀ ≤ μ₁ zm :=
    observedTranscript_left_envelope w l x leak μ hw.1 (fun z => (hl z).1) left_cap
  have capν : ∀ zm q₀, w₁ zm * mapWeight (q zm.1) (r₁ zm) q₀ ≤ ν₁ zm :=
    observedTranscript_right_envelope w r l q leak ν (fun z => (hl z).1) right_cap
  have capξ : ∀ zm y₀, w₁ zm * mapWeight (y zm.1) (r₁ zm) y₀ ≤ ξ₁ zm :=
    observedTranscript_right_envelope w r l y leak ξ (fun z => (hl z).1) refresh_cap
  have preserved : weightDist (retainedSeedWeight w₁ r₁
      (fun zm b => initialSeed (q zm.1 b)))
      (uniformSecondWeight (retainedSeedWeight w₁ r₁
        (fun zm b => initialSeed (q zm.1 b)))) ≤ δ := by
    rw [retainedSeedWeight_observe_left_dist w l r leak
      (fun z b => initialSeed (q z b)) hw.1 hl hr]
    exact seed
  have seed_bound := first.lookAhead_dist_le first_error second second_error w₁ l₁ r₁
    (fun zm => x zm.1) (fun zm => x zm.1) (fun zm => q zm.1) (fun zm => q zm.1)
    initialSeed μ₁ ν₁ hw₁ hl₁ hr₁ (fun zm => left_nonnegative zm.1) hν₁
    capμ capν preserved
  have seed_projected := weightDist_uniformSecond_map_first_le
    (lookAheadExtractionWeight w₁ l₁ r₁ (fun zm => x zm.1) (fun zm => x zm.1)
      (fun zm => q zm.1) (fun zm => q zm.1) initialSeed W QExt)
    (fun p : ((Z × Mid) × B) × (Mid × Mid) =>
      (p.1.1, fixedTamperingRightMessage q y' R p.1.1 p.1.2))
  rw [← fixedTamperingSecond_seed_eq_map w l r x q y' leak initialSeed W QExt R]
    at seed_projected
  have bound := refresh.alternating_dist_le refresh_error w₁ l₁ r₁
    (fixedTamperingRightMessage q y' R)
    (fun t a => (fixedTamperingSecondHonestMessage x initialSeed W QExt t a).2)
    (fun zm => y zm.1) ξ₁ hw₁ hl₁ hr₁ hξ₁ capξ (seed_projected.trans seed_bound)
  have projected := weightDist_uniformSecond_map_first_le
    (alternatingExtractionWeight w₁ l₁ r₁ (fixedTamperingRightMessage q y' R)
      (fun t a => (fixedTamperingSecondHonestMessage x initialSeed W QExt t a).2)
      (fun zm => y zm.1) R)
    (fun p : ((Z × Mid) × (Q × Out)) × A =>
      ((p.1, fixedTamperingSecondHonestMessage x initialSeed W QExt p.1 p.2), p.2))
  rw [← fixedTamperingSecondRefreshWeight_eq_alternating_map
    w l r x q y y' leak initialSeed W QExt R hl] at projected
  have result := projected.trans bound
  rw [show (∑ zm, μ₁ zm) = (Fintype.card Mid : ℝ) * ∑ z, μ z from
      observedTranscript_left_envelope_sum μ,
    show (∑ zm, ν₁ zm) = ∑ z, ν z from
      observedTranscript_right_envelope_sum ν l leak (fun z => (hl z).2),
    show (∑ zm, ξ₁ zm) = ∑ z, ξ z from
      observedTranscript_right_envelope_sum ξ l leak (fun z => (hl z).2)] at result
  simp only [Fintype.card_prod, Nat.cast_mul] at result ⊢
  convert result using 1
  ring

end Algebraic.Cutwidth.Extractor.Internal
