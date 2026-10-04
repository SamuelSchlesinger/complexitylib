/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Internal.Envelope
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Internal.Execution

/-!
# The actual first phase initializes the complete affine iteration

The initializer packages the checked first-phase observations, original
conditional sources, and output contributions. Its normalized factors,
source envelopes, and old-row law agree exactly with the first-phase APIs.
Following these with any finite number of rounds gives the actual complete
affine correlation-breaker map, on the same original source variables.

The final law retains the executed transcript, full original right state,
and every selected tampered output. These are exact algebraic identities
and envelope accounting for Chattopadhyay--Liao, *Extractors for Sum of Two
Sources*, Theorem 6.1: <https://arxiv.org/abs/2110.12652>. Extraction errors
and parameter reserves belong to the separate statistical iteration.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual first phase supplies normalized initial factors. -/
theorem affinePhaseOneIterationState_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    IsProbabilityWeight s.weight ∧ (∀ z, IsProbabilityWeight (s.left z)) ∧
      ∀ z, IsProbabilityWeight (s.right z) :=
  Internal.affinePhaseOneIterationState_probability
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice hw hl hr

/-- The initial factored law is the original law with its actual first-phase transcript. -/
theorem affinePhaseOneIterationState_factored (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    mapWeight (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice)
      (factoredWeight w l r) = factoredWeight s.weight s.left s.right :=
  Internal.affinePhaseOneIterationState_factored
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice hl hr

/-- The initial side contributions reconstruct each actual first-phase output. -/
theorem affinePhaseOneIterationState_rows_eq (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) (j : Option (Fin t)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let q := affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p
    (fun k => Bool.xor (s.leftRows q.1.1 q.2 j k) (s.rightRows q.1.1 q.1.2 j k)) =
      affinePhaseOneOutput n d h L₀ e₀ L₁ e₁ er
        (fun k => Bool.xor (x p.1.1 p.2 k) (mask p.1.1 p.1.2 k))
        (ys p.1.1 p.1.2 j) (advice j) :=
  Internal.affinePhaseOneIterationState_rows_eq
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice p j

/-- The initial old-left-row law is precisely the checked first-phase subset law. -/
theorem affinePhaseOneIterationState_leftRowsWeight_eq (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    affineRoundLeftRowsWeight h t L₁ s.weight s.left s.leftRows S =
      affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice S :=
  Internal.affinePhaseOneIterationState_leftRowsWeight_eq
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice S

/-- The original-left initializer envelope has its checked sign, cap, and exact total. -/
theorem affinePhaseOneIterationState_left_envelope (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let envelope := affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice
    (∀ z, 0 ≤ envelope z) ∧
      (∀ z x₀, s.weight z * mapWeight (s.source z) (s.left z) x₀ ≤ envelope z) ∧
      (∑ z, envelope z) =
        (Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) : ℝ) *
          ∑ z, μ z :=
  Internal.affinePhaseOneIterationState_left_envelope
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice μ hw hl hr nonnegative cap

/-- The original-right initializer envelope has its checked sign, cap, and exact total. -/
theorem affinePhaseOneIterationState_right_envelope (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (ν : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ ν z)
    (cap : ∀ z y₀, w z * mapWeight (fun b => ys z b none) (r z) y₀ ≤ ν z) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let envelope := affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ν l x
    (∀ z, 0 ≤ envelope z) ∧
      (∀ z y₀, s.weight z *
        mapWeight (fun b => s.rightWords z b none) (s.right z) y₀ ≤ envelope z) ∧
      (∑ z, envelope z) =
        (Fintype.card (AffinePhaseOneCopies t (matchedBlockSeedBits L₁)) : ℝ) *
          Fintype.card (AffinePhaseOneRightMessage t L₀) * ∑ z, ν z :=
  Internal.affinePhaseOneIterationState_right_envelope
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice ν hw hl hr nonnegative cap

/-- All initialized round factors are an exact image of the original source law. -/
theorem affinePhaseOneIterationState_iterate_factored (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    mapWeight (fun p => s.lift er rounds
      (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p))
      (factoredWeight w l r) =
      factoredWeight (s.iterate er rounds).weight
        (s.iterate er rounds).left (s.iterate er rounds).right :=
  Internal.affinePhaseOneIterationState_iterate_factored
    n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice hw hl hr

/-- The initialized iteration executes the complete actual affine algorithm pointwise. -/
theorem affinePhaseOneIterationState_iterate_rows_eq (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) (j : Option (Fin t)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let q := s.lift er rounds (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p)
    (fun k => Bool.xor
      ((s.iterate er rounds).leftRows q.1.1 q.2 j k)
      ((s.iterate er rounds).rightRows q.1.1 q.1.2 j k)) =
      affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds
        (fun k => Bool.xor (x p.1.1 p.2 k) (mask p.1.1 p.1.2 k))
        (ys p.1.1 p.1.2 j) (advice j) :=
  Internal.affinePhaseOneIterationState_iterate_rows_eq
    n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice p j

/-- The full retained-subset law is exactly the actual algorithm on the original inputs. -/
theorem affinePhaseOneIterationState_subsetWeight_eq (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    (s.iterate er rounds).subsetWeight S =
      mapWeight (fun p : (Z × B) × A =>
        let input := fun k => Bool.xor (x p.1.1 p.2 k) (mask p.1.1 p.1.2 k)
        let tag := s.transcript er rounds
          (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p)
        (((tag, p.1.2), fun j : S =>
          affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds input
            (ys p.1.1 p.1.2 (some j.val)) (advice (some j.val))),
          affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds input
            (ys p.1.1 p.1.2 none) (advice none)))
        (factoredWeight w l r) :=
  Internal.affinePhaseOneIterationState_subsetWeight_eq
    n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice S hw hl hr

end Algebraic.Cutwidth.Extractor
