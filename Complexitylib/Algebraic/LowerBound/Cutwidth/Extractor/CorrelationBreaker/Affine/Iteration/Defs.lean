/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope.Defs

/-!
# Actual states and transcripts of repeated affine rounds

Each state keeps the original left and right latent variables. A transition
only observes the actual round messages, conditions the corresponding
kernels, and computes the next row contributions. The original source maps
are lifted along the previous-transcript projection. No new randomness,
probability certificate, or extraction guarantee is part of a state.

The deterministic row iteration follows Chattopadhyay--Liao, *Extractors for
Sum of Two Sources*, Theorem 6.1, printed pp.23--25:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Iterate actual rounds, rereading the same original source words at every step. -/
def affineRoundsOutput (n d h L e : Nat) : Nat →
    (Fin n → Bool) → (Fin d → Bool) →
      (Fin (matchedBlockOutputBits h L) → Bool) →
      (Fin (matchedBlockOutputBits h L) → Bool)
  | 0, _, _, row => row
  | i + 1, x, y, row =>
      affineRoundOutput n d h L e x y (affineRoundsOutput n d h L e i x y row)

/-- Forget exactly the five observations added during one round. -/
def affineRoundOrigin {Z : Type*} {t L : Nat} (z : AffineRoundTranscript Z t L) : Z :=
  z.1.1.1.1.1

/-- The complete finite transcript after a specified number of actual rounds. -/
def AffineIterationTranscript (Z : Type u) (t L : Nat) : Nat → Type u
  | 0 => Z
  | i + 1 => AffineRoundTranscript (AffineIterationTranscript Z t L i) t L

/-- Finite initial transcripts remain finite under every finite number of observations. -/
instance {Z : Type*} [Fintype Z] (t L i : Nat) :
    Fintype (AffineIterationTranscript Z t L i) := by
  induction i with
  | zero => exact inferInstanceAs (Fintype Z)
  | succ i ih =>
      letI := ih
      exact inferInstanceAs
        (Fintype (AffineRoundTranscript (AffineIterationTranscript Z t L i) t L))

/-- Project the complete accumulated transcript to its original tag. -/
def AffineIterationTranscript.origin {Z : Type*} {t L : Nat} :
    (i : Nat) → AffineIterationTranscript Z t L i → Z
  | 0, z => z
  | i + 1, z => origin i (affineRoundOrigin z)

/-- Actual factors and side maps, with both original latent state spaces unchanged. -/
structure AffineIterationState (n d h t L : Nat) (Z A B : Type*) where
  /-- The current transcript's marginal weight. -/
  weight : Z → ℝ
  /-- The conditional weighting of the original left latent variable. -/
  left : Z → A → ℝ
  /-- The conditional weighting of the original right latent variable. -/
  right : Z → B → ℝ
  /-- The original left source word at the current transcript. -/
  source : Z → A → Fin n → Bool
  /-- The original right contribution to the masked left source word. -/
  mask : Z → B → Fin n → Bool
  /-- All original right words, with the honest copy indexed by `none`. -/
  rightWords : Z → B → AffinePhaseOneCopies t d
  /-- The current long rows' original-left contributions. -/
  leftRows : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)
  /-- The current long rows' original-right contributions. -/
  rightRows : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)

namespace AffineIterationState

variable {n d h t L : Nat} {Z A B : Type*}

/-- Execute one round's actual observations and next-row computations. -/
noncomputable def next [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat) :
    AffineIterationState n d h t L (AffineRoundTranscript Z t L) A B where
  weight := affineRoundTranscriptWeight d h t L e s.weight s.left s.right
    s.leftRows s.rightRows s.rightWords
  left := affineRoundTranscriptLeft h t L e s.left s.leftRows
  right := affineRoundTranscriptRight d h t L e s.right s.rightRows s.rightWords
  source z := s.source (affineRoundOrigin z)
  mask z := s.mask (affineRoundOrigin z)
  rightWords z := s.rightWords (affineRoundOrigin z)
  leftRows := affineRoundOutputLeft n h t L e s.source
  rightRows := affineRoundOutputRight n h t L e s.mask

/-- The actual evolving factor state after a fixed number of rounds. -/
noncomputable def iterate [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat) :
    (i : Nat) → AffineIterationState n d h t L (AffineIterationTranscript Z t L i) A B
  | 0 => s
  | i + 1 => (iterate s e i).next e

/-- The complete transcript computed from one fixed original pair of latent states. -/
noncomputable def transcript [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat) :
    (i : Nat) → (Z × B) × A → AffineIterationTranscript Z t L i
  | 0, p => p.1.1
  | i + 1, p =>
      let current := s.iterate e i
      affineRoundTranscript d h t L e current.leftRows current.rightRows current.rightWords
        ((transcript s e i p, p.1.2), p.2)

/-- Reindex the original law by its actual transcript without discarding either latent state. -/
noncomputable def lift [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (p : (Z × B) × A) :
    (AffineIterationTranscript Z t L i × B) × A :=
  ((s.transcript e i p, p.1.2), p.2)

/-- Evolve the original-left joint envelope by the actual message probabilities. -/
noncomputable def leftEnvelope [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat) (μ : Z → ℝ) :
    (i : Nat) → AffineIterationTranscript Z t L i → ℝ
  | 0 => μ
  | i + 1 =>
      let current := s.iterate e i
      affineRoundTranscriptLeftEnvelope d h t L e (leftEnvelope s e μ i)
        current.right current.rightRows current.rightWords

/-- Evolve the original-right joint envelope through the same actual observations. -/
noncomputable def rightEnvelope [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e : Nat) (ν : Z → ℝ) :
    (i : Nat) → AffineIterationTranscript Z t L i → ℝ
  | 0 => ν
  | i + 1 =>
      let current := s.iterate e i
      affineRoundTranscriptRightEnvelope h t L e (rightEnvelope s e ν i)
        current.left current.leftRows

end AffineIterationState

end Algebraic.Cutwidth.Extractor
