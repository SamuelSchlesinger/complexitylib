/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs

/-!
# Actual first phase of the standard-to-affine conversion

Every execution reads a prefix of its right input, extracts from the same
masked left input, uses the actual advice correlation breaker, and extracts
again. `none` indexes the honest execution and `some i` indexes a tampering.
Prefixes use false completion, so the program is total without size guards.

The transcript first observes all seed prefixes and mask contributions on
the right, then all first extraction outputs on the left, then all advice
outputs on the right. Its factors use the existing normalized conditional
kernels, including null rows, and retain both original latent variables.

This is the three-stage first phase of Chattopadhyay--Liao, *Extractors for
Sum of Two Sources* (2021), Theorem 6.1, printed p.23, with this library's
actual matched extractors and advice construction:
<https://arxiv.org/abs/2110.12652>. These definitions impose no statistical
guarantee or validity condition on those component programs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- A family containing the honest word and all `t` tampered words. -/
abbrev AffinePhaseOneCopies (t width : Nat) := Option (Fin t) → Fin width → Bool

/-- The initial seed prefix, completed by false bits when necessary. -/
def affinePhaseOneFirstSeed (d L₀ : Nat) (y : Fin d → Bool) :
    Fin (matchedBlockSeedBits L₀) → Bool :=
  fun i => (List.ofFn y)[i.val]?.getD false

/-- The actual first linear extraction, with output depth sixty-four. -/
def affinePhaseOneFirstOutput (n d L₀ e₀ : Nat) (x : Fin n → Bool)
    (y : Fin d → Bool) : Fin (matchedBlockOutputBits 64 L₀) → Bool :=
  matchedBlockExtractor n 64 L₀ e₀ x (affinePhaseOneFirstSeed d L₀ y)

/-- The actual advice construction supplies the seed for the final extraction. -/
def affinePhaseOneSecondSeed (n d L₀ e₀ L₁ e₁ : Nat) (x : Fin n → Bool)
    (y : Fin d → Bool) (advice : List Bool) : Fin (matchedBlockSeedBits L₁) → Bool :=
  adviceCorrelationBreaker d (matchedBlockOutputBits 64 L₀) L₁ e₁ y
    (affinePhaseOneFirstOutput n d L₀ e₀ x y) advice

/-- The actual output of the three-stage first phase. -/
def affinePhaseOneOutput (n d h L₀ e₀ L₁ e₁ er : Nat) (x : Fin n → Bool)
    (y : Fin d → Bool) (advice : List Bool) : Fin (matchedBlockOutputBits h L₁) → Bool :=
  matchedBlockExtractor n h L₁ er x (affinePhaseOneSecondSeed n d L₀ e₀ L₁ e₁ x y advice)

/-- The first right message fixes all prefixes and first mask contributions. -/
abbrev AffinePhaseOneRightMessage (t L₀ : Nat) :=
  AffinePhaseOneCopies t (matchedBlockSeedBits L₀) ×
    AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)

/-- The original tag and the first right message. -/
abbrev AffinePhaseOneRightTranscript (Z : Type*) (t L₀ : Nat) :=
  Z × AffinePhaseOneRightMessage t L₀

/-- The right transcript followed by all actual first extraction outputs. -/
abbrev AffinePhaseOneLeftTranscript (Z : Type*) (t L₀ : Nat) :=
  AffinePhaseOneRightTranscript Z t L₀ ×
    AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)

/-- The complete first-phase transcript, ending with all advice outputs. -/
abbrev AffinePhaseOneTranscript (Z : Type*) (t L₀ L₁ : Nat) :=
  AffinePhaseOneLeftTranscript Z t L₀ × AffinePhaseOneCopies t (matchedBlockSeedBits L₁)

variable {Z A B : Type*}

/-- The first observation depends only on the original right state. -/
def affinePhaseOneRightMessage (n d t L₀ e₀ : Nat)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (z : Z) (b : B) : AffinePhaseOneRightMessage t L₀ :=
  (fun i => affinePhaseOneFirstSeed d L₀ (ys z b i),
    fun i => affinePhaseOneFirstOutput n d L₀ e₀ (mask z b) (ys z b i))

/-- Once the right message is fixed, every actual first output is left-only. -/
def affinePhaseOneFirstLeft (n t L₀ e₀ : Nat) (x : Z → A → Fin n → Bool)
    (z : AffinePhaseOneRightTranscript Z t L₀) (a : A) :
    AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀) :=
  fun i j => Bool.xor (matchedBlockExtractor n 64 L₀ e₀ (x z.1 a) (z.2.1 i) j)
    (z.2.2 i j)

/-- Once the first outputs are fixed, every actual advice output is right-only. -/
def affinePhaseOneSecondRight (d t L₀ L₁ e₁ : Nat)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (z : AffinePhaseOneLeftTranscript Z t L₀) (b : B) :
    AffinePhaseOneCopies t (matchedBlockSeedBits L₁) :=
  fun i => adviceCorrelationBreaker d (matchedBlockOutputBits 64 L₀) L₁ e₁
    (ys z.1.1 b i) (z.2 i) (advice i)

/-- The actual first right transcript retains the original tag. -/
def affinePhaseOneRightTranscript (n d t L₀ e₀ : Nat)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (p : Z × B) : AffinePhaseOneRightTranscript Z t L₀ :=
  (p.1, affinePhaseOneRightMessage n d t L₀ e₀ mask ys p.1 p.2)

/-- The actual first extraction outputs extend the first right transcript. -/
def affinePhaseOneLeftTranscript (n d t L₀ e₀ : Nat)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    AffinePhaseOneLeftTranscript Z t L₀ :=
  (affinePhaseOneRightTranscript n d t L₀ e₀ mask ys p.1,
    fun i => affinePhaseOneFirstOutput n d L₀ e₀
      (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j)) (ys p.1.1 p.1.2 i))

/-- The actual advice outputs complete the first-phase transcript. -/
def affinePhaseOneTranscript (n d t L₀ e₀ L₁ e₁ : Nat)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) : AffinePhaseOneTranscript Z t L₀ L₁ :=
  (affinePhaseOneLeftTranscript n d t L₀ e₀ x mask ys p,
    fun i => affinePhaseOneSecondSeed n d L₀ e₀ L₁ e₁
      (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j))
      (ys p.1.1 p.1.2 i) (advice i))

/-- The final extraction's original-left contribution after fixing the transcript. -/
def affinePhaseOneOutputLeft (n t h L₀ L₁ er : Nat) (x : Z → A → Fin n → Bool)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) (a : A) :
    AffinePhaseOneCopies t (matchedBlockOutputBits h L₁) :=
  fun i => matchedBlockExtractor n h L₁ er (x z.1.1.1 a) (z.2 i)

/-- The final extraction's original-right mask contribution after fixing the transcript. -/
def affinePhaseOneOutputRight (n t h L₀ L₁ er : Nat) (mask : Z → B → Fin n → Bool)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) (b : B) :
    AffinePhaseOneCopies t (matchedBlockOutputBits h L₁) :=
  fun i => matchedBlockExtractor n h L₁ er (mask z.1.1.1 b) (z.2 i)

/-- Transcript weight after the first right observation. -/
noncomputable def affinePhaseOneRightWeight (n d t L₀ e₀ : Nat) [Fintype B]
    (w : Z → ℝ) (r : Z → B → ℝ) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) : AffinePhaseOneRightTranscript Z t L₀ → ℝ :=
  observedTranscriptWeight w r (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)

/-- Original right states conditioned on their first observation. -/
noncomputable def affinePhaseOneRightKernel (n d t L₀ e₀ : Nat) [Fintype B]
    (r : Z → B → ℝ) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) :
    AffinePhaseOneRightTranscript Z t L₀ → B → ℝ :=
  observedTranscriptKernel r (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)

/-- Transcript weight after additionally observing all first extraction outputs. -/
noncomputable def affinePhaseOneLeftWeight (n d t L₀ e₀ : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) : AffinePhaseOneLeftTranscript Z t L₀ → ℝ :=
  observedTranscriptWeight (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys)
    (fun z => l z.1) (affinePhaseOneFirstLeft n t L₀ e₀ x)

/-- Original left states conditioned on the actual first extraction outputs. -/
noncomputable def affinePhaseOneLeftKernel (n t L₀ e₀ : Nat) [Fintype A]
    (l : Z → A → ℝ) (x : Z → A → Fin n → Bool) :
    AffinePhaseOneLeftTranscript Z t L₀ → A → ℝ :=
  observedTranscriptKernel (fun z => l z.1) (affinePhaseOneFirstLeft n t L₀ e₀ x)

/-- The complete transcript weight, conditioning only the original side variables. -/
noncomputable def affinePhaseOneTranscriptWeight (n d t L₀ e₀ L₁ e₁ : Nat)
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) :
    AffinePhaseOneTranscript Z t L₀ L₁ → ℝ :=
  observedTranscriptWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
    (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
    (affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice)

/-- The original left kernel after all three observations. -/
noncomputable def affinePhaseOneTranscriptLeft (n t L₀ e₀ L₁ : Nat) [Fintype A]
    (l : Z → A → ℝ) (x : Z → A → Fin n → Bool)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) : A → ℝ :=
  affinePhaseOneLeftKernel n t L₀ e₀ l x z.1

/-- The original right kernel after all three observations. -/
noncomputable def affinePhaseOneTranscriptRight (n d t L₀ e₀ L₁ e₁ : Nat) [Fintype B]
    (r : Z → B → ℝ) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) :
    AffinePhaseOneTranscript Z t L₀ L₁ → B → ℝ :=
  observedTranscriptKernel (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
    (affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice)

/-- A left-source envelope after the first right observation. -/
noncomputable def affinePhaseOneRightLeftEnvelope (n d t L₀ e₀ : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) : AffinePhaseOneRightTranscript Z t L₀ → ℝ :=
  observedTranscriptWeight μ r (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)

/-- A left-source envelope after the right and left observations. -/
noncomputable def affinePhaseOneLeftEnvelope (n d t L₀ e₀ : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (z : AffinePhaseOneLeftTranscript Z t L₀) : ℝ :=
  affinePhaseOneRightLeftEnvelope n d t L₀ e₀ μ r mask ys z.1

/-- A right-source envelope after the right and left observations. -/
noncomputable def affinePhaseOneRightEnvelope (n t L₀ e₀ : Nat) [Fintype A]
    (ξ : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → Fin n → Bool) :
    AffinePhaseOneLeftTranscript Z t L₀ → ℝ :=
  observedTranscriptWeight (fun z : AffinePhaseOneRightTranscript Z t L₀ => ξ z.1)
    (fun z => l z.1) (affinePhaseOneFirstLeft n t L₀ e₀ x)

/-- The final left-source envelope keeps the probabilities of both right observations. -/
noncomputable def affinePhaseOneTranscriptLeftEnvelope (n d t L₀ e₀ L₁ e₁ : Nat)
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) :
    AffinePhaseOneTranscript Z t L₀ L₁ → ℝ :=
  observedTranscriptWeight (affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys)
    (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
    (affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice)

/-- The final right-source envelope copies the previous envelope to every advice output. -/
noncomputable def affinePhaseOneTranscriptRightEnvelope (n t L₀ e₀ L₁ : Nat)
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → Fin n → Bool)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) : ℝ :=
  affinePhaseOneRightEnvelope n t L₀ e₀ ξ l x z.1

end Algebraic.Cutwidth.Extractor
