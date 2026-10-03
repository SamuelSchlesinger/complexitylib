/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs

/-!
# Refreshing against a fixed left-side tampered seed

The transcript records a left-only tampered seed, the original right input
to the initial-seed map, the tampered refresh, and the honest first output.
The original left and right states are retained in the factored law. The
refresh law additionally retains the full left state and outputs the actual
honest refresh, without replacing either source by fresh randomness.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B X Q Seed Mid Y Out : Type*}

/-- Original tag and left leak, then right input and tampered refresh, then honest first output. -/
abbrev FixedTamperingTranscript (Z Q Mid Out : Type*) :=
  ((Z × Mid) × (Q × Out)) × Mid

/-- Once the left leak is fixed, both the right input and tampered refresh are right messages. -/
def fixedTamperingRightMessage (q : Z → B → Q) (y' : Z → B → Y)
    (R : Y → Mid → Out) (zm : Z × Mid) (b : B) : Q × Out :=
  (q zm.1 b, R (y' zm.1 b) zm.2)

/-- Once the right input is fixed, the honest first output is a left message. -/
def fixedTamperingHonestMessage (x : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (t : (Z × Mid) × (Q × Out)) (a : A) : Mid :=
  W (x t.1.1 a) (initialSeed t.2.1)

/-- The actual transcript computed from the original pair of states. -/
def fixedTamperingTranscriptValue (x : Z → A → X) (q : Z → B → Q)
    (y' : Z → B → Y) (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out) (z : Z) (a : A) (b : B) :
    FixedTamperingTranscript Z Q Mid Out :=
  let t := ((z, leak z a), fixedTamperingRightMessage q y' R (z, leak z a) b)
  (t, fixedTamperingHonestMessage x initialSeed W t a)

/-- Exact transcript weights after the left, right, and final left observations. -/
noncomputable def fixedTamperingTranscriptWeight [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out) :
    FixedTamperingTranscript Z Q Mid Out → ℝ :=
  observedTranscriptWeight
    (observedTranscriptWeight (observedTranscriptWeight w l leak)
      (fun zm => r zm.1) (fixedTamperingRightMessage q y' R))
    (fun t => observedTranscriptKernel l leak t.1)
    (fixedTamperingHonestMessage x initialSeed W)

/-- The normalized original left-state kernel after all observations. -/
noncomputable def fixedTamperingLeft [Fintype A]
    (l : Z → A → ℝ) (x : Z → A → X) (leak : Z → A → Mid)
    (initialSeed : Q → Seed) (W : X → Seed → Mid) :
    FixedTamperingTranscript Z Q Mid Out → A → ℝ :=
  observedTranscriptKernel (fun t => observedTranscriptKernel l leak t.1)
    (fixedTamperingHonestMessage x initialSeed W)

/-- The normalized original right-state kernel after its observed input and tampered refresh. -/
noncomputable def fixedTamperingRight [Fintype B]
    (r : Z → B → ℝ) (q : Z → B → Q) (y' : Z → B → Y)
    (R : Y → Mid → Out) (t : FixedTamperingTranscript Z Q Mid Out) : B → ℝ :=
  observedTranscriptKernel (fun zm => r zm.1) (fixedTamperingRightMessage q y' R) t.1

/-- The actual honest refresh, retaining the full transcript and original left state. -/
noncomputable def fixedTamperingRefreshWeight [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out) :
    (FixedTamperingTranscript Z Q Mid Out × A) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((fixedTamperingTranscriptValue x q y' leak initialSeed W R p.1.1 p.2 p.1.2, p.2),
      R (y p.1.1 p.1.2) (W (x p.1.1 p.2) (initialSeed (q p.1.1 p.1.2)))))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
