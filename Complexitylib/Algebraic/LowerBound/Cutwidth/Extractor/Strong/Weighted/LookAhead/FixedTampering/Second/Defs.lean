/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Defs

/-!
# A second-output refresh with an arbitrary left-only tampered seed

The actual transcript records the left-only leak, original right input,
tampered refresh, and both honest look-ahead outputs. The honest refresh
uses the second output and reads the original right source. The output law
also retains the entire original left state. Every value is computed from
the original factored source law, without independently resampling a source.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B X Q Seed Mid Y Out : Type*}

/-- Original tag and left leak, then right observation, then both honest look-ahead outputs. -/
abbrev FixedTamperingSecondTranscript (Z Q Mid Out : Type*) :=
  ((Z × Mid) × (Q × Out)) × (Mid × Mid)

/-- Both honest look-ahead outputs are left-only once the original right input is fixed. -/
def fixedTamperingSecondHonestMessage (x : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (t : (Z × Mid) × (Q × Out)) (a : A) : Mid × Mid :=
  let first := W (x t.1.1 a) (initialSeed t.2.1)
  (first, W (x t.1.1 a) (QExt t.2.1 first))

/-- The actual full transcript computed from the original left and right states. -/
def fixedTamperingSecondTranscriptValue (x : Z → A → X) (q : Z → B → Q)
    (y' : Z → B → Y) (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (R : Y → Mid → Out)
    (z : Z) (a : A) (b : B) : FixedTamperingSecondTranscript Z Q Mid Out :=
  let t := ((z, leak z a), fixedTamperingRightMessage q y' R (z, leak z a) b)
  (t, fixedTamperingSecondHonestMessage x initialSeed W QExt t a)

/-- The honest second-output refresh retaining the full transcript and original left state. -/
noncomputable def fixedTamperingSecondRefreshWeight
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (R : Y → Mid → Out) :
    (FixedTamperingSecondTranscript Z Q Mid Out × A) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let transcript := fixedTamperingSecondTranscriptValue x q y' leak initialSeed
      W QExt R p.1.1 p.2 p.1.2
    ((transcript, p.2), R (y p.1.1 p.1.2) transcript.2.2))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
