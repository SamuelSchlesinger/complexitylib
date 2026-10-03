/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs

/-!
# Actual refresh laws and their common look-ahead transcript

The transcript first records both right inputs and then the honest and
tampered two-round outputs. Both refresh seeds are explicit coordinates.
The first refresh uses the honest first output. The opposite-advice refresh
uses the honest second output and retains the tampered refresh seeded by
the tampered first output. Both calls read the original right source.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The old transcript, both right inputs, then the two outputs of each look-ahead. -/
abbrev LookAheadBaseTranscript (Z Q Mid : Type*) :=
  (Z × (Q × Q)) × ((Mid × Mid) × (Mid × Mid))

/-- Both honest and tampered look-ahead outputs, after fixing the right input pair. -/
def lookAheadBaseMessage {Z A X Q Seed Mid : Type*}
    (x x' : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (zq : Z × (Q × Q)) (a : A) : (Mid × Mid) × (Mid × Mid) :=
  let r₁ := W (x zq.1 a) (initialSeed zq.2.1)
  let r₁' := W (x' zq.1 a) (initialSeed zq.2.2)
  ((r₁, W (x zq.1 a) (QExt zq.2.1 r₁)),
    (r₁', W (x' zq.1 a) (QExt zq.2.2 r₁')))

/-- The actual common transcript distribution after the right and left observations. -/
noncomputable def lookAheadBaseWeight {Z A B X Q Seed Mid : Type*}
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) :
    LookAheadBaseTranscript Z Q Mid → ℝ :=
  observedTranscriptWeight (observedTranscriptWeight w r (fun z b => (q z b, q' z b)))
    (fun zq => l zq.1) (lookAheadBaseMessage x x' initialSeed W QExt)

/-- The left conditional kernel after recording all four look-ahead outputs. -/
noncomputable def lookAheadBaseLeft {Z A X Q Seed Mid : Type*} [Fintype A]
    (l : Z → A → ℝ) (x x' : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) :
    LookAheadBaseTranscript Z Q Mid → A → ℝ :=
  observedTranscriptKernel (fun zq : Z × (Q × Q) => l zq.1)
    (lookAheadBaseMessage x x' initialSeed W QExt)

/-- The right conditional kernel after recording both right inputs. -/
noncomputable def lookAheadBaseRight {Z B Q Mid : Type*} [Fintype B]
    (r : Z → B → ℝ) (q q' : Z → B → Q)
    (t : LookAheadBaseTranscript Z Q Mid) : B → ℝ :=
  observedTranscriptKernel r (fun z b => (q z b, q' z b)) t.1

/-- The original left envelope scaled by the right-pair message probability. -/
noncomputable def lookAheadBaseLeftEnvelope {Z B Q Mid : Type*} [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ) (q q' : Z → B → Q)
    (t : LookAheadBaseTranscript Z Q Mid) : ℝ :=
  observedTranscriptWeight μ r (fun z b => (q z b, q' z b)) t.1

/-- The original right envelope scaled by the four-output left message probability. -/
noncomputable def lookAheadBaseRightEnvelope {Z A X Q Seed Mid : Type*} [Fintype A]
    (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) :
    LookAheadBaseTranscript Z Q Mid → ℝ :=
  observedTranscriptWeight (fun zq : Z × (Q × Q) => ν zq.1) (fun zq => l zq.1)
    (lookAheadBaseMessage x x' initialSeed W QExt)

/-- Refresh with the honest first output, retaining the common transcript and full left state. -/
noncomputable def lookAheadFirstRefreshWeight {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) :
    (LookAheadBaseTranscript Z Q Mid × A) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let zq := (p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2))
    let messages := lookAheadBaseMessage x x' initialSeed W QExt zq p.2
    (((zq, messages), p.2), R (y p.1.1 p.1.2) messages.1.1)) (factoredWeight w l r)

/-- Refresh with the honest second output, retaining the tampered first-output refresh too. -/
noncomputable def lookAheadTamperedRefreshWeight {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y y' : Z → B → Y) (R : Y → Mid → Out) :
    ((LookAheadBaseTranscript Z Q Mid × Out) × A) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let zq := (p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2))
    let messages := lookAheadBaseMessage x x' initialSeed W QExt zq p.2
    ((((zq, messages), R (y' p.1.1 p.1.2) messages.2.1), p.2),
      R (y p.1.1 p.1.2) messages.1.2)) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
