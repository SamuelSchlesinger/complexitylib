/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs

/-!
# A flip-flop half-step with a fixed tampered right input

One actual two-round look-ahead is followed by the selected refresh on each
side. Each selection bit chooses the second look-ahead output exactly when
it is true. The tampered right input is determined by the old transcript.
The output law retains both complete look-ahead pairs, both right inputs,
the selected tampered refresh, and the full original left state.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual half-step law, retaining its entire transcript and original left state. -/
noncomputable def flipFlopHalfWeight (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    ((LookAheadBaseTranscript Z (Fin (matchedBlockOutputBits 64 L) → Bool)
      (Fin (matchedBlockSeedBits L) → Bool) × (Fin (matchedBlockOutputBits 64 L) → Bool)) × A) ×
      (Fin (matchedBlockOutputBits 64 L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let honest := flipFlopLookAhead n L e (x p.1.1 p.2) (q p.1.1 p.1.2)
    let tampered := flipFlopLookAhead n L e (x' p.1.1 p.2) (q' p.1.1)
    let transcript := ((p.1.1, (q p.1.1 p.1.2, q' p.1.1)), (honest, tampered))
    (((transcript, matchedBlockExtractor m 64 L e (y' p.1.1 p.1.2)
      (if b' then tampered.2 else tampered.1)), p.2),
      matchedBlockExtractor m 64 L e (y p.1.1 p.1.2)
        (if b then honest.2 else honest.1)))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
