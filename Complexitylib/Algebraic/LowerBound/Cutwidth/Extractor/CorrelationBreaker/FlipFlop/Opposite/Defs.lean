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
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# The actual opposite-advice flip-flop law

The retained transcript records the old transcript, both initial right
states, the four first look-ahead outputs, both refreshed states, the four
second look-ahead outputs, and the tampered final output. The law also
retains the entire original left state. Every recorded value is computed
from the original factored source law by the actual matched extractors.

This is the opposite-advice step of Chattopadhyay--Goyal--Li, Algorithm 1
and Lemma 6.8, in *Non-Malleable Extractors and Codes, with their Many
Tampered Extensions*, Section 6.3: https://arxiv.org/pdf/1505.00107.
No repaired distribution or supplied independence invariant occurs in this
definition. The two honest advice-bit cases share exactly this transcript.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Both complete look-ahead histories followed by the tampered final refresh. -/
abbrev FlipFlopOppositeTranscript (Z : Type*) (L : Nat) :=
  LookAheadBaseTranscript
    (LookAheadBaseTranscript Z (Fin (matchedBlockOutputBits 64 L) → Bool)
      (Fin (matchedBlockSeedBits L) → Bool))
    (Fin (matchedBlockOutputBits 64 L) → Bool) (Fin (matchedBlockSeedBits L) → Bool) ×
    (Fin (matchedBlockOutputBits 64 L) → Bool)

/-- The full retained history of the actual honest and opposite-advice tampered executions. -/
def flipFlopOppositeTranscript (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b : Bool) (p : (Z × B) × A) : FlipFlopOppositeTranscript Z L :=
  let z := p.1.1
  let r := flipFlopLookAhead n L e (x z p.2) (q z p.1.2)
  let r' := flipFlopLookAhead n L e (x' z p.2) (q' z p.1.2)
  let qbar := matchedBlockExtractor m 64 L e (y z p.1.2) (if b then r.2 else r.1)
  let qbar' := matchedBlockExtractor m 64 L e (y' z p.1.2) (if b then r'.1 else r'.2)
  let second := flipFlopLookAhead n L e (x z p.2) qbar
  let second' := flipFlopLookAhead n L e (x' z p.2) qbar'
  (((((z, (q z p.1.2, q' z p.1.2)), (r, r')), (qbar, qbar')), (second, second')),
    flipFlopStep n m L e (x' z p.2) (y' z p.1.2) (q' z p.1.2) (!b))

/-- The original-law output, retaining the full history and the complete original left state. -/
noncomputable def flipFlopOppositeWeight (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool) :
    (FlipFlopOppositeTranscript Z L × A) × (Fin (matchedBlockOutputBits 64 L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((flipFlopOppositeTranscript n m L e x x' y y' q q' b p, p.2),
      flipFlopStep n m L e (x p.1.1 p.2) (y p.1.1 p.1.2) (q p.1.1 p.1.2) b))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
