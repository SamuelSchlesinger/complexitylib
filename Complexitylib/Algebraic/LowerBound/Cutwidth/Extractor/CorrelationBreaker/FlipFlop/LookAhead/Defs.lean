/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# The actual matched-width look-ahead output law

Push the conditionally factored source through the concrete three-call
look-ahead program. Retain the transcript, the entire right state, and both
honest and tampered first outputs together with the honest second output.
The two inputs on each side may be arbitrary functions of that side state.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual second output with the full right state and both first outputs retained. -/
noncomputable def flipFlopLookAheadWeight (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) :
    ((Z × B) × ((Fin (matchedBlockSeedBits L) → Bool) ×
      (Fin (matchedBlockSeedBits L) → Bool))) × (Fin (matchedBlockSeedBits L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let honest := flipFlopLookAhead n L e (x p.1.1 p.2) (q p.1.1 p.1.2)
    let tampered := flipFlopLookAhead n L e (x' p.1.1 p.2) (q' p.1.1 p.1.2)
    ((p.1, (honest.1, tampered.1)), honest.2)) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
