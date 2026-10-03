/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs

/-!
# Actual alternating extraction with selected tamperings

Every left seed and right source copy is read from the original factored
sample. The law retains all executed left seeds and the chosen tampered
outputs. It is the alternating step of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/pdf/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual right extraction retains all left seeds and selected tampered outputs. -/
noncomputable def alternatingCopiesWeight {Z A B X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (ss : Z → A → Option (Fin t) → Seed) (xs : Z → B → Option (Fin t) → X)
    (E : X → Seed → Out) (S : Finset (Fin t)) :
    ((Z × (Option (Fin t) → Seed)) × (S → Out)) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    (((p.1.1, ss p.1.1 p.2), fun j : S => E (xs p.1.1 p.1.2 (some j))
      (ss p.1.1 p.2 (some j))), E (xs p.1.1 p.1.2 none) (ss p.1.1 p.2 none)))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
