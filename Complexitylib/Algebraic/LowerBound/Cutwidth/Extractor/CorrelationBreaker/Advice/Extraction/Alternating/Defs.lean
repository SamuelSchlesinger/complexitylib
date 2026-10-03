/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs

/-!
# The actual advice-breaker call after a right-side observation

The original right side supplies both source words. A preceding right
message lets the original left side compute both seeds. The law retains
that message, the entire original left state, and the actual tampered
output. This is the source/seed reversal in the first phase of
Chattopadhyay--Liao Theorem 6.1, <https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Run both advice programs after a right observation, retaining the full original left state. -/
noncomputable def alternatingAdviceWeight (n m L e : Nat) {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s s' : Z × V → A → Fin m → Bool)
    (x x' : Z → B → Fin n → Bool) (advice advice' : List Bool) :
    (((Z × V) × A) × (Fin (matchedBlockSeedBits L) → Bool)) ×
      (Fin (matchedBlockSeedBits L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((((p.1.1, v p.1.1 p.1.2), p.2),
      adviceCorrelationBreaker n m L e (x' p.1.1 p.1.2)
        (s' (p.1.1, v p.1.1 p.1.2) p.2) advice'),
      adviceCorrelationBreaker n m L e (x p.1.1 p.1.2)
        (s (p.1.1, v p.1.1 p.1.2) p.2) advice)) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
