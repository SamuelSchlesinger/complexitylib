/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# The actual strong advice-correlation-breaker law

Run both concrete advice programs on the original factored sources. The
honest output is compared with uniform while retaining the original
transcript, the entire original right state, and the tampered output.
Thus this law retains both right inputs even when they are correlated.

The program is Chattopadhyay--Goyal--Li Algorithm 2 followed by the final
left-source extraction specified in `Advice.Defs`. The finite error budget
uses conservative amplification of the checked per-bit error; it does not
claim the sharper error parameters of the original construction.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Both actual advice programs, retaining the entire original right state and tampered output. -/
noncomputable def adviceCorrelationBreakerWeight (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) :
    ((Z × B) × (Fin (matchedBlockSeedBits L) → Bool)) ×
      (Fin (matchedBlockSeedBits L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((p.1, adviceCorrelationBreaker n m L e (x' p.1.1 p.2) (y' p.1.1 p.1.2) advice'),
      adviceCorrelationBreaker n m L e (x p.1.1 p.2) (y p.1.1 p.1.2) advice))
    (factoredWeight w l r)

/-- A finite error budget for advice length `a` and original left-envelope total `α`. -/
noncomputable def adviceCorrelationBreakerError (m L e a : Nat) (α : ℝ) : ℝ :=
  let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
  let J : ℝ := (2 : ℝ) ^ (2 ^ 142 * L)
  let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
  let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
  let ε := ((2 : ℝ) ^ e)⁻¹
  ε + (a : ℝ) * 4 ^ a *
    (12 * ε + 3 * K * D ^ 2 / C + 6 * K * D ^ (8 * a + 7) * α +
      3 * J * C ^ (5 * a + 5) * ((2 : ℝ) ^ m)⁻¹) + K * D ^ (8 * a + 1) * α

end Algebraic.Cutwidth.Extractor
