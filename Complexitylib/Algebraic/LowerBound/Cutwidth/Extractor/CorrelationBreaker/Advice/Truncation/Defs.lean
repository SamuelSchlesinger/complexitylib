/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Defs

/-!
# Total output truncation for the actual advice program

The requested output consists of its first coordinates, with false bits
beyond the actual output width. Both honest and tampered programs use this
same total map. The retained law keeps the original shared tag and entire
right state, together with the truncated tampered output.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Keep the first requested bits, completing positions beyond the input width by false. -/
def adviceOutputPrefix (out : Nat) {d : Nat} (bits : Fin d → Bool) : Fin out → Bool :=
  fun i => (List.ofFn bits)[i.val]?.getD false

/-- The actual advice correlation breaker at a requested total output width. -/
def adviceTruncatedCorrelationBreaker (n m L e out : Nat)
    (x : Fin n → Bool) (y : Fin m → Bool) (advice : List Bool) : Fin out → Bool :=
  adviceOutputPrefix out (adviceCorrelationBreaker n m L e x y advice)

/-- Both truncated programs, retaining the original right state and truncated tampered output. -/
noncomputable def adviceTruncatedCorrelationBreakerWeight (n m L e out : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) : ((Z × B) × (Fin out → Bool)) × (Fin out → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((p.1, adviceTruncatedCorrelationBreaker n m L e out
      (x' p.1.1 p.2) (y' p.1.1 p.1.2) advice'),
      adviceTruncatedCorrelationBreaker n m L e out
        (x p.1.1 p.2) (y p.1.1 p.1.2) advice)) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
