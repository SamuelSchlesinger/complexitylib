/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Defs
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Language
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs

/-!
# Balanced padding and the dual depth-three polarity

Use the existing balanced padding: XOR the original verdict with a fresh
first bit. The same three-layer wiring represents an AND-OR-AND circuit by
complementing every input literal and constant and exchanging AND with OR.
-/

@[expose] public section

namespace Complexity.DepthThreeLowerBound

/-- XOR the language on the tail with the first input bit, defaulting to false. -/
noncomputable def balancedLanguage (w : List Bool) : Bool :=
  Bool.xor (language w.tail) (w.headD false)

/-- The exactly balanced extension of the hard length-`n` function. -/
noncomputable def balancedFamily (n : ℕ) : Cube (Fin (n + 1)) → Bool :=
  Algebraic.Cutwidth.balancePad (fun x => language (List.ofFn x))

/-- Evaluate the same wiring as AND-OR-AND with every bottom input complemented. -/
noncomputable def Circuit3.dualEval {V : Type*} (C : Circuit3 V) (x : Cube V) : Bool := by
  classical
  exact decide (∀ j ∈ C.top, ∃ i ∈ C.middle j, ∀ l ∈ C.bottom i, l.eval x = false)

/-- The AND-OR-AND interpretation agrees with the specified Boolean function. -/
def Circuit3.ComputesDual {V : Type*} (C : Circuit3 V) (f : Cube V → Bool) : Prop :=
  ∀ x, C.dualEval x = f x

end Complexity.DepthThreeLowerBound
